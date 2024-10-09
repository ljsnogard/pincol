use core::{
    marker::PhantomPinned,
    pin::Pin,
    ptr::{self, NonNull},
    sync::atomic::AtomicUsize,
    task::Waker,
};

use atomex::{AtomicFlags, CmpxchResult, StrictOrderings, TrCmpxchOrderings};
use atomic_sync::{
    mutex::embedded::{MsbAsMutexSignal, SpinningMutexBorrowed},
    x_deps::atomex,
};

use super::slot_::{PinnedSlot, Cursor};

pub(super) type ListMutex<'a, T, O> =
    SpinningMutexBorrowed<'a,
        Pin<&'a mut PinnedList<T, O>>,
        AtomicUsize,
        MsbAsMutexSignal<usize>,
        O,
    >;

pub(super) type ListFlags<'a, O> = AtomicFlags<usize, &'a mut AtomicUsize, O>;

#[derive(Debug)]
pub struct PinnedList<T = Option<Waker>, O = StrictOrderings>
where
    T: ?Sized,
    O: TrCmpxchOrderings,
{
    _pin_: PhantomPinned,
    /// The last pushed `CtxSlot`
    head_: Option<NonNull<PinnedSlot<T, O>>>,
    /// The first pushed `CtxSlot`
    tail_: Option<NonNull<PinnedSlot<T, O>>>,
    /// The flag for mutex and list length
    flag_: AtomicUsize,
}

impl<T, O> PinnedList<T, O>
where
    T: ?Sized,
    O: TrCmpxchOrderings,
{
    /// Create an empty queue.
    pub const fn new() -> Self {
        PinnedList {
            _pin_: PhantomPinned,
            head_: Option::None,
            tail_: Option::None,
            flag_: AtomicUsize::new(0usize),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn len(&self) -> usize {
        let u = self.list_flags().value();
        Self::get_list_len_(u)
    }

    pub fn mutex(&self) -> ListMutex<'_, T, O> {
        unsafe {
            let this = self as *const Self as *mut Self;
            let cell = &mut (*this).flag_;
            let data = {
                let mut p = NonNull::new_unchecked(this);
                Pin::new_unchecked( p.as_mut())
            };
            ListMutex::new(data, cell)
        }
    }

    pub fn find(
        self: Pin<&mut Self>,
        slot: Pin<&mut PinnedSlot<T, O>>,
    ) -> Option<Cursor<'_, T, O>> {
        if slot.is_element_of(self.as_ref().get_ref()) {
            let p = unsafe {
                let ptr = slot.get_unchecked_mut();
                NonNull::new_unchecked(ptr)
            };
            Option::Some(Cursor::new(Option::Some(p)))
        } else {
            Option::None
        }
    }

    pub fn tail_mut(self: Pin<&mut Self>) -> Cursor<T, O> {
        Cursor::new(self.tail_)
    }

    pub fn head_mut(self: Pin<&mut Self>) -> Cursor<T, O> {
        Cursor::new(self.head_)
    }

    pub fn push_head(
        self: Pin<&mut Self>,
        slot: Pin<&mut PinnedSlot<T, O>>,
    ) -> Result<usize, usize> {
        unsafe { self.get_unchecked_mut().push_head_(slot) }
    }

    /// Insert the slot pointer into the list keeping the FIFO order, and
    /// return the length of the list after insertion.
    /// 
    /// This operation will return `Ok` when and only when the slot is not
    /// element of any lists.
    pub fn push_tail(
        self: Pin<&mut Self>,
        slot: Pin<&mut PinnedSlot<T, O>>,
    ) -> Result<usize, usize> {
        unsafe { self.get_unchecked_mut().push_tail_(slot) }
    }

    pub fn pop_head(
        self: Pin<&mut Self>,
    ) -> Option<Pin<&mut PinnedSlot<T, O>>> {
        unsafe { self.get_unchecked_mut().pop_head_() }
    }

    pub fn clear<F>(self: Pin<&mut Self>, iter: F) -> usize
    where
        F: FnMut(Pin<&mut PinnedSlot<T, O>>) -> bool,
    {
        unsafe { self.get_unchecked_mut().clear_(iter) }
    }

    /// Detach the slot pointed by `slot` and amend the linkings of the list.
    pub(super) fn try_detach(
        self: Pin<&mut Self>,
        slot: Pin<&mut PinnedSlot<T, O>>,
    ) -> Result<usize, usize> {
        unsafe { self.get_unchecked_mut().try_detach_(slot) }
    }

    pub(super) fn insert_prev(
        self: Pin<&mut Self>,
        hint: Pin<&mut PinnedSlot<T, O>>,
        slot: Pin<&mut PinnedSlot<T, O>>,
    ) -> Result<usize, usize> {
        unsafe { self.get_unchecked_mut().insert_prev_(hint, slot) }
    }

    pub(super) fn insert_next(
        self: Pin<&mut Self>,
        hint: Pin<&mut PinnedSlot<T, O>>,
        slot: Pin<&mut PinnedSlot<T, O>>,
    ) -> Result<usize, usize> {
        unsafe { self.get_unchecked_mut().insert_next_(hint, slot) }
    }
}

impl<T, O> PinnedList<T, O>
where
    T: ?Sized,
    O: TrCmpxchOrderings,
{
    fn push_head_(
        &mut self,
        slot: Pin<&mut PinnedSlot<T, O>>,
    ) -> Result<usize, usize> {
        if !slot.try_attach(self) {
            return Result::Err(self.len());
        }
        let mut new_head = unsafe {
            NonNull::new_unchecked(slot.get_unchecked_mut())
        };
        if let Option::Some(mut old_head) = self.head_ {
            let old_head_mut = unsafe { old_head.as_mut() };
            let x = old_head_mut.set_prev_(Option::Some(new_head));
            debug_assert!(x.is_none());

            let new_head_mut = unsafe { new_head.as_mut() };
            let x = new_head_mut.set_next_(Option::Some(old_head));
            debug_assert!(x.is_none());

            self.head_ = Option::Some(new_head);
        } else {
            let x = self.head_.replace(new_head);
            debug_assert!(x.is_none());
            let x = self.tail_.replace(new_head);
            debug_assert!(x.is_none());
        }
        let x = self.incr_len();
        debug_assert!(x.is_succ());
        let l = Self::get_list_len_(x.into_inner());
        Result::Ok(l + 1)
    }

    fn push_tail_(
        &mut self,
        slot: Pin<&mut PinnedSlot<T, O>>,
    ) -> Result<usize, usize> {
        if !slot.try_attach(self) {
            return Result::Err(self.len());
        }
        let mut new_tail = unsafe {
            NonNull::new_unchecked(slot.get_unchecked_mut())
        };
        if let Option::Some(mut old_tail) = self.tail_ {
            let old_tail_mut = unsafe { old_tail.as_mut() };
            let x = old_tail_mut.set_next_(Option::Some(new_tail));
            debug_assert!(x.is_none());

            let new_tail_mut = unsafe { new_tail.as_mut() };
            let x = new_tail_mut.set_prev_(Option::Some(old_tail));
            debug_assert!(x.is_none());

            self.tail_ = Option::Some(new_tail);
        } else {
            let x = self.tail_.replace(new_tail);
            debug_assert!(x.is_none());
            let x = self.head_.replace(new_tail);
            debug_assert!(x.is_none());
        }
        let x = self.incr_len();
        debug_assert!(x.is_succ());
        let l = Self::get_list_len_(x.into_inner());
        Result::Ok(l + 1)
    }

    fn pop_head_(&mut self) -> Option<Pin<&mut PinnedSlot<T, O>>> {
        let mut head = self.head_.take()?;
        let head_mut = unsafe { head.as_mut() };
        if let Option::Some(head_next) = head_mut.next_ptr() {
            self.head_ = Option::Some(head_next);
        } else {
            self.tail_ = Option::None;
        };
        let mut head_pin = unsafe { Pin::new_unchecked(head_mut) };
        if !head_pin.as_mut().try_detach_from(self) {
            unreachable!("[PinnedList::pop_head] unmatched list");
        };
        let x = self.decr_len();
        debug_assert!(x.is_succ());
        Option::Some(head_pin)
    }

    fn insert_prev_(
        &mut self,
        hint: Pin<&mut PinnedSlot<T, O>>,
        slot: Pin<&mut PinnedSlot<T, O>>,
    ) -> Result<usize, usize> {
        debug_assert!(hint.is_element_of(self));
        let slot_mut = unsafe {
            NonNull::new_unchecked(slot.get_unchecked_mut()).as_mut()
        };
        if !slot_mut.try_attach(self) {
            return Result::Err(self.len())
        };
        let hint_mut = unsafe {
            NonNull::new_unchecked(hint.get_unchecked_mut()).as_mut()
        };
        // hint slot has prev, so the hint slot is not the head of the list
        if let Option::Some(mut prev) = hint_mut.prev_ptr() {
            slot_mut.set_prev_(Option::Some(prev));
            let prev_mut = unsafe { prev.as_mut() };
            prev_mut.set_next_(Option::Some(unsafe {
                NonNull::new_unchecked(slot_mut)
            }));
        } else {
            self.head_ = Option::Some(unsafe {
                NonNull::new_unchecked(slot_mut)
            });
        }

        slot_mut.set_next_(Option::Some(unsafe {
            NonNull::new_unchecked(hint_mut)
        }));
        hint_mut.set_prev_(Option::Some(unsafe {
            NonNull::new_unchecked(slot_mut)
        }));
        let x = self.incr_len();
        debug_assert!(x.is_succ());
        let l = Self::get_list_len_(x.into_inner());
        Result::Ok(l + 1)
    }

    fn insert_next_(
        &mut self,
        hint: Pin<&mut PinnedSlot<T, O>>,
        slot: Pin<&mut PinnedSlot<T, O>>,
    ) -> Result<usize, usize> {
        debug_assert!(hint.is_element_of(self));
        let slot_mut = unsafe {
            NonNull::new_unchecked(slot.get_unchecked_mut()).as_mut()
        };
        if !slot_mut.try_attach(self) {
            return Result::Err(self.len())
        };
        let hint_mut = unsafe {
            NonNull::new_unchecked(hint.get_unchecked_mut()).as_mut()
        };
        // hint slot has next, so the hint slot is not the tail of the list
        if let Option::Some(mut next) = hint_mut.next_ptr() {
            slot_mut.set_next_(Option::Some(next));
            let next_mut = unsafe { next.as_mut() };
            next_mut.set_prev_(Option::Some(unsafe {
                NonNull::new_unchecked(slot_mut)
            }));
        } else {
            self.tail_ = Option::Some(unsafe {
                NonNull::new_unchecked(slot_mut)
            });
        }
        slot_mut.set_prev_(Option::Some(unsafe {
            NonNull::new_unchecked(hint_mut)
        }));
        hint_mut.set_next_(Option::Some(unsafe {
            NonNull::new_unchecked(slot_mut)
        }));
        let x = self.incr_len();
        debug_assert!(x.is_succ());
        let l = Self::get_list_len_(x.into_inner());
        Result::Ok(l + 1)
    }

    fn try_detach_(
        &mut self,
        mut slot: Pin<&mut PinnedSlot<T, O>>,
    ) -> Result<usize, usize> {
        let opt_prev = slot.prev_ptr();
        let opt_next = slot.next_ptr();
        if !slot.as_mut().try_detach_from(self) {
            return Result::Err(self.len())
        };
        if let Option::Some(mut prev) = opt_prev {
            let prev_mut = unsafe { prev.as_mut() };
            prev_mut.set_next_(opt_next);
            let Option::Some(tail) = self.tail_ else {
                unreachable!("[PinnedList::try_detach] empty tail");
            };
            let slot_ref = slot.as_ref().get_ref();
            let tail_ref = unsafe { tail.as_ref() };
            if ptr::eq(slot_ref, tail_ref) {
                let new_tail = unsafe { NonNull::new_unchecked(prev_mut) };
                self.tail_ = Option::Some(new_tail);
            }
        };
        if let Option::Some(mut next) = opt_next {
            let next_mut = unsafe { next.as_mut() };
            next_mut.set_prev_(opt_prev);
            let Option::Some(head) = self.head_ else {
                unreachable!("[PinnedList::try_detach] empty head");
            };
            let slot_ref = slot.as_ref().get_ref();
            let head_ref = unsafe { head.as_ref() };
            if ptr::eq(slot_ref, head_ref) {
                let new_head = unsafe { NonNull::new_unchecked(next_mut) };
                self.head_ = Option::Some(new_head);
            }
        };
        if opt_prev.is_none() && opt_next.is_none() {
            self.head_ = Option::None;
            self.tail_ = Option::None;
        }
        let x = self.decr_len();
        debug_assert!(x.is_succ());
        let l = Self::get_list_len_(x.into_inner());
        Result::Ok(l + 1)
    }

    fn clear_<F>(&mut self, mut iter: F) -> usize
    where
        F: FnMut(Pin<&mut PinnedSlot<T, O>>) -> bool,
    {
        let mut len = 0usize;
        loop {
            let Option::Some(head) = self.pop_head_() else {
                break len;
            };
            len += 1;
            if !iter(head) {
                break len;
            }
        }
    }
}

impl<T, O> PinnedList<T, O>
where
    T: ?Sized,
    O: TrCmpxchOrderings,
{
    #[inline(always)]
    #[allow(non_snake_case)]
    fn LEN_MASK() -> usize {
        MsbAsMutexSignal::<usize>::K_MSB_FLAG() - 1
    }

    fn get_list_len_(u: usize) -> usize {
        u & Self::LEN_MASK()
    }

    #[inline(always)]
    fn list_flags(&self) -> ListFlags<'_, O> {
        let this = self as *const Self as *mut Self;
        unsafe { ListFlags::new(&mut (*this).flag_) }
    }

    fn incr_len(&self) -> CmpxchResult<usize> {
        let expect = |u| Self::get_list_len_(u) < Self::LEN_MASK();
        let desire = |u| u + 1;
        self.list_flags().try_spin_compare_exchange_weak(expect, desire)
    }

    fn decr_len(&self) -> CmpxchResult<usize> {
        let expect = |u| Self::get_list_len_(u) > 0;
        let desire = |u| u - 1;
        self.list_flags().try_spin_compare_exchange_weak(expect, desire)
    }
}

impl<T, O> Default for PinnedList<T, O>
where
    T: ?Sized,
    O: Default + TrCmpxchOrderings,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<T, O> Drop for PinnedList<T, O>
where
    T: ?Sized,
    O: TrCmpxchOrderings,
{
    fn drop(&mut self) {
        let _ = self.clear_(|_| true);
    }
}

unsafe impl<T, O> Send for PinnedList<T, O>
where
    T: Send,
    O: TrCmpxchOrderings,
{}

unsafe impl<T, O> Sync for PinnedList<T, O>
where 
    T: Send + Sync,
    O: TrCmpxchOrderings,
{}

#[cfg(test)]
mod tests_ {
    use std::{
        borrow::Borrow,
        boxed::Box,
        future::Future,
        pin::{pin, Pin},
        sync::{atomic::*, Arc,},
        task::{Context, Poll, Waker},
        time::Duration,
        vec::Vec,
    };
    use pin_project::pin_project;
    use pin_utils::pin_mut;
    use atomic_sync::x_deps::abs_sync::x_deps::pin_utils;

    use super::*;

    #[test]
    fn push_tail_clear_smoke() {
        let _ = env_logger::builder().is_test(true).try_init();

        let q = PinnedList::<(), StrictOrderings>::new();
        let mutex = q.mutex();
        let mut l = 0usize;

        let mut s1 = Box::pin(PinnedSlot::new(()));
        let mut g = mutex.acquire().wait();
        let r = (*g).as_mut().push_tail(s1.as_mut());
        assert!(r.is_ok());
        assert!(s1.is_element_of(&q));
        l += 1;
        assert_eq!(r.ok().unwrap(), l);
        assert_eq!(q.len(), l);
        drop(g);

        let mut s2 = Box::pin(PinnedSlot::new(()));
        let mut g = mutex.acquire().wait();
        let r = (*g).as_mut().push_tail(s2.as_mut());
        assert!(r.is_ok());
        assert!(s2.is_element_of(&q));
        l += 1;
        assert_eq!(r.ok().unwrap(), l);
        assert_eq!(q.len(), l);
        drop(g);

        let mut s3 = Box::pin(PinnedSlot::new(()));
        let mut g = mutex.acquire().wait();
        let r = (*g).as_mut().push_tail(s3.as_mut());
        assert!(r.is_ok());
        assert!(s3.is_element_of(&q));
        l += 1;
        assert_eq!(r.ok().unwrap(), l);
        assert_eq!(q.len(), l);
        drop(g);

        drop(s2);

        let len = q.len();
        let mut i = 0usize;
        let mut g = mutex.acquire().wait();
        let l = (*g).as_mut().clear(|_| { i += 1; true });
        assert_eq!(l, len);
        assert_eq!(i, len);
    }

    #[test]
    fn insert_prev_smoke() {
        let _ = env_logger::builder().is_test(true).try_init();
        const LEN: usize = 3;

        let q = PinnedList::<(), StrictOrderings>::new();
        let mut a = Vec::with_capacity(LEN);
        pin_mut!(q);
        while q.len() < LEN {
            let mut s = Box::pin(PinnedSlot::new(()));
            let r = q.as_mut().push_tail(s.as_mut());
            assert!(r.is_ok());
            assert!(s.is_element_of(q.as_ref().get_ref()));
            a.push(s);
        }
        let mut cursor = q.as_mut().head_mut();
        while cursor.move_next() {}

        let mut slot = Box::pin(PinnedSlot::new(()));
        let r = cursor.insert_prev(slot.as_mut());
        assert!(r.is_ok());

        let mut i = 0;
        while q.len() > 0 {
            assert!(q.as_mut().pop_head().is_some());
            i += 1;
        }
        assert_eq!(i, LEN + 1);
    }

    #[tokio::test]
    async fn wake_queue_smoke() {
        let _ = env_logger::builder().is_test(true).try_init();

        #[pin_project]
        struct TestFut<D, Q>
        where
            D: Borrow<AtomicUsize>,
            Q: Borrow<PinnedList<Option<Waker>, StrictOrderings>>,
        {
            data_: D,
            queue_: Q,
            #[pin]slot_: PinnedSlot<Option<Waker>, StrictOrderings>,
        }
    
        impl<D, Q> TestFut<D, Q>
        where
            D: Borrow<AtomicUsize>,
            Q: Borrow<PinnedList<Option<Waker>, StrictOrderings>>,
        {
            pub fn new(data: D, queue: Q) -> Self {
                TestFut {
                    data_: data,
                    queue_: queue,
                    slot_: PinnedSlot::new(Option::None),
                }
            }
        }
    
        impl<D, Q> Future for TestFut<D, Q>
        where
            D: Borrow<AtomicUsize>,
            Q: Borrow<PinnedList<Option<Waker>, StrictOrderings>>,
        {
            type Output = ();
    
            fn poll(
                self: Pin<&mut Self>, 
                cx: &mut Context<'_>,
            ) -> Poll<Self::Output> {
                let mut this = self.project();
                let data = (*this.data_).borrow();
                let sign = data.load(Ordering::Relaxed);
                if sign != 0 {
                    log::trace!("[TestFut::poll] sign({sign})");
                    return Poll::Ready(());
                }
                let queue = (*this.queue_).borrow();
                let mut slot = this.slot_.as_mut();
                let opt = slot.as_mut().data_pinned().get_mut();
                if opt.is_none() {
                    *opt = Option::Some(cx.waker().clone());
                    let mutex = queue.mutex();
                    let mut queue_mut = mutex.acquire().wait();
                    let r = queue_mut.as_mut().push_tail(this.slot_.as_mut());
                    debug_assert!(r.is_ok());
                    log::trace!(
                        "[TestFut::poll] queue.push({:?})",
                        this.slot_.as_mut(),
                    );
                }
                Poll::Pending
            }
        }

        let (tx, rx) = tokio::sync::oneshot::channel::<()>();

        let d = Arc::new(AtomicUsize::new(0usize));
        let q = Arc::new(PinnedList::<Option<Waker>, StrictOrderings>::new());
        let f1 = tokio::task::spawn(TestFut::new(d.clone(), q.clone()));
        let f2 = tokio::task::spawn(TestFut::new(d.clone(), q.clone()));

        let f_wake = tokio::task::spawn(async move {
            fn iter(
                slot: Pin<&mut PinnedSlot<Option<Waker>, StrictOrderings>>,
            ) -> bool {
                let opt = slot.data_pinned().get_mut().take();
                if let Option::Some(waker) = opt {
                    waker.wake();
                };
                true
            }

            let x = rx.await;
            assert!(x.is_ok());
            let mutex = q.mutex();
            let mut g = mutex.acquire().wait();
            (*g).as_mut().clear(iter)
        });

        tokio::time::sleep(Duration::from_secs(2)).await;
        d.store(1, Ordering::SeqCst);
        assert!(tx.send(()).is_ok());
        let Result::Ok(l) = f_wake.await else {
            unreachable!()
        };
        assert_eq!(l, 2);
        // assert_eq!(c, 2);

        assert!(f1.await.is_ok());
        assert!(f2.await.is_ok());
    }
}
