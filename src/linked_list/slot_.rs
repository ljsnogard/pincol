use core::{
    fmt,
    marker::{PhantomData, PhantomPinned},
    pin::Pin,
    ptr::{self, NonNull},
    sync::atomic::AtomicPtr,
    task::Waker,
};

use atomex::{AtomexPtrOwned, StrictOrderings, TrCmpxchOrderings};
use atomic_sync::x_deps::atomex;

use super::list_::PinnedList;

pub(super) type AtomexListPtr<T, O> = AtomexPtrOwned<PinnedList<T, O>, O>;

#[repr(C)]
pub struct PinnedSlot<T = Option<Waker>, O = StrictOrderings>
where
    T: ?Sized,
    O: TrCmpxchOrderings,
{
    _pin_: PhantomPinned,
    prev_: Option<NonNull<Self>>,
    next_: Option<NonNull<Self>>,
    list_: AtomexListPtr<T, O>,
    data_: T,
}

impl<T, O> PinnedSlot<T, O>
where
    O: TrCmpxchOrderings,
{
    pub const fn new(data: T) -> Self {
        PinnedSlot {
            _pin_: PhantomPinned,
            prev_: Option::None,
            next_: Option::None,
            list_: AtomexListPtr::new(AtomicPtr::new(ptr::null_mut())),
            data_: data,
        }
    }
}

impl<T, O> PinnedSlot<T, O>
where
    T: ?Sized,
    O: TrCmpxchOrderings,
{
    pub fn is_detached(&self) -> bool {
        self.list_.pointer().is_null()
    }

    pub fn is_element_of(&self, list: &PinnedList<T, O>) -> bool {
        ptr::eq(self.list_.pointer(), list)
    }

    pub fn data(&self) -> &T {
        &self.data_
    }

    pub fn data_pinned(self: Pin<&mut Self>) -> Pin<&mut T> {
        unsafe {
            let pointer = &mut self.get_unchecked_mut().data_;
            Pin::new_unchecked(pointer)
        }
    }

    pub fn attached_list(&self) -> Option<&PinnedList<T, O>> {
        unsafe { self.list_.pointer().as_ref() }
    }

    pub(super) fn attached_pinned_list(
        self: Pin<&mut Self>,
    ) -> Option<Pin<&mut PinnedList<T, O>>> {
        unsafe {
            let pointer = self.list_.pointer().as_mut()?;
            Option::Some(Pin::new_unchecked(pointer))
        }
    }

    pub(super) fn prev_ptr(&self) -> Option<NonNull<Self>> {
        self.prev_
    }

    pub(super) fn next_ptr(&self) -> Option<NonNull<Self>> {
        self.next_
    }

    pub(super) fn set_prev_(
        &mut self,
        prev: Option<NonNull<Self>>,
    ) -> Option<NonNull<Self>> {
        let x = self.prev_.take();
        self.prev_ = prev;
        x
    }

    pub(super) fn set_next_(
        &mut self,
        next: Option<NonNull<Self>>,
    ) -> Option<NonNull<Self>> {
        let x = self.next_.take();
        self.next_ = next;
        x
    }

    pub(super) fn try_attach(&self, list: &PinnedList<T, O>) -> bool {
        let ptr = list as *const _ as *mut _;
        let Option::Some(init) = NonNull::new(ptr) else {
            return false;
        };
        self.list_.try_spin_init(init).is_ok()
    }

    pub(super) fn try_detach_from(
        self: Pin<&mut Self>,
        list: &PinnedList<T, O>,
    ) -> bool {
        unsafe { self.get_unchecked_mut().try_detach_from_(list) }
    }

    /// Tries to reset to list pointer, on successful, reset prev and next
    /// to null and return the pointer to the list previously linked; on failure
    /// exit without doing anything.
    fn try_detach_from_(&mut self, list: &PinnedList<T, O>) -> bool {
        let p = unsafe {
            NonNull::new_unchecked(list as *const _ as *mut _)
        };
        let r = self.list_.try_spin_compare_and_reset(p);
        if let Result::Err(x) = r {
            debug_assert_eq!(x, p.as_ptr(), "[PinnedSlot::try_detach_from]");
            return false;
        }
        self.prev_ = Option::None;
        self.next_ = Option::None;
        true
    }
}

impl<T, O> Drop for PinnedSlot<T, O>
where
    T: ?Sized,
    O: TrCmpxchOrderings,
{
    fn drop(&mut self) {
        let opt_q = unsafe { self.list_.pointer().as_ref() };
        let Option::Some(q) = opt_q else {
            return;
        };
        let mutex = q.mutex();
        let mut g = mutex.acquire().wait();
        let slot = unsafe { Pin::new_unchecked(self) };
        let r = (*g).as_mut().try_detach(slot);
        debug_assert!(r.is_ok(), "[PinnedSlot::drop]");
    }
}

impl<T, O> AsRef<T> for PinnedSlot<T, O>
where
    T: ?Sized,
    O: TrCmpxchOrderings,
{
    #[inline(always)]
    fn as_ref(&self) -> &T {
        self.data()
    }
}

impl<T, O> fmt::Debug for PinnedSlot<T, O>
where
    T: ?Sized,
    O: TrCmpxchOrderings,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[PinnedSlot({self:p}): ")?;
        if let Option::Some(prev) = &self.prev_ {
            write!(f, "prev({prev:p}), ")?;
        } else {
            write!(f, "prev(null), ")?;
        };
        if let Option::Some(next) = &self.next_ {
            write!(f, "next({next:p}), ")?;
        } else {
            write!(f, "next(null), ")?;
        };
        let data = &self.data_;
        write!(f, "data({data:p})]")
    }
}

impl<T, O> Default for PinnedSlot<T, O>
where
    T: Default,
    O: TrCmpxchOrderings,
{
    fn default() -> Self {
        Self::new(T::default())
    }
}

unsafe impl<T, O> Send for PinnedSlot<T, O>
where
    T: Send,
    O: TrCmpxchOrderings,
{}

unsafe impl<T, O> Sync for PinnedSlot<T, O>
where 
    T: Send + Sync,
    O: TrCmpxchOrderings,
{}

#[derive(Debug)]
pub struct Cursor<'a, T, O>(
    Option<NonNull<PinnedSlot<T, O>>>,
    PhantomData<&'a PinnedList<T, O>>)
where
    T: ?Sized,
    O: TrCmpxchOrderings;

impl<'a, T, O> Cursor<'a, T, O>
where
    T: ?Sized,
    O: TrCmpxchOrderings,
{
    #[inline(always)]
    pub(super) const fn new(node: Option<NonNull<PinnedSlot<T, O>>>) -> Self {
        Cursor(node, PhantomData)
    }

    #[inline(always)]
    pub fn into_pinned_slot(mut self) -> Option<Pin<&'a mut PinnedSlot<T, O>>> {
        self.0
            .take()
            .map(|mut p| unsafe { Pin::new_unchecked(p.as_mut()) })
    }

    #[inline(always)]
    pub fn pinned_slot(&self) -> Option<Pin<&PinnedSlot<T, O>>> {
        self.0
            .map(|p| unsafe { Pin::new_unchecked(p.as_ref()) })
        
    }

    #[inline(always)]
    pub fn pinned_slot_mut(&mut self) -> Option<Pin<&mut PinnedSlot<T, O>>> {
        self.0
            .map(|mut p| unsafe { Pin::new_unchecked(p.as_mut()) })
        
    }

    #[inline(always)]
    pub fn is_detached(&self) -> bool {
        self.0
            .map(|p| unsafe { p.as_ref().is_detached() })
            .unwrap_or(true)
    }

    #[inline(always)]
    pub fn is_element_of(&self, list: &PinnedList<T, O>) -> bool {
        self.0
            .map(|p| unsafe { p.as_ref().is_element_of(list) })
            .unwrap_or(false)
        
    }

    pub fn move_prev(&mut self) -> bool {
        let Option::Some(slot) = self.0 else {
            return false;
        };
        let slot = unsafe { slot.as_ref() };
        if let Option::Some(prev) = slot.prev_ptr() {
            self.0.replace(prev);
            true
        } else {
            false
        }
    }

    pub fn move_next(&mut self) -> bool {
        let Option::Some(slot) = self.0 else {
            return false;
        };
        let slot = unsafe { slot.as_ref() };
        if let Option::Some(next) = slot.next_ptr() {
            self.0.replace(next);
            true
        } else {
            false
        }
    }

    pub fn current_pinned(&mut self) -> Option<Pin<&mut T>> {
        let p = &mut self.0?;
        unsafe {
            let x = Pin::new_unchecked(p.as_mut());
            Option::Some(x.data_pinned())
        }
    }

    pub fn peek_prev_pinned(&mut self) -> Option<Pin<&mut T>> {
        let p = &self.0?;
        unsafe {
            let node = p.as_ref();
            let prev = Pin::new_unchecked(node.prev_ptr()?.as_mut());
            Option::Some(prev.data_pinned())
        }
    }

    pub fn peek_next_pinned(&mut self) -> Option<Pin<&mut T>> {
        let p = &self.0?;
        unsafe {
            let node = p.as_ref();
            let next = Pin::new_unchecked(node.next_ptr()?.as_mut());
            Option::Some(next.data_pinned())
        }
    }

    pub fn insert_prev(
        &mut self,
        slot: Pin<&mut PinnedSlot<T, O>>,
    ) -> Result<usize, usize> {
        let Option::Some(mut hint) = self.pinned_slot_mut() else {
            return Result::Err(0);
        };
        let opt_list = hint.as_mut().attached_pinned_list();
        let Option::Some(list) = opt_list else {
            return Result::Err(0);
        };
        let list = unsafe {
            let mut p = NonNull::new_unchecked(list.get_unchecked_mut());
            Pin::new_unchecked(p.as_mut())
        };
        list.insert_prev(hint, slot)
    }

    pub fn insert_next(
        &mut self,
        slot: Pin<&mut PinnedSlot<T, O>>,
    ) -> Result<usize, usize> {
        let Option::Some(mut hint) = self.pinned_slot_mut() else {
            return Result::Err(0);
        };
        let opt_list = hint.as_mut().attached_pinned_list();
        let Option::Some(list) = opt_list else {
            return Result::Err(0);
        };
        let list = unsafe {
            let mut p = NonNull::new_unchecked(list.get_unchecked_mut());
            Pin::new_unchecked(p.as_mut())
        };
        list.insert_next(hint, slot)
    }

    pub fn try_detach(&mut self) -> bool {
        let Option::Some(mut slot) = self.pinned_slot_mut() else {
            return false;
        };
        let opt_list = slot.as_mut().attached_pinned_list();
        let Option::Some(list) = opt_list else {
            return false;
        };
        let list = unsafe {
            let mut p = NonNull::new_unchecked(list.get_unchecked_mut());
            Pin::new_unchecked(p.as_mut())
        };
        list.try_detach(slot.as_mut()).is_ok()
    }
}

impl<'a, T, O> Cursor<'a, T, O>
where
    T: ?Sized + Unpin,
    O: TrCmpxchOrderings,
{
    #[inline(always)]
    pub fn current(&mut self) -> Option<&mut T> {
        unsafe {
            let x = Pin::new_unchecked(self.0?.as_mut());
            Option::Some(x.data_pinned().get_mut())
        }
    }

    #[inline(always)]
    pub fn peek_prev_mut(&mut self) -> Option<&mut T> {
        unsafe {
            let node = self.0?.as_ref();
            let prev = Pin::new_unchecked(node.prev_ptr()?.as_mut());
            Option::Some(prev.data_pinned().get_mut())
        }
    }

    pub fn peek_next_mut(&mut self) -> Option<&mut T> {
        unsafe {
            let node = self.0?.as_ref();
            let next = Pin::new_unchecked(node.next_ptr()?.as_mut());
            Option::Some(next.data_pinned().get_mut())
        }
    }
}

impl<'a, T, O> PartialEq for Cursor<'a, T, O>
where
    T: ?Sized,
    O: TrCmpxchOrderings,
{
    fn eq(&self, other: &Self) -> bool {
        let (a, b) = (&self.0, &other.0);
        match (a, b) {
            (Option::Some(a), Option::Some(b)) => ptr::eq(a.as_ptr(), b.as_ptr()),
            (Option::None, Option::None) => true,
            _ => false,
        }
    }
}
