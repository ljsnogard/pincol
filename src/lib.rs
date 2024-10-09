#![no_std]
#![feature(type_alias_impl_trait)]
#![feature(try_trait_v2)]

// We always pull in `std` during tests, because it's just easier
// to write tests when you can assume you're on a capable platform
#[cfg(test)]
extern crate std;

pub mod linked_list;

pub mod x_deps {
    pub use atomic_sync;
    pub use atomic_sync::x_deps::atomex;
    pub use atomic_sync::x_deps::abs_sync::x_deps::pin_utils;
}
