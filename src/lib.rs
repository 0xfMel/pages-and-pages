#![warn(missing_docs)]
#![warn(rustdoc::all)]
#![deny(absolute_paths_not_starting_with_crate)]
#![deny(keyword_idents)]
#![deny(macro_use_extern_crate)]
#![deny(missing_abi)]
#![deny(non_ascii_idents)]
#![deny(pointer_structural_match)]
#![deny(unsafe_op_in_unsafe_fn)]
#![warn(explicit_outlives_requirements)]
#![warn(invalid_reference_casting)]
#![warn(let_underscore_drop)]
#![warn(meta_variable_misuse)]
#![warn(missing_copy_implementations)]
#![warn(missing_debug_implementations)]
#![warn(noop_method_call)]
#![warn(single_use_lifetimes)]
#![warn(trivial_casts)]
#![warn(trivial_numeric_casts)]
#![warn(unused_crate_dependencies)]
#![warn(unused_import_braces)]
#![warn(unused_lifetimes)]
#![warn(unused_macro_rules)]
#![warn(unused_qualifications)]
#![warn(unused_tuple_struct_fields)]
#![warn(variant_size_differences)]
#![warn(unreachable_pub)]
// Clippy
#![warn(clippy::pedantic)]
#![warn(clippy::nursery)]
#![warn(clippy::cargo)]
// Restrictions
#![deny(clippy::clone_on_ref_ptr)]
#![deny(clippy::mod_module_files)]
#![deny(clippy::partial_pub_fields)]
#![deny(clippy::pattern_type_mismatch)]
#![deny(clippy::same_name_method)]
#![deny(clippy::tests_outside_test_module)]
#![warn(clippy::absolute_paths)]
#![warn(clippy::as_underscore)]
#![warn(clippy::assertions_on_result_states)]
#![warn(clippy::big_endian_bytes)]
#![warn(clippy::create_dir)]
#![warn(clippy::dbg_macro)]
#![warn(clippy::decimal_literal_representation)]
#![warn(clippy::default_numeric_fallback)]
#![warn(clippy::default_union_representation)]
#![warn(clippy::deref_by_slicing)]
#![warn(clippy::else_if_without_else)]
#![warn(clippy::empty_drop)]
#![warn(clippy::empty_structs_with_brackets)]
#![warn(clippy::error_impl_error)]
#![warn(clippy::exhaustive_enums)]
#![warn(clippy::exhaustive_structs)]
#![warn(clippy::exit)]
#![warn(clippy::filetype_is_file)]
#![warn(clippy::float_cmp_const)]
#![warn(clippy::fn_to_numeric_cast_any)]
#![warn(clippy::format_push_string)]
#![warn(clippy::get_unwrap)]
#![warn(clippy::host_endian_bytes)]
#![warn(clippy::if_then_some_else_none)]
#![warn(clippy::impl_trait_in_params)]
#![warn(clippy::integer_division)]
#![warn(clippy::large_include_file)]
#![warn(clippy::let_underscore_must_use)]
#![warn(clippy::let_underscore_untyped)]
#![warn(clippy::lossy_float_literal)]
#![warn(clippy::map_err_ignore)]
#![warn(clippy::mem_forget)]
#![warn(clippy::missing_assert_message)]
#![warn(clippy::missing_enforced_import_renames)]
#![warn(clippy::missing_trait_methods)]
#![warn(clippy::mixed_read_write_in_expression)]
#![warn(clippy::multiple_inherent_impl)]
#![warn(clippy::multiple_unsafe_ops_per_block)]
#![warn(clippy::mutex_atomic)]
#![warn(clippy::needless_raw_strings)]
#![warn(clippy::non_ascii_literal)]
#![warn(clippy::rc_mutex)]
#![warn(clippy::redundant_type_annotations)]
#![warn(clippy::rest_pat_in_fully_bound_structs)]
#![warn(clippy::unseparated_literal_suffix)]
#![warn(clippy::shadow_same)]
#![warn(clippy::str_to_string)]
#![warn(clippy::string_add)]
#![warn(clippy::string_lit_chars_any)]
#![warn(clippy::string_slice)]
#![warn(clippy::string_to_string)]
#![warn(clippy::suspicious_xor_used_as_pow)]
#![warn(clippy::try_err)]
#![warn(clippy::undocumented_unsafe_blocks)]
#![warn(clippy::unimplemented)]
#![warn(clippy::unnecessary_safety_comment)]
#![warn(clippy::unnecessary_safety_doc)]
#![warn(clippy::unnecessary_self_imports)]
#![warn(clippy::unneeded_field_pattern)]
#![warn(clippy::unwrap_used)]
#![warn(clippy::use_debug)]
#![warn(clippy::verbose_file_reads)]
#![warn(clippy::wildcard_enum_match_arm)]
#![allow(clippy::redundant_pub_crate)]
#![allow(clippy::module_name_repetitions)]

//! Allows control over a manually allocated region of page-aligned memory with support
//! for granular protection and locking of underlying pages

use std::{
    alloc::{self, Layout},
    any::Any,
    fmt::{self, Debug},
    io,
    ops::{Deref, DerefMut},
    ptr, slice,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    },
};

use error::{IntoPagesError, JoinError, JoinErrorKind};

/// Provides methods for pages, currently just [`page::size`]
pub mod page {
    pub use crate::mem::page_size as size;
}

mod mem;

/// Error types
pub mod error;

/// Represents an allocation of 1 or more pages of memory
pub struct Allocation {
    pages: usize,
    ptr: *mut u8,
    mutable: AtomicUsize,
    immutable: AtomicUsize,
    inaccessible: AtomicUsize,
}

impl Debug for Allocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Allocation")
            .field("pages", &self.pages)
            .finish_non_exhaustive()
    }
}

// SAFETY: essentially a Vec<u8> which is Send.  Additional features are handled in a
// thread-safe manner
unsafe impl Send for Allocation {}

// SAFETY: essentially a Vec<u8> which is Sync.  Additional features are handled in a
// thread-safe manner
unsafe impl Sync for Allocation {}

/// Represents the accessibility of a page or range of pages in memory.  Corresponds to the
/// page protection
#[allow(clippy::exhaustive_enums)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(i32)]
pub enum Accessibility {
    /// Page or pages are inaccessible to all reading or modification.  Corresponds to the page
    /// protection PROT_NONE
    Inaccessible = libc::PROT_NONE,

    /// Page or pages are immutable so can be read but not modified.  Corresponds to the page
    /// protection PROT_READ
    Immutable = libc::PROT_READ,

    /// Page or pages are mutable so can be read and modified.  Corresponds to the page protections
    /// PROT_READ and PROT_WRITE
    Mutable = libc::PROT_READ | libc::PROT_WRITE,
}

#[allow(clippy::exhaustive_enums)]
#[derive(Debug)]
/// Represents the type of pages object.  Contains either [`MutPages`], [`Pages`], or
/// [`InaccessiblePages`].  Corresponds to the [`Accessibility`] of the pages.
pub enum PagesType {
    /// This [`PagesType`] contains a [`MutPages`] object.
    Mutable(MutPages),

    /// This [`PagesType`] contains an immutable [`Pages`] object.
    Immutable(Pages),

    /// This [`PagesType`] contains an [`InaccessiblePages`] object.
    Inaccessible(InaccessiblePages),
}

/// Common trait of all types of pages
/// Note: This trait is sealed as assumptions are made about the implementors that allow properties
/// to be safe.  It would not make sense to create your own pages object which implements this
/// trait.
pub trait AnyPages: private::Sealed {
    /// Gets the start index of the page of the underlying allocation which this object references
    fn start(&self) -> usize;
    /// Gets the end index of the page of the underlying allocation which this object references
    fn end(&self) -> usize;
    /// Gets the [`Accessibility`] of this pages object
    fn accessibility(&self) -> Accessibility;
    /// Gets this pages object as a `&dyn Any` object for reference downcasting
    fn as_any(&self) -> &dyn Any;
    /// Gets this pages object as a `&mut dyn Any` object for reference downcasting
    fn as_any_mut(&mut self) -> &mut dyn Any;
    /// Gets this pages object as a [`PagesType`] enum to allow pattern matching and unwrapping on accessibility
    fn into_pages_type(self) -> PagesType;
    /// Gets an immutable reference to the underlying [`Allocation`]
    fn allocation(&self) -> &Allocation;

    /// Gets the number of pages this pages object references
    fn pages(&self) -> usize {
        self.end() - self.start()
    }

    /// Gets the number of bytes this pages object references.  This is implemented as [`AnyPages::pages`]
    /// multiplied by the page size
    fn len_bytes(&self) -> usize {
        self.pages() * mem::page_size()
    }

    /// Gets the underlying allocation as a [`PagesAllocation`] object.  This is for internal use only,
    /// [`PagesAllocation`] exposes no methods or fields
    #[doc(hidden)]
    fn allocation_(&self) -> private::PagesAllocation<'_>;
}

impl dyn AnyPages {
    /// Downcasts `&dyn AnyPages` into `&T: AnyPages`
    pub fn downcast_ref<T: AnyPages + 'static>(&self) -> Option<&T> {
        self.as_any().downcast_ref()
    }

    /// Downcasts `&mut dyn AnyPages` into `&mut T: AnyPages`
    pub fn downcast_mut<T: AnyPages + 'static>(&mut self) -> Option<&mut T> {
        self.as_any_mut().downcast_mut()
    }
}

/// Common trait for pages objects which can be read
pub trait SlicePages: private::Sealed {
    /// Gets a slice of the raw bytes of the pages represented by this pages object
    fn slice(&self) -> &[u8];
}

#[doc(hidden)]
mod private {
    use std::sync::Arc;

    use crate::Allocation;

    /// Seals a trait to prevent bugs and unsoundness from unexpected implementations of traits
    #[doc(hidden)]
    pub trait Sealed {}

    /// Gives internal access to the allocation represented by a pages object.  Exposes no methods
    /// or fields externally
    #[doc(hidden)]
    #[derive(Debug)]
    pub struct PagesAllocation<'a> {
        pub(crate) allocation: &'a Arc<Allocation>,
    }
}

impl Deref for PagesType {
    type Target = dyn AnyPages;

    fn deref(&self) -> &Self::Target {
        match *self {
            Self::Mutable(ref m) => m,
            Self::Immutable(ref i) => i,
            Self::Inaccessible(ref p) => p,
        }
    }
}

impl DerefMut for PagesType {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match *self {
            Self::Mutable(ref mut p) => p,
            Self::Immutable(ref mut p) => p,
            Self::Inaccessible(ref mut p) => p,
        }
    }
}

impl Allocation {
    /// Creates a new allocation with a certain number of pages, returning an error on allocation
    /// failure
    ///
    /// # Panics
    /// Panics when pages == 0
    ///
    /// # Errors
    /// When allocation fails, instead of handling allocation error in the usual way by aborting,
    /// it will return an [`io::Error`] containing the OS error
    pub fn try_new(pages: usize) -> io::Result<Self> {
        assert_ne!(pages, 0, "Allocation: cannot create allocation of 0 pages");
        let ptr = mem::alloc(pages * mem::page_size())?;

        Ok(Self {
            ptr,
            pages,
            mutable: AtomicUsize::new(0),
            immutable: AtomicUsize::new(0),
            inaccessible: AtomicUsize::new(0),
        })
    }

    /// Crates a new allocation with a certain number of pages
    ///
    /// # Panics
    /// Panics when pages == 0
    #[must_use = "Creating an allocation without using it has no effect other than expensively allocating unused memory"]
    pub fn new(pages: usize) -> Self {
        Self::try_new(pages).unwrap_or_else(|_| {
            #[allow(clippy::unwrap_used)]
            alloc::handle_alloc_error(Layout::from_size_align(pages * mem::page_size(), 1).unwrap())
        })
    }

    /// Frees allocation memory
    ///
    /// # Errors
    /// When freeing memory failed, instead of handling free error in the usual way by aborting,
    /// it will return an [`io::Error`] containing the OS error
    pub fn free(mut self) -> io::Result<()> {
        // SAFETY: Method takes ownership of Allocation so cannot be called twice, drop impl checks
        // that it hasn't already been run
        unsafe { self.free_() }
    }

    /// # Safety
    /// Must only be called once for an allocation
    unsafe fn free_(&mut self) -> io::Result<()> {
        // SAFETY: This function is only called once for an allocation as per function safety
        // comment, so the memory region is still allocated and must have been allocated from an
        // Allocation
        unsafe { mem::dealloc(self.ptr, self.pages * mem::page_size()) }?;
        self.ptr = ptr::null_mut();
        Ok(())
    }

    /// Gets the number of pages this allocation represents
    pub const fn pages(&self) -> usize {
        self.pages
    }
}

impl Drop for Allocation {
    fn drop(&mut self) {
        // SAFETY: If the free_ method has been called already then it will have set ptr to null,
        // so checking the ptr isn't null is a sufficient check to ensure this method isn't called
        // twice
        if !self.ptr.is_null() && unsafe { self.free_() }.is_err() {
            alloc::handle_alloc_error(
                #[allow(clippy::unwrap_used)]
                Layout::from_size_align(self.pages * mem::page_size(), 1).unwrap(),
            )
        }
    }
}

macro_rules! pages {
    (
        Self = $Self:ident,
        Accessibility = $Accessibility:ident,
        counter = $counter:ident,
        alloc_into_method = $alloc_into:ident,
        into_method = $into_method:ident,

        other1 = {
            Type = $Other1:ident,
            counter = $other_counter1:ident,
        },

        other2 = {
            Type = $Other2:ident,
            counter = $other_counter2:ident,
        },
    ) => {
        #[doc = concat!("Represents a page, or range of pages with `", stringify!($Accessibility), "` accessibility")]
        pub struct $Self {
            allocation: Arc<Allocation>,
            start: usize,
            end: usize,
        }

        impl $Self {
            #[doc = concat!("Splits this [`", stringify!($Self), "`] into two consecutive [`", stringify!($Self), "`] at a given index")]
            ///
            /// # Errors
            /// If the index would result in one half of the split having 0 size, this will return
            /// itself back out as an error
            pub fn split(self, index: usize) -> Result<(Self, Self), Self> {
                let size = self.end - self.start;
                if index == 0 || index >= size {
                    return Err(self);
                }

                self.allocation.$counter.fetch_add(1, Ordering::Release);

                let left = Self {
                    allocation: Arc::clone(&self.allocation),
                    start: self.start,
                    end: self.start + index,
                };

                let right = Self {
                    allocation: Arc::clone(&self.allocation),
                    start: self.start + index,
                    end: self.end,
                };

                Ok((left, right))
            }

            #[doc = concat!("Sets whether the pages represented by this [`", stringify!($Self), "`] is locked into memory or not.")]
            /// See [mlock(2)](https://man.archlinux.org/man/mlock.2.en)
            ///
            /// # Errors
            /// If the OS returns an error from the `mlock` or `munlock` syscall, it is returned as an
            /// [`io::Error`]
            pub fn set_locked(&mut self, locked: bool) -> io::Result<()> {
                if locked {
                    mem::mlock(self.ptr(), self.len_bytes())
                } else {
                    mem::munlock(self.ptr(), self.len_bytes())
                }
            }

            /// Joins two or more contiguous pages from the same allocation into a single object,
            /// updating the protection of the memory region in a single syscall if nessassary.
            ///
            /// # Errors
            /// See [`JoinErrorKind`] docs.  Will return a [`JoinError`] containing the input [`PagesType`]s and a [`JoinErrorKind`]
            /// containing what went wrong.
            pub fn join<const C: usize>(
                parts: [PagesType; C],
            ) -> Result<Self, JoinError<[PagesType; C]>> {
                let mut index = [0; C];
                for i in 1..C {
                    index[i] = i;
                }

                index.sort_unstable_by_key(|x| parts[*x].start());
                Self::join_(&parts, &index).map_err(|kind| JoinError { kind, parts })
            }

            /// Joins two or more contiguous pages from the same allocation into a single object,
            /// updating the protection of the memory region in a single syscall if nessassary.
            /// Accepts a Vec as an input rather than a const size array like [`Self::join`]
            ///
            /// # Errors
            /// See [`JoinErrorKind`] docs.  Will return a [`JoinError`] containing the input [`PagesType`]s and a [`JoinErrorKind`]
            /// containing what went wrong.
            pub fn join_vec(parts: Vec<PagesType>) -> Result<Self, JoinError<Vec<PagesType>>> {
                let mut index: Vec<_> = (0..parts.len()).collect();
                index.sort_unstable_by_key(|x| parts[*x].start());
                Self::join_(&parts, &index).map_err(|kind| JoinError { kind, parts })
            }

            fn join_(parts: &[PagesType], index: &[usize]) -> Result<Self, JoinErrorKind> {
                let mut index = index.iter().copied();
                let Some(first) = index.next() else {
                    return Err(JoinErrorKind::NonContiguous);
                };

                let mut mutable = 0_usize;
                let mut immutable = 0_usize;
                let mut inaccessible = 0_usize;

                let allocation = parts[first].allocation_().allocation;
                let start = parts[first].start();
                let mut end = parts[first].end();
                let first_accessibility = parts[first].accessibility();
                let mut common_prot = Some(first_accessibility);

                match first_accessibility {
                    Accessibility::Mutable => mutable += 1,
                    Accessibility::Immutable => immutable += 1,
                    Accessibility::Inaccessible => inaccessible += 1,
                }

                for i in index {
                    let part = &parts[i];
                    if end != part.start() {
                        return Err(JoinErrorKind::NonContiguous);
                    }

                    if !Arc::ptr_eq(allocation, part.allocation_().allocation) {
                        return Err(JoinErrorKind::NonContiguous);
                    }

                    if let Some(p) = common_prot {
                        if p != part.accessibility() {
                            common_prot = None;
                        }
                    }

                    match part.accessibility() {
                        Accessibility::Mutable => mutable += 1,
                        Accessibility::Immutable => immutable += 1,
                        Accessibility::Inaccessible => inaccessible += 1,
                    }

                    end = part.end();
                }

                let mut joined = Self {
                    allocation: Arc::clone(allocation),
                    start,
                    end,
                };
                let mut needs_protect = true;
                if let Some(p) = common_prot {
                    needs_protect = p != Accessibility::$Accessibility;
                }

                if needs_protect {
                    joined.protect().map_err(JoinErrorKind::IO)?;
                }

                let (this_count, this_counter) = match Accessibility::$Accessibility {
                    Accessibility::Mutable => (&mut mutable, &joined.allocation.mutable),
                    Accessibility::Immutable => (&mut immutable, &joined.allocation.immutable),
                    Accessibility::Inaccessible => {
                        (&mut inaccessible, &joined.allocation.inaccessible)
                    }
                };

                match this_count.checked_sub(1) {
                    None => {
                        this_counter.fetch_add(1, Ordering::Release);
                    }
                    Some(0) => {}
                    Some(i) => {
                        this_counter.fetch_sub(i, Ordering::Release);
                    }
                }

                *this_count = 0;

                if mutable != 0 {
                    joined
                        .allocation
                        .mutable
                        .fetch_sub(mutable, Ordering::Release);
                }

                if immutable != 0 {
                    joined
                        .allocation
                        .immutable
                        .fetch_sub(immutable, Ordering::Release);
                }

                if inaccessible != 0 {
                    joined
                        .allocation
                        .inaccessible
                        .fetch_sub(inaccessible, Ordering::Release);
                }

                Ok(joined)
            }

            fn protect(&mut self) -> io::Result<()> {
                // SAFETY: Sets the pages referenced by this object to its protection.  Safety is
                // ensured by the type system to avoid illegal access that violates the protection.
                // The region being protected is allocated through an Allocation object that must
                // still be alive.
                unsafe {
                    mem::mprotect(
                        self.ptr(),
                        self.len_bytes(),
                        Accessibility::$Accessibility as i32,
                    )
                }
            }

            fn ptr(&self) -> *mut u8 {
                // SAFETY: Adding to the ptr is safe as the start value is only modifyable by
                // spliting a Pages object which references only the region allocated.
                unsafe { self.allocation.ptr.add(self.start * mem::page_size()) }
            }

            #[doc = concat!("Converts this [`", stringify!($Self), "`] into an [`Allocation`].")]
            /// If the only reference that still exists to pages inside the allocation is through
            /// `self`, then this will succeed.
            /// Other references can be removed by dropping other pages objects or by joining them
            /// together through [`Self::join`] or [`Self::join_vec`].
            ///
            /// # Errors
            /// Will return [`Self`] as an error if other references to the allocation still exist.
            pub fn try_into_allocation(self) -> Result<Allocation, Self> {
                Allocation::try_from(self)
            }
        }

        impl Debug for $Self {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_struct(stringify!($Self))
                    .field("allocation", &self.allocation)
                    .field("start", &self.start)
                    .field("end", &self.end)
                    .finish()
            }
        }

        impl Allocation {
            #[doc = concat!("Converts this [`Allocation`] into [`", stringify!($Self), "`]")]
            ///
            /// # Errors
            /// Will error if protecting the pages fails, error object contains this [`Allocation`].
            pub fn $alloc_into(self) -> Result<$Self, IntoPagesError<Self>> {
                $Self::try_from(self)
            }
        }

        impl $Other1 {
            #[doc = concat!("Converts this [`", stringify!($Self), "`] into [`", stringify!($Other1), "`], updating the protection of the underlying pages")]
            ///
            /// # Errors
            /// Will error if protecting the pages fails, error object contains self.
            pub fn $into_method(self) -> Result<$Self, IntoPagesError<Self>> {
                $Self::try_from(self)
            }
        }

        impl $Other2 {
            #[doc = concat!("Converts this [`", stringify!($Self), "`] into [`", stringify!($Other2), "`], updating the protection of the underlying pages")]
            ///
            /// # Errors
            /// Will error if protecting the pages fails, error object contains self.
            pub fn $into_method(self) -> Result<$Self, IntoPagesError<Self>> {
                $Self::try_from(self)
            }
        }

        impl $crate::private::Sealed for $Self {}

        #[allow(clippy::missing_trait_methods)]
        impl AnyPages for $Self {
            fn start(&self) -> usize {
                self.start
            }

            fn end(&self) -> usize {
                self.end
            }

            fn accessibility(&self) -> Accessibility {
                Accessibility::$Accessibility
            }

            fn allocation(&self) -> &Allocation {
                &*self.allocation
            }

            fn allocation_(&self) -> $crate::private::PagesAllocation<'_> {
                $crate::private::PagesAllocation {
                    allocation: &self.allocation,
                }
            }

            fn as_any(&self) -> &dyn Any {
                self
            }

            fn as_any_mut(&mut self) -> &mut dyn Any {
                self
            }

            fn into_pages_type(self) -> PagesType {
                PagesType::from(self)
            }
        }

        impl From<$Self> for PagesType {
            fn from(value: $Self) -> PagesType {
                PagesType::$Accessibility(value)
            }
        }

        impl TryFrom<$Self> for Allocation {
            type Error = $Self;

            fn try_from(value: $Self) -> Result<Self, Self::Error> {
                let start = value.start;
                let end = value.end;
                Arc::try_unwrap(value.allocation).map_err(|value| $Self {
                    allocation: value,
                    start,
                    end,
                })
            }
        }

        impl TryFrom<Allocation> for $Self {
            type Error = IntoPagesError<Allocation>;

            fn try_from(value: Allocation) -> Result<Self, Self::Error> {
                let mut pages = $Self {
                    start: 0,
                    end: value.pages,
                    allocation: Arc::new(value),
                };

                let mut allocation = Arc::get_mut(&mut pages.allocation)
                    .expect("Arc has just been created, cannot have been cloned yet");

                if *allocation.$other_counter1.get_mut() != 0
                    || *allocation.$other_counter2.get_mut() != 0
                {
                    match pages.protect() {
                        Ok(()) => {}
                        Err(err) => {
                            let allocation = Arc::into_inner(pages.allocation)
                                .expect("Arc has just been created, cannot have been cloned yet");
                            return Err(IntoPagesError {
                                err,
                                from: allocation,
                            });
                        }
                    }

                    allocation = Arc::get_mut(&mut pages.allocation)
                        .expect("Arc has just been created, cannot have been cloned yet");
                    *allocation.$other_counter1.get_mut() = 0;
                    *allocation.$other_counter2.get_mut() = 0;
                }

                *allocation.$counter.get_mut() = 1;
                Ok(pages)
            }
        }

        try_from_pages_impl! {
            From = $Other1,
            To = $Self,
            from_counter = $other_counter1,
            to_counter = $counter,
        }

        try_from_pages_impl! {
            From = $Other2,
            To = $Self,
            from_counter = $other_counter2,
            to_counter = $counter,
        }
    };
}

macro_rules! try_from_pages_impl {
    (
        From = $From:ident,
        To = $To:ty,
        from_counter = $from_counter:ident,
        to_counter = $to_counter:ident,
    ) => {
        impl TryFrom<$From> for $To {
            type Error = IntoPagesError<$From>;

            fn try_from(value: $From) -> Result<Self, Self::Error> {
                let mut pages = Self {
                    start: value.start,
                    end: value.end,
                    allocation: value.allocation,
                };
                match pages.protect() {
                    Ok(()) => {}
                    Err(err) => {
                        return Err(IntoPagesError {
                            err,
                            from: $From {
                                start: pages.start,
                                end: pages.end,
                                allocation: pages.allocation,
                            },
                        });
                    }
                }
                pages
                    .allocation
                    .$from_counter
                    .fetch_sub(1, Ordering::Release);
                pages.allocation.$to_counter.fetch_add(1, Ordering::Release);
                Ok(pages)
            }
        }
    };
}

macro_rules! slice_pages_impl {
    ($Self:ty) => {
        impl SlicePages for $Self {
            fn slice(&self) -> &[u8] {
                // SAFETY:
                // - This trait is only implemented for pages objects which allow reading of
                // the memory region.
                // - The data region is ensured to be within the region allocated by Allocation
                // because the only way ptr and len_bytes can be modified is through splitting and
                // joining pages objects created from the underlying Allocation.
                // - All bytes are initialized to 0.
                // - The pages objects enforce borrowing rules so mutable references to the
                // underlying bytes cannot be acquired while the immutable reference exists.
                // - The memory region is returned from a successful allocation so the length
                // cannot overflow an isize.
                unsafe { slice::from_raw_parts(self.ptr(), self.len_bytes()) }
            }
        }
    };
}

impl MutPages {
    /// Gets a mutable slice of the raw bytes of the pages represented by this [`MutPages`] object
    pub fn slice_mut(&mut self) -> &mut [u8] {
        // SAFETY:
        // - This method is only implemented for MutPages which allows reading & writing of
        // the memory region.
        // - The data region is ensured to be within the region allocated by Allocation
        // because the only way ptr and len_bytes can be modified is through splitting and
        // joining pages objects created from the underlying Allocation.
        // - All bytes are initialized to 0.
        // - The pages objects enforce borrowing rules so immutable references, nor other mutable
        // references to the underlying bytes cannot be acquired while this mutable reference exists.
        // - The memory region is returned from a successful allocation so the length
        // cannot overflow an isize.
        unsafe { slice::from_raw_parts_mut(self.ptr(), self.len_bytes()) }
    }
}

pages! {
    Self = MutPages,
    Accessibility = Mutable,
    counter = mutable,
    alloc_into_method = try_into_pages_mut,
    into_method = try_into_mutable,

    other1 = {
        Type = Pages,
        counter = immutable,
    },

    other2 = {
        Type = InaccessiblePages,
        counter = inaccessible,
    },
}

pages! {
    Self = Pages,
    Accessibility = Immutable,
    counter = immutable,
    alloc_into_method = try_into_pages,
    into_method = try_into_immutable,

    other1 = {
        Type = MutPages,
        counter = mutable,
    },

    other2 = {
        Type = InaccessiblePages,
        counter = inaccessible,
    },
}

pages! {
    Self = InaccessiblePages,
    Accessibility = Inaccessible,
    counter = inaccessible,
    alloc_into_method = try_into_pages_inaccessible,
    into_method = try_into_inaccessible,

    other1 = {
        Type = Pages,
        counter = immutable,
    },

    other2 = {
        Type = MutPages,
        counter = mutable,
    },
}

slice_pages_impl!(MutPages);
slice_pages_impl!(Pages);

#[cfg(test)]
mod test {
    use std::sync::atomic::Ordering;

    use crate::{mem, Allocation, AnyPages, JoinError, JoinErrorKind, MutPages, Pages, SlicePages};

    fn test_new(pages: usize) -> Allocation {
        let alloc = Allocation::try_new(pages)
            .expect("allocation of {pages} pages should create successfully");
        let mut pages = alloc
            .try_into_pages_mut()
            .expect("should be able to create MutPages from new allocation");

        for b in pages.slice() {
            assert_eq!(*b, 0, "data is not zero-filled");
        }

        for b in pages.slice_mut() {
            *b = 1;
        }

        for b in pages.slice() {
            assert_eq!(*b, 1, "rw test failed");
        }

        pages
            .try_into_allocation()
            .expect("should be able to convert back to allocation")
    }

    fn check_counters(allocation: &Allocation, expected: [usize; 3]) {
        let mut actual = [0; 3];
        actual[0] = allocation.mutable.load(Ordering::Acquire);
        actual[1] = allocation.immutable.load(Ordering::Acquire);
        actual[2] = allocation.inaccessible.load(Ordering::Acquire);
        assert_eq!(actual, expected, "wrong counter values");
    }

    #[test]
    fn new_free() {
        let pages = test_new(1);
        pages.free().expect("should free allocation successfully");
    }

    #[test]
    fn multiple_pages() {
        test_new(5);
    }

    #[test]
    #[should_panic(expected = "Allocation: cannot create allocation of 0 pages")]
    fn new_empty() {
        test_new(0);
    }

    #[test]
    fn into_mutable() {
        let alloc = test_new(1);
        let pages = alloc
            .try_into_pages_mut()
            .expect("should be able to convert allocation into mutable pages");
        check_counters(&pages.allocation, [1, 0, 0]);
    }

    #[test]
    fn into_immutable() {
        let alloc = test_new(1);
        let pages = alloc
            .try_into_pages()
            .expect("should be able to convert allocation into immutable pages");
        check_counters(&pages.allocation, [0, 1, 0]);
    }

    #[test]
    fn into_inaccessible() {
        let alloc = test_new(1);
        let pages = alloc
            .try_into_pages_inaccessible()
            .expect("should be able to convert allocation into inaccessible pages");
        check_counters(&pages.allocation, [0, 0, 1]);
    }

    #[test]
    fn read_immutable() {
        let alloc = test_new(1);
        let pages = alloc
            .try_into_pages()
            .expect("should be able to convert allocation into immutable pages");
        for b in pages.slice() {
            assert_eq!(*b, 1);
        }
    }

    #[test]
    fn split() {
        let alloc = test_new(2);
        let pages = alloc
            .try_into_pages()
            .expect("should be able to convert allocation into immutable pages");
        let (left, right) = pages
            .split(1)
            .expect("splitting at index 1 with a size of 2 should be successful");
        assert_eq!(
            left.pages(),
            1,
            "left half of split has wrong number of pages"
        );
        assert_eq!(
            right.pages(),
            1,
            "right half of split has wrong number of pages"
        );

        check_counters(&right.allocation, [0, 2, 0]);
    }

    #[test]
    fn split_0() {
        let alloc = test_new(2);
        let pages = alloc
            .try_into_pages()
            .expect("should be able to convert allocation into immutable pages");
        let pages = pages
            .split(0)
            .expect_err("splitting at index 0 should fail");

        check_counters(&pages.allocation, [0, 1, 0]);
    }

    #[test]
    fn split_end() {
        let alloc = test_new(2);
        let pages = alloc
            .try_into_pages()
            .expect("should be able to convert allocation into immutable pages");
        let pages = pages
            .split(2)
            .expect_err("splitting at the pages' end should fail");

        check_counters(&pages.allocation, [0, 1, 0]);
    }

    #[test]
    fn join_fail() {
        let alloc = test_new(3);
        let pages = alloc
            .try_into_pages()
            .expect("should be able to convert allocation into immutable pages");
        let (left, right) = pages
            .split(1)
            .expect("splitting at index 1 with 3 pages should succeed");
        let (middle, right) = right
            .split(1)
            .expect("splitting at index 1 with 2 pages should succeed");
        assert_eq!(left.pages(), 1, "invalid number of pages for left");
        assert_eq!(middle.pages(), 1, "invalid number of pages for middle");
        assert_eq!(right.pages(), 1, "invalid number of pages for right");
        match Pages::join([left.into(), right.into()]) {
            Err(JoinError {
                kind: JoinErrorKind::NonContiguous,
                ..
            }) => {}
            Err(JoinError { kind, .. }) => panic!("join failed for the wrong reason: {kind:?}"),
            Ok(_) => panic!("join of non-contiguous pages should fail"),
        }
    }

    #[test]
    fn join() {
        let alloc = test_new(3);
        let pages = alloc
            .try_into_pages_inaccessible()
            .expect("should be able to convert allocation into inaccessible pages");
        let (left, right) = pages
            .split(1)
            .expect("splitting at index 1 with 3 pages should succeed");
        let (middle, right) = right
            .split(1)
            .expect("splitting at index 1 with 2 pages should succeed");
        assert_eq!(left.pages(), 1, "invalid number of pages for left");
        assert_eq!(middle.pages(), 1, "invalid number of pages for middle");
        assert_eq!(right.pages(), 1, "invalid number of pages for right");

        let mut pages = MutPages::join([middle.into(), right.into(), left.into()])
            .map_err(|e| e.kind)
            .expect("join of contiguous pages should succeed in any order");

        assert_eq!(pages.pages(), 3, "invalid number of pages for joined pages");

        check_counters(&pages.allocation, [1, 0, 0]);

        for x in pages.slice_mut() {
            *x = 2;
        }

        for x in pages.slice() {
            assert_eq!(*x, 2, "rw test failed");
        }
    }

    #[test]
    fn join_different_allocs() {
        let alloc1 = test_new(1);
        let pages1 = alloc1
            .try_into_pages()
            .expect("should be able to convert allocation into immutable pages");
        let alloc2 = test_new(1);
        let pages2 = alloc2
            .try_into_pages()
            .expect("should be able to convert allocation into immutable pages");

        match Pages::join([pages1.into(), pages2.into()]) {
            Err(JoinError {
                kind: JoinErrorKind::NonContiguous,
                ..
            }) => {}
            Err(JoinError { kind, .. }) => panic!("join failed for the wrong reason: {kind:?}"),
            Ok(_) => panic!("join of pages from different allocations should fail"),
        }
    }

    #[test]
    fn join_from_one_of_each_protection() {
        let alloc = test_new(3);
        let pages = alloc
            .try_into_pages_inaccessible()
            .expect("should be able to convert allocation into inaccessible pages");
        let (left, right) = pages
            .split(1)
            .expect("splitting at index 1 with 3 pages should succeed");
        let (middle, right) = right
            .split(1)
            .expect("splitting at index 1 with 2 pages should succeed");
        assert_eq!(left.pages(), 1, "invalid number of pages for left");
        assert_eq!(middle.pages(), 1, "invalid number of pages for middle");
        assert_eq!(right.pages(), 1, "invalid number of pages for right");

        let left = left
            .try_into_immutable()
            .expect("should be able to convert inaccessible pages into immutable pages");

        let middle = middle
            .try_into_mutable()
            .expect("should be able to convert inaccessible pages into mutable pages");

        let mut pages = MutPages::join([middle.into(), right.into(), left.into()])
            .map_err(|e| e.kind)
            .expect("join of contiguous pages should succeed in any order");

        assert_eq!(pages.pages(), 3, "invalid number of pages for joined pages");

        check_counters(&pages.allocation, [1, 0, 0]);

        for x in pages.slice_mut() {
            *x = 2;
        }

        for x in pages.slice() {
            assert_eq!(*x, 2, "rw test failed");
        }
    }

    #[test]
    fn pages_into_mutable() {
        let alloc = test_new(1);
        let pages = alloc
            .try_into_pages_inaccessible()
            .expect("should be able to convert allocation into inaccessible pages");

        check_counters(&pages.allocation, [0, 0, 1]);

        let pages = pages
            .try_into_mutable()
            .expect("should be able to convert inaccessible pages into mutable pages");

        check_counters(&pages.allocation, [1, 0, 0]);
    }

    #[test]
    fn pages_into_immutable() {
        let alloc = test_new(1);
        let pages = alloc
            .try_into_pages_mut()
            .expect("should be able to convert allocation into mutable pages");

        check_counters(&pages.allocation, [1, 0, 0]);

        let pages = pages
            .try_into_immutable()
            .expect("should be able to convert mutable pages into immutable pages");

        check_counters(&pages.allocation, [0, 1, 0]);
    }

    #[test]
    fn pages_into_inaccessible() {
        let alloc = test_new(1);
        let pages = alloc
            .try_into_pages()
            .expect("should be able to convert allocation into immutable pages");

        check_counters(&pages.allocation, [0, 1, 0]);

        let pages = pages
            .try_into_inaccessible()
            .expect("should be able to convert immutable pages into inaccessible pages");

        check_counters(&pages.allocation, [0, 0, 1]);
    }

    #[test]
    fn into_allocation_fail() {
        let alloc = test_new(2);
        let pages = alloc
            .try_into_pages()
            .expect("should be able to convert allocation into immutable pages");
        let (left, right) = pages
            .split(1)
            .expect("splitting at index 1 with a size of 2 should be successful");
        let _left = left
            .try_into_allocation()
            .expect_err("trying to convert split pages into an allocation when other pages are alive should fail");
        right
            .try_into_allocation()
            .expect_err("trying to convert split pages into an allocation when other pages are alive should fail");
    }

    #[test]
    fn into_allocation_dropped_page() {
        let alloc = test_new(2);
        let pages = alloc
            .try_into_pages()
            .expect("should be able to convert allocation into immutable pages");
        let (left, right) = pages
            .split(1)
            .expect("splitting at index 1 with a size of 2 should be successful");
        drop(right);
        left.try_into_allocation()
            .expect("trying to convert split pages into an allocation when all other pages are dropped should succeed");
    }

    #[test]
    fn lock_unlock() {
        let alloc = test_new(1);
        let mut pages = alloc
            .try_into_pages()
            .expect("should be able to convert allocation into immutable pages");
        pages
            .set_locked(true)
            .expect("should be able to lock pages");
        pages
            .set_locked(false)
            .expect("should be able to unlock pages");
    }

    #[allow(clippy::cast_possible_truncation, clippy::integer_division)]
    #[test]
    fn full() {
        let alloc = test_new(3);
        let pages = alloc
            .try_into_pages_mut()
            .expect("should be able to convert allocation into mutable pages");
        let (mut left, right) = pages
            .split(1)
            .expect("should be able to split 3 mutable pages with an index of 1");
        let (mut middle, mut right) = right
            .split(1)
            .expect("should be able to split 2 mutable pages with an index of 1");

        check_counters(&left.allocation, [3, 0, 0]);

        for b in left.slice_mut() {
            *b = 10;
        }

        for b in middle.slice_mut() {
            *b = 11;
        }

        for b in right.slice_mut() {
            *b = 12;
        }

        let pages = Pages::join([right.into(), middle.into(), left.into()])
            .expect("should be able to join 3 mutable pages into immutable pages");

        check_counters(&pages.allocation, [0, 1, 0]);

        for (i, b) in pages.slice().iter().enumerate() {
            let expected = 10 + (i / mem::page_size());
            assert_eq!(
                *b, expected as u8,
                "reading value at index {i} from joined pages failed"
            );
        }

        let pages = pages
            .try_into_inaccessible()
            .expect("should be able to convert immutable pages into inaccessible pages");

        check_counters(&pages.allocation, [0, 0, 1]);

        let allocation = pages
            .try_into_allocation()
            .expect("should be able to convert only remaining pages reference to allocation");

        check_counters(&allocation, [0, 0, 1]);

        let mut pages = allocation.try_into_pages_mut().expect(
            "should be able to convert allocation from inaccessible pages into mutable pages",
        );

        check_counters(&pages.allocation, [1, 0, 0]);

        for (i, b) in pages.slice_mut().iter_mut().enumerate() {
            let expected = 10 + (i / mem::page_size());
            assert_eq!(
                *b, expected as u8,
                "reading value at index {i} from mutable pages from allocation from inaccessible pages failed"
            );

            *b = 20;
        }

        for b in pages.slice() {
            assert_eq!(*b, 20, "rw test failed");
        }
    }
}
