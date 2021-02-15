#pragma once

template <typename T>
struct ref_ptr_cmp {
    constexpr bool operator() (const std::reference_wrapper<T>& lhs,
                               const std::reference_wrapper<T>& rhs) const {
      return std::addressof (lhs.get ()) < std::addressof (rhs.get ());
    }
};
