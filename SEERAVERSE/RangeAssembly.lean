import Mathlib

/-!
# Range assembly

Glues together depth results proved on individual ranges into a single
global statement over all `N ≥ 1`.
-/
namespace RangeAssembly

theorem all_depth_from_three_ranges
    (P : ℕ → Prop)
    (h1 : ∀ N, 1 ≤ N → N ≤ 4052 → P N)
    (h2 : ∀ N, 4053 ≤ N → N ≤ 10148 → P N)
    (h3 : ∀ N, 10149 ≤ N → P N) :
    ∀ N, 1 ≤ N → P N := by
  intro N hN
  by_cases h4052 : N ≤ 4052
  · exact h1 N hN h4052
  by_cases h10148 : N ≤ 10148
  · exact h2 N (by omega) h10148
  · exact h3 N (by omega)
#check RangeAssembly.all_depth_from_three_ranges
#print axioms RangeAssembly.all_depth_from_three_ranges
end RangeAssembly
