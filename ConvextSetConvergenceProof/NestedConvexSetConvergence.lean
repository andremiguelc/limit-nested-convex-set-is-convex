import Mathlib

open scoped Topology
open Filter
open Set

namespace NestedConvexSetConvergence

/-! ### Core definitions -/
/-- Kuratowski upper limit (outer limit) of a sequence of sets `C n`. -/
def kuratowskiLimsup {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (C : ℕ → Set X) : Set X :=
  {x : X |
    ∃ (n : ℕ → ℕ), StrictMono n ∧
    ∃ (xk : ℕ → X),
      (∀ k, xk k ∈ C (n k)) ∧ Tendsto xk atTop (𝓝 x)}

/-! ### Practice / sandbox -/
section Practice
-- Practice theorem to apply definition
-- The set sequence of the universe implies that any x is part of the Limsup of that sequence
theorem mem_kuratowskiLimsup_univ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (x : X) :
    x ∈ kuratowskiLimsup (X := X) (fun _n : ℕ => (Set.univ : Set X)) := by
  change
    (∃ (n : ℕ → ℕ), StrictMono n ∧
      ∃ (xk : ℕ → X),
        (∀ k, xk k ∈ (Set.univ : Set X)) ∧ Tendsto xk atTop (𝓝 x))
  refine ⟨fun k => k, ?_⟩
  refine ⟨?_, ?_⟩
  · intro a b hab
    exact hab
  · refine ⟨fun _k => x, ?_⟩
    refine ⟨?_, ?_⟩
    · intro k
      simp
    · simp

-- Practice lemma to work induction on nested set sequences
lemma subset_of_succ_subset
  {X : Type*} {C : ℕ → Set X}
  (h : ∀ n, C (n + 1) ⊆ C n)
  {a b : ℕ} (hab : a ≤ b) :
  C b ⊆ C a := by

  refine (Nat.le_induction (m := a) (P := fun n _hn => C n ⊆ C a) ?_ ?_ b hab)
  · intro x hx
    exact hx
  · intro n hmn ih x hx
    exact ih ((h n) hx)
end Practice

/-! ### Helper lemmas for the main proof -/
section Helpers
-- If `C (n+1) ⊆ C n` for all `n`, then `C` is antitone (nested decreasing). -
lemma antitone_of_succ_subset {X : Type*} {C : ℕ → Set X}
    (h : ∀ n, C (n + 1) ⊆ C n) : Antitone C := by
  exact antitone_nat_of_succ_le h
end Helpers

/-! ### Main theorem -/
section Main

theorem convex_kuratowskiLimsup_of_succ_subset
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {C : ℕ → Set X}
    (h : ∀ n, C (n + 1) ⊆ C n)
    (hconv : ∀ n, Convex ℝ (C n)) :
    Convex ℝ (kuratowskiLimsup (X := X) C) := by

  sorry

end Main

end NestedConvexSetConvergence
