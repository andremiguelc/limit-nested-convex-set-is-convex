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
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  dsimp [kuratowskiLimsup] at hx
  rcases hx with ⟨nx, hx⟩
  rcases hx with ⟨hMonox, hx⟩
  rcases hx with ⟨ck, hx⟩
  rcases hx with ⟨hck_mem, hx⟩
  dsimp [kuratowskiLimsup] at hy
  rcases hy with ⟨ny, hy⟩
  rcases hy with ⟨hMonoy, hy⟩
  rcases hy with ⟨sk, hy⟩
  rcases hy with ⟨hsk_mem, hy⟩
  --At the n index level, we are constructing n_hat
  set nhat : ℕ → ℕ := fun k => min (nx k) (ny k) with hnhat
  dsimp [kuratowskiLimsup]
  refine ⟨nhat, ?_⟩
  constructor
  · refine (strictMono_nat_of_lt_succ (α := ℕ) (f := nhat) ?_)
    intro k
    rw [hnhat]
    dsimp
    by_cases hmin : nx k ≤ ny k
    · --pos
      have hmin_eq : min (nx k) (ny k) = nx k := min_eq_left hmin
      rw [hmin_eq]
      apply (lt_min_iff).2
      constructor
      · exact hMonox (Nat.lt_succ_self k)
      · exact lt_of_le_of_lt (hmin) (hMonoy (Nat.lt_succ_self k))
    · --neg
      have hny_lt_nx : ny k < nx k := (not_le).1 hmin
      have hny_le_nx : ny k ≤ nx k := le_of_lt hny_lt_nx
      have hmin_eq : min (nx k) (ny k) = ny k := min_eq_right hny_le_nx
      rw [hmin_eq]
      apply (lt_min_iff).2
      constructor
      · exact lt_trans (hny_lt_nx) (hMonox (Nat.lt_succ_self k))
      · exact hMonoy (Nat.lt_succ_self k)
  · set tk : ℕ → X := fun k => a • ck k + b • sk k with htk
    refine ⟨tk, ?_⟩
    constructor
    · --set membership C nhat
      intro k
      rw [htk]
      have hanti : Antitone C := antitone_of_succ_subset (C := C) h
      have hle_x : nhat k ≤ nx k := by
        rw [hnhat]
        exact min_le_left (nx k) (ny k)
      have hck_hat : ck k ∈ C (nhat k) := (hanti hle_x) (hck_mem k)
      have hle_y : nhat k ≤ ny k := by
        rw [hnhat]
        exact min_le_right (nx k) (ny k)
      have hsk_hat : sk k ∈ C (nhat k) := (hanti hle_y) (hsk_mem k)
      have hconvk : Convex ℝ (C (nhat k)) := hconv (nhat k)
      have hadd := (convex_iff_add_mem).1 hconvk
      exact hadd hck_hat hsk_hat ha hb hab
    · -- convex combination tends to
      rw [htk]
      have hx' := hx.const_smul a
      have hy' := hy.const_smul b
      exact Tendsto.add (hx') (hy')
end Main

end NestedConvexSetConvergence
