import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenUIsGenFam
import Development.WeilBound.CoreStatements.PluriharmonicCharts.AdjoinLow

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

private theorem revInv_unitriangular_and_mem_of_unitriangular {Ω G : Type} [Field Ω] [Field G] [Algebra Ω G] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) G) (hd : ∀ a, M a a = 1) (hl : ∀ a b, a < b → M a b = 0) :
    (∀ a, revInv M a a = 1) ∧ (∀ a b, a < b → revInv M a b = 0) ∧
      ∀ F : IntermediateField Ω G, (∀ a b, revInv M a b ∈ F) → ∀ a b, M a b ∈ F := by
  classical
  have hup : (Mᵀ).BlockTriangular id := by
    intro i j hij
    rw [Matrix.transpose_apply]
    exact hl j i hij
  have hunit : IsUnit (Mᵀ).det := by
    rw [Matrix.det_of_isUpperTriangular hup]
    simp [Matrix.transpose_apply, hd]
  letI : Invertible (Mᵀ) := Matrix.invertibleOfIsUnitDet _ hunit
  have hup' : (Mᵀ)⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hup
  have hdiag : ∀ i, (Mᵀ)⁻¹ i i = 1 := by
    intro i
    have h1 : ((Mᵀ)⁻¹ * Mᵀ) i i = 1 := by
      rw [Matrix.nonsing_inv_mul _ hunit, Matrix.one_apply_eq]
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
    · simpa [Matrix.transpose_apply, hd] using h1
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hup' h, zero_mul]
      · rw [hup h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hrev : ∀ a b, revInv M a b = (Mᵀ)⁻¹ a.rev b.rev := fun a b => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro a
    rw [hrev]
    exact hdiag _
  · intro a b hab
    rw [hrev]
    exact hup' (Fin.rev_lt_rev.mpr hab)
  · intro F hF a b
    have hmem : ∀ x y, (Mᵀ)⁻¹ x y ∈ F := by
      intro x y
      have := hF x.rev y.rev
      rwa [hrev, Fin.rev_rev, Fin.rev_rev] at this
    have hdet' : IsUnit ((Mᵀ)⁻¹).det := Matrix.isUnit_nonsing_inv_det _ hunit
    have := PositivityTheory.Xgp.GenFam.inv_mem F ((Mᵀ)⁻¹) hdet' hmem b a
    rwa [Matrix.nonsing_inv_nonsing_inv _ hunit, Matrix.transpose_apply] at this

theorem PositivityTheory.Xgp.t_c_fm_exists_flags_revgen : ∀ (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] (S : Type) [Finite S] (r : S → ℕ) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) (P : S → Prop) [DecidablePred P], IsGenFam Ω G u → IsGenFam Ω G (fun s => if P s then revInv (u s) else u s) := by
  intro Ω G _ _ _ S _ r u P _ hu
  have hu' := hu
  obtain ⟨hd, hl, -, -⟩ := hu'
  have key := fun s => revInv_unitriangular_and_mem_of_unitriangular (Ω := Ω) (u s) (hd s) (hl s)
  refine PositivityTheory.Xgp.GenFam.of_gen hu ?_ ?_ ?_
  · intro s a
    by_cases h : P s
    · rw [if_pos h]
      exact (key s).1 a
    · rw [if_neg h]
      exact hd s a
  · intro s a b hab
    by_cases h : P s
    · rw [if_pos h]
      exact (key s).2.1 a b hab
    · rw [if_neg h]
      exact hl s a b hab
  · intro s a b
    have hsub : ∀ x y, (if P s then revInv (u s) else u s) x y ∈
        IntermediateField.adjoin Ω (Set.range fun (q : (σ : S) × Fin (r σ) × Fin (r σ)) =>
          (if P q.fst then revInv (u q.fst) else u q.fst) q.snd.1 q.snd.2) :=
      fun x y => IntermediateField.subset_adjoin _ _ ⟨⟨s, x, y⟩, rfl⟩
    by_cases h : P s
    · rw [if_pos h] at hsub
      exact (key s).2.2 _ hsub a b
    · rw [if_neg h] at hsub
      exact hsub a b
