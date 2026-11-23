import Mathlib
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.DecInertia

theorem valuation_lt_one_iff_norm {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] {A : ValuationSubring Ω}
    {j : Ω →+* PadicAlgCl p} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) (x : Ω) :
    A.valuation x < 1 ↔ ‖j x‖ < 1 := by
  rw [valuation_lt_one_iff', hj, hj, map_inv₀, norm_inv]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h0 : 0 < ‖j x‖ := norm_pos_iff.mpr ((_root_.map_ne_zero _).mpr hx)
    simp only [hx, false_or, not_le, one_lt_inv₀ h0]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

theorem inertiaK_iff_mem_Ine (p : ℕ) [Fact p.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p) (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (i : ↥(A.decompositionSubgroup F) ≃* (PadicAlgCl p ≃ₐ[↥K] PadicAlgCl p))
    (hi : ∀ (g : ↥(A.decompositionSubgroup F)) (x : Ω), i g (j x) = j ((g : Ω ≃ₐ[F] Ω) x))
    (g : ↥(A.decompositionSubgroup F)) :
    i g ∈ Formalism.GaloisCohomology.inertiaK p K ↔ (g : Ω ≃ₐ[F] Ω) ∈ Ine (F := F) A := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have hn : ∀ (σ : PadicAlgCl p ≃ₐ[↥K] PadicAlgCl p) (z : PadicAlgCl p), ‖σ z‖ = ‖z‖ := fun σ z =>
    GlobalTheory.PlaceBridge.norm_algEquiv (σ.restrictScalars ℚ_[p]) z
  have hadd : ∀ a b : PadicAlgCl p, ‖a + b‖ ≤ max ‖a‖ ‖b‖ := IsUltrametricDist.norm_add_le_max
  constructor
  · intro h
    let H : Subgroup (PadicAlgCl p ≃ₐ[↥K] PadicAlgCl p) :=
      ((Ine (F := F) A).subgroupOf (A.decompositionSubgroup F)).map i.toMonoidHom
    have hsub : Formalism.GaloisCohomology.inertiaSet p K ⊆ H := by
      intro σ hσ
      refine ⟨i.symm σ, ?_, by simp⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      refine ⟨(i.symm σ).2, fun x hx => ?_⟩
      rw [valuation_lt_one_iff_norm hj, map_sub, ← hi, MulEquiv.apply_symm_apply]
      exact hσ (j x) ((hj x).1 ((A.valuation_le_one_iff x).1 hx))
    have hle : Formalism.GaloisCohomology.inertiaK p K ≤ H := (Subgroup.closure_le _).2 hsub
    obtain ⟨g', hg', e⟩ := hle h
    have : g' = g := i.injective e
    subst this
    exact Subgroup.mem_subgroupOf.1 hg'
  · intro h
    apply Subgroup.subset_closure
    intro x hx
    obtain ⟨y, hy⟩ := (GlobalTheory.PlaceBridge.denseRange_embedding j).exists_dist_lt x one_pos
    rw [dist_eq_norm] at hy
    have hjy : ‖j y‖ ≤ 1 := by
      have e : j y = x + -(x - j y) := by ring
      rw [e]
      exact (hadd _ _).trans (max_le hx (by rw [norm_neg]; exact hy.le))
    have hgy : ‖(i g) (j y) - j y‖ < 1 := by
      rw [hi, ← map_sub, ← valuation_lt_one_iff_norm hj]
      exact h.2 y ((A.valuation_le_one_iff y).2 ((hj y).2 hjy))
    have e : (i g) x - x = (i g) (x - j y) + (((i g) (j y) - j y) + -(x - j y)) := by
      rw [map_sub]; ring
    rw [e]
    refine (hadd _ _).trans_lt (max_lt (by rw [hn]; exact hy) ((hadd _ _).trans_lt (max_lt hgy ?_)))
    rw [norm_neg]; exact hy

end GlobalTheory.DecInertia
