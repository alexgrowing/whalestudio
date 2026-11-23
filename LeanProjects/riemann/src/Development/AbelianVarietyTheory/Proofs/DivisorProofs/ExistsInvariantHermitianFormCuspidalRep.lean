import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieSkewAdjointMatrixStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIntegrableSmoothSubmoduleGL
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
open MeasureTheory GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC

noncomputable section

namespace GlobalTheory.GelfandKazhdanHerm

open scoped InnerProductSpace

theorem exists_invariant_hermitian : GlobalTheory.Published.CuspFormsBoundedGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), GlobalTheory.DiscSpec.IsNormalised π → ∃ H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ, (∀ φ ψ, starRingEnd ℂ (H φ ψ) = H ψ φ) ∧ (∀ φ, φ ≠ 0 → 0 < (H φ φ).re) ∧ (∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) ∧ (∀ k φ ψ, H (π.op (.cpt k) φ) (π.op (.cpt k) ψ) = H φ ψ) ∧ ∀ X φ ψ, H (π.op (.lie X) φ) ψ + H φ (π.op (.lie X) ψ) = 0 := by
  intro hB E _ _ _ a π hπ
  let μ : Measure (GA E a) := Measure.haar
  haveI : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  have hc : ∀ φ ∈ π.V, Continuous φ.1 := fun φ hφ =>
    ContAut.continuous_of_isOpen_stab E a φ (π.cusp φ hφ).1.level
  have hm : ∀ φ ∈ π.V, MemL2Quotient (latticeGL E a) μ φ.1 := fun φ hφ => by
    obtain ⟨C, hC⟩ := hB.of_invariant (π.cusp φ hφ) (hπ φ hφ)
    exact (memL2_iff_isSqInt (hc φ hφ) (π.cusp φ hφ).1.left (hπ φ hφ)).2
      (GlobalTheory.DiscChar.isSqInt_of_bounded (hπ φ hφ) hC)
  let T := toL2ₗ μ π.V hm
  have hinj : Function.Injective T := toL2ₗ_injective hm hc
  have hR : ∀ (g : GA E a) (x y : L2 (latticeGL E a) μ),
      ⟪R (latticeGL E a) μ g x, R (latticeGL E a) μ g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g x y => by
    let U : L2 (latticeGL E a) μ →ₗᵢ[ℂ] L2 (latticeGL E a) μ :=
      ⟨(R (latticeGL E a) μ g).toLinearMap, fun v => norm_R _ v⟩
    exact U.inner_map_map x y
  refine ⟨((innerₛₗ ℂ).comp T).compl₂ T, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ ψ
    exact inner_conj_symm (T ψ) (T φ)
  · intro φ h0
    have hT : T φ ≠ 0 := fun e => h0 (hinj (e.trans (map_zero T).symm))
    change 0 < (⟪T φ, T φ⟫_ℂ).re
    first
      | exact (re_inner_self_pos (𝕜 := ℂ)).2 hT
      | exact inner_self_pos.2 hT
      | exact (RCLike.inner_self_pos).2 hT
      | (rw [inner_self_eq_norm_sq_to_K]; norm_cast; simpa using hT)
  · intro k φ ψ
    change ⟪T (π.op (.fin k) φ), T (π.op (.fin k) ψ)⟫_ℂ = ⟪T φ, T ψ⟫_ℂ
    rw [← hR (finGL E a k) (T φ) (T ψ)]
    congr 1
    · exact (R_toL2ₗ hm φ (π.stable (.fin k) _ φ.2)).symm
    · exact (R_toL2ₗ hm ψ (π.stable (.fin k) _ ψ.2)).symm
  · intro k φ ψ
    change ⟪T (π.op (.cpt k) φ), T (π.op (.cpt k) ψ)⟫_ℂ = ⟪T φ, T ψ⟫_ℂ
    rw [← hR (infGL E a (Unitary.toUnits k)) (T φ) (T ψ)]
    congr 1
    · exact (R_toL2ₗ hm φ (π.stable (.cpt k) _ φ.2)).symm
    · exact (R_toL2ₗ hm ψ (π.stable (.cpt k) _ ψ.2)).symm
  · intro X φ ψ
    change ⟪T (π.op (.lie X) φ), T ψ⟫_ℂ + ⟪T φ, T (π.op (.lie X) ψ)⟫_ℂ = 0
    have := GlobalTheory.T.lie_skew_adjoint_matrix E a μ π.V hm π.stable (fun θ hθ => (π.cusp θ hθ).1) X φ ψ
    rw [eq_neg_iff_add_eq_zero] at this
    exact this

end GlobalTheory.GelfandKazhdanHerm

end
