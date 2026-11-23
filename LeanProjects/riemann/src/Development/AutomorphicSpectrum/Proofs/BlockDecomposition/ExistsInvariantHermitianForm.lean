import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.HasInfCharOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalisedCuspFormL2BoundedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieActionSkewAdjointL2Statement

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.ClozelHerm

def petersson {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (μ : Measure (GA E a))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (π : CuspSub E a)
    (hm : ∀ φ ∈ π.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1) :
    π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun φ ψ => inner ℂ (toL2ₗ μ π.V hm ψ) (toL2ₗ μ π.V hm φ))
    (fun φ φ' ψ => by simp only [map_add, inner_add_right])
    (fun c φ ψ => by simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply])
    (fun φ ψ ψ' => by simp only [map_add, inner_add_left])
    (fun c φ ψ => by simp only [map_smul, inner_smul_left, smul_eq_mul])

theorem exists_isHerm : GlobalTheory.Published.CuspFormsBoundedGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (π : CuspSub E a), GlobalTheory.DiscSpec.IsNormalised π → ∃ B : π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ, IsHerm π B := by
  intro hB E _ _ _ a μ _ _ π hπ
  have hl := GlobalTheory.T.normalised_cusp_form_L2_bounded hB E a μ π hπ
  have hm : ∀ φ ∈ π.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1 := fun φ hφ => (hl φ hφ).1
  have hb : ∀ φ ∈ π.V, ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C := fun φ hφ => (hl φ hφ).2
  refine ⟨petersson μ π hm, fun X φ ψ => GlobalTheory.T.lie_action_skew_adjoint_L2 E a μ π hm hb X φ ψ, ?_⟩
  obtain ⟨φ, hφ, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne_bot
  have hi : Function.Injective (toL2ₗ μ π.V hm) :=
    toL2ₗ_injective hm fun ψ hψ => ContAut.continuous_of_isOpen_stab E a ψ (π.cusp ψ hψ).1.level
  have hT : toL2ₗ μ π.V hm ⟨φ, hφ⟩ ≠ 0 := fun h =>
    hne (congrArg Subtype.val (hi (h.trans (map_zero _).symm)))
  refine ⟨⟨φ, hφ⟩, ?_⟩
  show inner ℂ (toL2ₗ μ π.V hm ⟨φ, hφ⟩) (toL2ₗ μ π.V hm ⟨φ, hφ⟩) ≠ 0
  exact inner_self_ne_zero.2 hT

end GlobalTheory.CompanionTheory.ClozelHerm

end
