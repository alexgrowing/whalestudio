import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.Reg GlobalTheory.FlagMod

namespace GlobalTheory

theorem exists_affine_domain_open_preimage {X X' : Scheme.{0}} (v : X' ⟶ X) (hv : IsOpenImmersion v)
    (U : X.Opens) (hU : IsAffineOpen U) (hD : IsDomain Γ(X, U)) (y : X') (hy : v y ∈ U) :
    ∃ U' : X'.Opens, IsAffineOpen U' ∧ IsDomain Γ(X', U') ∧ y ∈ U' ∧ U' ≤ v ⁻¹ᵁ U := by
  have hxV : v y ∈ U ⊓ v.opensRange := ⟨hy, ⟨y, rfl⟩⟩
  obtain ⟨r, hrle, hxr⟩ := hU.exists_basicOpen_le (V := U ⊓ v.opensRange) ⟨v y, hxV⟩ hy
  have hB : IsAffineOpen (X.basicOpen r) := hU.basicOpen r
  have hBr : X.basicOpen r ≤ v.opensRange := hrle.trans inf_le_right
  have hBU : X.basicOpen r ≤ U := hrle.trans inf_le_left
  have hU' : IsAffineOpen (v ⁻¹ᵁ X.basicOpen r) := hB.preimage_of_isOpenImmersion v hBr
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hxr
    exact hxr
  have hloc : IsLocalization.Away r Γ(X, X.basicOpen r) := hU.isLocalization_basicOpen r
  have hdomB : IsDomain Γ(X, X.basicOpen r) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers r) Γ(X, X.basicOpen r)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hr0)
  have himg : v ''ᵁ (v ⁻¹ᵁ X.basicOpen r) = X.basicOpen r := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.2 hBr]
  have hdomI : IsDomain Γ(X, v ''ᵁ (v ⁻¹ᵁ X.basicOpen r)) := by
    rw [himg]; exact hdomB
  refine ⟨v ⁻¹ᵁ X.basicOpen r, hU', ?_, hxr, fun z hz => hBU hz⟩
  exact (v.appIso (v ⁻¹ᵁ X.basicOpen r)).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _

end GlobalTheory
