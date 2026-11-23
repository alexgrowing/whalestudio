import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionLabelsUniformisedDominatingTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationThetaSeriesAlgebraicOverFractionFielStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPointOfAlgebraicSeriesOneTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtRationalTorsionUniformisedTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsGaloisAllLevelsOfSquaresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesValuesGaloisScalarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLevelLabelsGaloisConjEqSerreLemmaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_finExt_galEqN : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))) (lab : Labels D₁.toPre A), FinExt ρ → Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → OneTrait D₁.toPre A lab → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ₂ : R →+* R₂) (D₂ : DegData R₂ (maximalIdeal R₂)) (A₂ : PolAV (Sp (FractionRing R₂))) (lab₂ : Labels D₂.toPre A₂), FinExt ρ₂ ∧ Nonempty (IsPullDeg ρ₂ D.toPre D₂.toPre) ∧ (letI := A₂.isAb.comm; GlobalTheory.ZH.HypS A₂.A A₂.L) ∧ OneTrait D₂.toPre A₂ lab₂ ∧ GalEqN n lab₂ := by
  intro R _ _ _ hR D n hn ho hu R₁ _ _ _ ρ D₁ A lab hρ hP hS hOT
  have hU₁ : UniTrait D₁.toPre A := by
    obtain ⟨W, i1, i2, i3, φ, G', i4, i5, D', A', U', hD, a, i6, em, hW, hφ, hloc, hG, hF, -, -⟩ := hOT
    exact ⟨W, i1, i2, i3, φ, G', i4, i5, D', A', U', hD, a, hW, hφ, hloc, hG, hF⟩
  obtain ⟨R₂, _, _, _, ρ₂, D₂, A₂, hρ₂, hP₂, hS₂, hU₂, hRat⟩ := GlobalTheory.T.exists_finite_ext_rational_torsion_uniformised_trait R hR D n hn ho hu R₁ ρ D₁ A hρ hP hS hU₁
  have hB₂ : Base R₂ := by
    have := hR.2
    exact ⟨hρ₂.1, charZero_of_injective_ringHom hρ₂.2.1⟩
  have hu₂ : IsUnit (n : R₂) := by simpa using hu.map ρ₂
  obtain ⟨lab₂, hOT₂⟩ := GlobalTheory.T.exists_torsionLabels_uniformisedDominatingTrait R₂ hB₂ D₂ A₂ hU₂
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, ρ₂, D₂, A₂, lab₂, hρ₂, hP₂, hS₂, hOT₂, ?_⟩
  obtain ⟨i₀, hi₀⟩ := GlobalTheory.T.thetaLevelLabels_galoisConj_eq_serreLemma R₂ hB₂ n hn ho hu₂ D₂ A₂ lab₂ hOT₂ hRat
  refine GlobalTheory.T.torsionLabels_galois_all_levels_of_squares R₂ hB₂ n hn ho hu₂ D₂ A₂ lab₂ hOT₂ ⟨i₀, fun i hi => ?_⟩
  have hmo : Odd (n ^ i) := ho.pow
  have hmu : IsUnit ((n ^ i : ℕ) : R₂) := by rw [Nat.cast_pow]; exact hu₂.pow i
  obtain ⟨v, hv⟩ := GlobalTheory.T.degenerationThetaSeries_algebraic_over_fractionField R₂ hB₂ D₂ (n ^ i) hmo hmu (QkPt D₂.toPre (Kb R₂) ((n ^ i) ^ 2)) id
  have hθ := GlobalTheory.T.isThetaPoint_of_algebraic_series_one_trait R₂ hB₂ D₂ A₂ lab₂ n hn ho hu₂ hOT₂ i v hv
  exact hi₀ i hi v hθ (GlobalTheory.T.thetaSeries_values_galois_scalar R₂ hB₂ D₂ A₂ lab₂ hOT₂ (n ^ i) hmo hmu v hv)

end GlobalTheory.Mum
