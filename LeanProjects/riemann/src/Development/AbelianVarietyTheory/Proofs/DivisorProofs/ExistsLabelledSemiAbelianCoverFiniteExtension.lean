import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeometricFibreIsoOfTraitUniformisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedTraitDescentFiniteExtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionLabelsUniformisedDominatingTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionGaloisEquivariantLabelsStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_desc_labels : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (D' : DegData W (maximalIdeal W)) (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (A' : PolAV (Sp (FractionRing W))), Nonempty (IsPullDeg φ D.toPre D'.toPre) → IsSemiAbelian G' → Nonempty (Unif (maximalIdeal W) D' A' G') → (letI := A'.isAb.comm; GlobalTheory.ZH.HypS A'.A A'.L) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))) (lab : Labels D₁.toPre A), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) ∧ OneTrait D₁.toPre A lab ∧ GalEqN n lab := by
  intro R _ _ _ hR D n hn ho hu W _ _ _ hW φ hφ hl D' G' _ _ A' hP hG hU hS
  obtain ⟨A₀, e₀, hc, hS₀, hI⟩ := GlobalTheory.T.exists_geometricFibreIso_of_traitUniformisation R hR D n hn ho hu W hW φ hφ hl D' G' A' hP hG hU hS
  obtain ⟨R₁, _, _, _, ρ, D₁, A, hF, hP₁, hS₁, hT⟩ :=
    GlobalTheory.T.exists_uniformisedTrait_descent_finite_ext R hR D n hn ho hu W hW φ hφ hl D' G' A' hP hG hU hS A₀ e₀ hc hS₀ hI
  have hR₁ : Base R₁ := ⟨hF.1, by haveI := hR.2; exact charZero_of_injective_ringHom hF.2.1⟩
  obtain ⟨lab, hO⟩ := GlobalTheory.T.exists_torsionLabels_uniformisedDominatingTrait R₁ hR₁ D₁ A hT
  exact GlobalTheory.T.exists_finite_extension_galois_equivariant_labels R hR D n hn ho hu R₁ ρ D₁ A lab hF hP₁ hS₁ hO

end GlobalTheory.Mum
