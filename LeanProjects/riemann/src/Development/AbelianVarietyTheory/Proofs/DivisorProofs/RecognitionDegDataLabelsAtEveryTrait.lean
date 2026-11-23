import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPointOfAlgebraicSeriesOneTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisEquivariantTorsionValuesUltrametricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsInducedAllEmbeddingsOfGaloisStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Recognition

theorem pullDeg_induces : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre A lab → GalEqN n lab → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (a : A'.A.left ⟶ A.A.left), IsSemiAbelian G' → IsFib φ A A' a → ∃ hD : IsPullDeg φ D.toPre D'.toPre, ∀ j : ℕ, Induces lab φ U' hD a (n ^ j) := by
  intro R _ _ _ hR D A lab n hn ho hu hOT hGal W _ _ _ hW φ hφ hloc G' _ _ D' A' U' a hG hF
  obtain ⟨hD, C, i1, i2, i3, i4, em, hc, hP⟩ := GlobalTheory.T.galois_equivariant_torsion_values_ultrametric R hR D A lab n hn ho hu hOT hGal
    (GlobalTheory.T.isThetaPoint_of_algebraic_series_one_trait R hR D A lab n hn ho hu hOT) W hW φ hφ hloc G' D' A' U' a hG hF
  exact ⟨hD, fun j => GlobalTheory.T.labels_induced_all_embeddings_of_galois R hR D A lab n hn ho hu hGal W hW φ hφ hloc G' D' A' U' a hG hF hD j
    ⟨C, i1, i2, i3, i4, em, hc, hP j⟩⟩

end GlobalTheory.Mum.Recognition
