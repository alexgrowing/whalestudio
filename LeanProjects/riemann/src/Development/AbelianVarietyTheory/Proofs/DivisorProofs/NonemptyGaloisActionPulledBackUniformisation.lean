import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedGroupGaloisAutomorphismMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapMulStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem galAct_nonempty : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), Nonempty (GalAct ρ hD U') := by
  intro R _ _ _ hR R' _ _ _ ρ hfin hgal D D' hD A' G' _ _ hG U'
  have hex : ∀ σ : Gal ρ, ∃ a, GalMap hD U' σ a := GlobalTheory.T.exists_uniformisedGroup_galoisAutomorphism_map R hR R' ρ hfin D D' hD A' G' hG U'
  choose act hact using hex
  exact ⟨{ act := act
           cart := fun σ => (hact σ).1
           act_one := GlobalTheory.T.uniformisedGroup_galoisMap_unique R hR R' ρ hfin D D' hD A' G' hG U' 1 _ _ (hact 1) (GlobalTheory.T.uniformisedGroup_galoisMap_one R hR R' ρ hfin D D' hD A' G' hG U')
           act_mul := fun σ τ => GlobalTheory.T.uniformisedGroup_galoisMap_unique R hR R' ρ hfin D D' hD A' G' hG U' (σ * τ) _ _ (hact (σ * τ))
             (GlobalTheory.T.uniformisedGroup_galoisMap_mul R hR R' ρ hfin D D' hD A' G' hG U' σ τ _ _ (hact σ) (hact τ))
           unif := fun σ => (hact σ).2 }⟩

end GlobalTheory.Mum
