import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTripleMapOfSameUniformisedCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tripleMap_of_same_uniformised_coords : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base R → GlobalTheory.Mum.Base V → ∀ (t₁ : SAB H (Sp R)) (P₁ : PELUnif (maximalIdeal R) t₁) (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (iw : L.W →+* R) (θ : R →+* V), IsLocalHom θ → ∀ {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e₁ : P₁.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, θ (s k) ≠ 0) → DivFrom L P₁.D.toPre P₁.oD iw s ε e₁ → DivFrom L P.D.toPre P.oD (θ.comp iw) (fun k => θ (s k)) ε e → Nonempty (SABMap t t₁ (spMap θ)) := by
  first | exact @GlobalTheory.UCanon.sabMap_of_same_coords | exact GlobalTheory.UCanon.sabMap_of_same_coords | (intros; apply GlobalTheory.UCanon.sabMap_of_same_coords <;> assumption)
