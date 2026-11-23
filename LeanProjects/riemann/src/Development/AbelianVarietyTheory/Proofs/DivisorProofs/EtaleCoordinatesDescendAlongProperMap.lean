import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsolatedInFibreCoordinateMapAffineSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatChartEtaleOfQuasiFiniteAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNhdsAffineSpaceMapOfFlatBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyPulledBackNearPointOfEtaleCoordinatesStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem etale_coord_descend : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∃ V : U.left.Opens, x ∈ V ∧ Etale (V.ι ≫ τ) ∧ IsPullback (a ∣_ V) ((a ⁻¹ᵁ V).ι ≫ b) (V.ι ≫ U.hom) π := by
  intro R _ _ _ hR S X π U a b g τ c hπ hs hΓ hlft hsep ha haV hτ hc1 hc2 hc x hx hxc hmono hsurj
  have hq := GlobalTheory.T.isolated_in_fibre_coordinateMap_affineSpace R hR S X π U a b g τ c hπ hs hΓ hlft hsep ha haV hτ hc1 hc2 hc x hx hxc hmono hsurj
  obtain ⟨T, h, W, p, hfl, hpW, hpx, hW⟩ := GlobalTheory.T.exists_flat_chart_etale_of_quasiFiniteAt_alt R hR S X π U a b g τ c hπ hs hΓ hlft hsep ha haV hτ hc1 hc2 hc x hx hxc hmono hsurj hq
  obtain ⟨V, hxV, hV⟩ := GlobalTheory.T.etale_nhds_affineSpace_map_of_flat_baseChange R hR U g τ hlft hτ T h hfl W p hpW hW
  rw [hpx] at hxV
  exact GlobalTheory.T.family_pulled_back_near_point_of_etale_coordinates R hR S X π U a b g τ c hπ hs hΓ hlft hsep ha haV hτ hc1 hc2 hc x hx hxc hmono hsurj V hxV hV

end GlobalTheory.Mum
