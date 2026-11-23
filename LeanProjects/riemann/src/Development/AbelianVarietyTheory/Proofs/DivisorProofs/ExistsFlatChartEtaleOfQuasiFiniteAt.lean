import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleNeighbourhoodFinitePieceIsolatedPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoFinitePieceFlatConnectedChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_flat_chart_etale_of_quasiFiniteAt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → (∃ O : U.left.Opens, x ∈ O ∧ ∀ u ∈ O, τ u = τ x → u = x) → ∃ (T : Scheme.{0}) (h : T ⟶ 𝔸(Fin g; Sp R)) (W : (pullback τ h).Opens) (p : ↥(pullback τ h)), Flat h ∧ p ∈ W ∧ pullback.fst τ h p = x ∧ Etale (W.ι ≫ pullback.snd τ h) := by
  intro R _ _ _ hR S X π U a b g τ c hπp hπs hπΓ hUf hUs ha haΓ hτ hc1 hc2 hc x hxc hxm hinj hsurj hqf
  have hτf : LocallyOfFiniteType τ := by
    have : LocallyOfFiniteType (τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R)) := by rw [hτ]; exact hUf
    exact locallyOfFiniteType_of_comp τ (𝔸(Fin g; Sp R) ↘ Sp R)
  have hτs : IsSeparated τ := by
    have : IsSeparated (τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R)) := by rw [hτ]; exact hUs
    exact IsSeparated.of_comp τ (𝔸(Fin g; Sp R) ↘ Sp R)
  have : IsNoetherianRing R := hR.1
  have hA : IsLocallyNoetherian 𝔸(Fin g; Sp R) := LocallyOfFiniteType.isLocallyNoetherian (𝔸(Fin g; Sp R) ↘ Sp R)
  obtain ⟨T, h, W, p, het, hcon, hpW, hpx, hfin, hone, hgeo⟩ := GlobalTheory.T.exists_etale_neighbourhood_finite_piece_isolated_point _ _ τ hA hτf hτs x hqf
  have hiso := GlobalTheory.T.isIso_finite_piece_flat_connected_chart R hR S X π U a b g τ c hπp hπs hπΓ hUf hUs ha haΓ hτ hc1 hc2 hc x hxm hinj hsurj
    T h W p inferInstance hcon hpW hpx hfin hone hgeo
  exact ⟨T, h, W, p, inferInstance, hpW, hpx, inferInstance⟩
