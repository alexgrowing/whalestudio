import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPointRelationFieldExt
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoordBC

attribute [local instance] Over.cartesianMonoidalCategory

theorem isCoord_map : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e) {k k' : Type} [Field k] [Field k'] (θ : k →+* k') {φ : c.F →+* k} {x : Sp k ⟶ Z.X} {φ' : c.F →+* k'} {x' : Sp k' ⟶ Z.X} (p : Sp k ⟶ Y.Y.X) (g : EigFrame Z φ x) (g' : EigFrame Z φ' x') (n : Letter Dw → ℤ) (s : Y.Y.Fn) (a : k), φ' = θ.comp φ → x' = spMap θ ≫ x → g.IsMap θ g' → IsCoord Y p g n s a → IsCoord Y (spMap θ ≫ p) g' n s (θ a) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e Y k k' _ _ θ φ x φ' x' p g g' n s a hφ hx hg hc
  obtain ⟨y, ψ, φ₁, f, t, t', r, hp, h1, h2, h3, h4⟩ := hc
  refine ⟨y, θ.comp ψ, φ₁, f, t, fun τ i => Units.map (θ : k →* k') (t' τ i), r, ?_, h1, ?_, h3, ?_⟩
  · rw [hp, ← Category.assoc, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
  · refine ⟨?_, ?_, fun τ i => ?_⟩
    · rw [hx, h2.1, ← Category.assoc, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
    · rw [hφ, h2.2.1]
      rfl
    · obtain ⟨cf, hc1, hc2, hc3⟩ := h2.2.2 τ i
      refine ⟨fun k => θ (cf k), by show θ (cf i) = _; rw [hc1]; rfl, fun k hk => by show θ (cf k) = 0; rw [hc2 k hk, map_zero], ?_⟩
      have h := GlobalTheory.GradedPieces.comb_map θ hx.symm hc3
      rw [hg τ i]
      simpa only [GlobalTheory.GradedPieces.dual_comp] using h
  · rw [h4, map_mul]
    congr 1
    have : (∏ z : Letter Dw, Units.map (θ : k →* k') (t' z.1 z.2) ^ (-n z)) =
        Units.map (θ : k →* k') (∏ z : Letter Dw, t' z.1 z.2 ^ (-n z)) := by
      simp only [map_prod, map_zpow]
    rw [this]
    rfl

end GlobalTheory.CoordBC
