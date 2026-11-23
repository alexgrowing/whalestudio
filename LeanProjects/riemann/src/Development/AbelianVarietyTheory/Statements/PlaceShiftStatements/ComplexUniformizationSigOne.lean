import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PointsNonemptyUnitaryGaussian

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ComplexUniformization

def ComplexUniformizationSigOne : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → D.Compact →
    ∀ (R : Type) [CommRing R] (b : Base D R) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ),
    b.Matches σ → b.IsType σ ρ → ∀ N : ℕ, 3 ≤ N → N.Coprime p → ∀ (M : Model b N) (v : InfinitePlace G.F),
    sigPosH (G.gram_herm v) = 1 →
    ∃ Φ : GlobalTheory.LKCx.CxPtsM M σ ≃ GlobalTheory.LKCx.AllPts G v (L.KN N) (GlobalTheory.LKCx.KpOne G),
      ∀ (y : GlobalTheory.LKCx.CxPtsM M σ) (o : Obj b N (spMap σ)), Classifies M y.1 o →
        ∀ (q : GlobalTheory.LKCx.FCls G) (a : GlobalTheory.LKCx.Dat G v (Quot.out q).β),
          Φ y = (⟨q, Quot.mk _ a⟩ : GlobalTheory.LKCx.AllPts G v (L.KN N) (GlobalTheory.LKCx.KpOne G)) →
          ∃ E : GlobalTheory.LKCx.QIsog L o ≃ GlobalTheory.LKCx.FixP v (Quot.out q) (GlobalTheory.LKCx.KpOne G) a,
            (∀ π : GlobalTheory.LKCx.QIsog L o, IsGamma L o π.1 (a.1.1⁻¹ * GlobalTheory.LKCx.Form.toAf (Quot.out q) (E π).1 * a.1.1)) ∧
            Nat.card {π : GlobalTheory.LKCx.QIsog L o // ∃ k ∈ L.KN N, IsGamma L o π.1 k} =
              Nat.card (GlobalTheory.LKCx.Form.Stab v (Quot.out q) (L.KN N) (GlobalTheory.LKCx.KpOne G) a)

theorem complex_unif_of_sig_one (h : ComplexUniformizationSigOne) : GlobalTheory.LKCx.CxUnif := by
  intro p _ D G L hD R _ b σ ρ hm ht N hN hNp M v hv
  refine h p D G L hD.1 (Or.inr ⟨hD.2.2, ?_⟩) R b σ ρ hm ht N hN hNp M v hv
  have h1 := hD.2.1
  have h2 := D.n_pos
  omega

end GlobalTheory.ComplexUniformization
