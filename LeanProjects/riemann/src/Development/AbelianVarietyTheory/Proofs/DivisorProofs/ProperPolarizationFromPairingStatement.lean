import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperPolarizationFromPairing
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaSuccPow

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PDiv GlobalTheory.PDivGroup WithConv
open GlobalTheory.DeRham (spOver spOver_comp)

open GlobalTheory GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Closed

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_polarization_from_pairing : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {t : SAB H (Sp k)} {p : ℕ} [Fact p.Prime] {GG : PDivGroup p k} (tw : GG.TorsionTower t.G) (I : GeomTate Dw t), IsProper t.G.hom → ∀ φ : GG ⟶ GG.dual, (∀ (x y : Dw.La) (n : ℕ), muRoot (pairing GG k (tau tw I x) (tateMap GG GG.dual k φ (tau tw I y))) n = ((I.ζ (p ^ n) ^ Dw.EF x y : kˣ) : k)) → ∀ (n : ℕ) (K : Type) [Field K] [IsAlgClosed K] [Algebra k K] (x x' : Tors t.G (p ^ n) K) (y : Dw.La) (u : Kˣ), (TorsionMap.ofTower tw).pt n K x' = tatePt (tau tw I y) n K → (u : K) = (TorsionMap.ofTower tw).pt n K x (charElem (tateMap GG GG.dual k φ (tau tw I y)) n) → Out.WeilIs t.G t.PP.L ((p ^ n : ℕ) : ℤ) x.1 x'.1 (unitOn u) := by
  first | exact @GlobalTheory.GroupBplus.ClosedWeil.weilIs_of_pairing | exact GlobalTheory.GroupBplus.ClosedWeil.weilIs_of_pairing | (intros; apply GlobalTheory.GroupBplus.ClosedWeil.weilIs_of_pairing <;> assumption)
