import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingFormulaAllPoints
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
theorem _root_.GlobalTheory.T.weil_pairing_formula_all_points : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {t : SAB H (Sp k)} {p : ℕ} [Fact p.Prime] {GG : PDivGroup p k} (tw : GG.TorsionTower t.G) (I : GeomTate Dw t), ∀ φ : GG ⟶ GG.dual, (∀ (x y : Dw.La) (n : ℕ), muRoot (pairing GG k (tau tw I x) (tateMap GG GG.dual k φ (tau tw I y))) n = ((I.ζ (p ^ n) ^ Dw.EF x y : kˣ) : k)) → ∀ x y : Dw.La, pairing GG k (tau tw I x) (tateMap GG GG.dual k φ (tau tw I y)) = ((Dw.EF x y : ℤ) : ℤ_[p]) • eps p I := by
  first | exact @GlobalTheory.GroupBplus.Closed.pairing_tau_eq_smul_eps | exact GlobalTheory.GroupBplus.Closed.pairing_tau_eq_smul_eps | (intros; apply GlobalTheory.GroupBplus.Closed.pairing_tau_eq_smul_eps <;> assumption)
