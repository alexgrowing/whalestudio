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

namespace GlobalTheory.GroupBplus.Closed

theorem pairing_tau_eq_smul_eps : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {t : SAB H (Sp k)} {p : ℕ} [Fact p.Prime] {GG : PDivGroup p k} (tw : GG.TorsionTower t.G) (I : GeomTate Dw t), ∀ φ : GG ⟶ GG.dual, (∀ (x y : Dw.La) (n : ℕ), muRoot (pairing GG k (tau tw I x) (tateMap GG GG.dual k φ (tau tw I y))) n = ((I.ζ (p ^ n) ^ Dw.EF x y : kˣ) : k)) → ∀ x y : Dw.La, pairing GG k (tau tw I x) (tateMap GG GG.dual k φ (tau tw I y)) = ((Dw.EF x y : ℤ) : ℤ_[p]) • eps p I := by
  intro E _ _ _ H Dw k _ _ _ t p _ GG tw I φ h x y
  refine muRoot_ext fun n => ?_
  rw [h x y n, muRoot_smul, muRoot_eps]
  have hx : (I.ζ (p ^ n)) ^ p ^ n = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]; exact (zeta_prim p I n).pow_eq_one)
  rw [← Units.val_pow_eq_pow_val]
  congr 1
  rw [← zpow_natCast, zpow_eq_zpow_emod _ (n := ((p ^ n : ℕ) : ℤ)) (by rw [zpow_natCast]; exact hx),
    zpow_eq_zpow_emod ((digit n ((Dw.EF x y : ℤ) : ℤ_[p]) : ℕ) : ℤ) (n := ((p ^ n : ℕ) : ℤ)) (by rw [zpow_natCast]; exact hx)]
  congr 1
  rw [← ZMod.intCast_eq_intCast_iff', Int.cast_natCast, cast_digit, map_intCast]

end GlobalTheory.GroupBplus.Closed
