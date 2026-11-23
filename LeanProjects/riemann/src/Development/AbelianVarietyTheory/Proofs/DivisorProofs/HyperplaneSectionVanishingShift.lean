import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Formalism.HarderNarasimhan.StatementPl

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore

theorem vanishFrom_cut {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (F : Y.Modules) (t : L.Sec)
    [Mono (GlobalTheory.cutHom F hL t)] {j₀ : ℤ} (h : VanishFrom L F j₀) :
    VanishFrom L (GlobalTheory.cut F hL t) (j₀ + 1) := by
  intro j hj q hq
  have hS := Twist.shortExact_map (Twist.isLB_lbZPow hL j) (shortExact_cutComplex F hL t)
  have e := Twist.twistZAddIso F hL (show (-1 : ℤ) + j = j - 1 by ring)
  have h₁ := h (j - 1) (by omega) (q + 1) q.succ_pos
  exact cohOn.subsingleton₃ hS ⊤ q (h j (by omega) q hq)
    (cohOn.mapIso ℤ ⊤ (q + 1) e).injective.subsingleton

theorem vanishFrom_cut_and_hdim : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k Y) → ∀ (L : LB Y) (hL : L.IsLB) (F : Y.Modules) [IsFiniteQC F] (t : L.Sec) [Mono (GlobalTheory.cutHom F hL t)] (j₀ : ℤ), VanishFrom L F j₀ → VanishFrom L (GlobalTheory.cut F hL t) (j₀ + 1) ∧ ∀ j : ℤ, j₀ + 1 ≤ j → GlobalTheory.hdim k (GlobalTheory.twistZ F L j) 0 = GlobalTheory.hdim k (GlobalTheory.twistZ F L (j - 1)) 0 + GlobalTheory.hdim k (GlobalTheory.twistZ (GlobalTheory.cut F hL t) L j) 0 := by
  intro k _ Y _ hY L hL F _ t _ j₀ h
  have hc := vanishFrom_cut hL F t h
  refine ⟨hc, fun j hj => ?_⟩
  have hF := finiteCohTwists_of_isProjOver (algebraMap_eq_strHom k Y) F hY
  have hj' := Twist.isLB_lbZPow hL j
  have e := Twist.twistZAddIso F hL (show (-1 : ℤ) + j = j - 1 by ring)
  have key : chi k (GlobalTheory.twistZ F L j) =
      chi k (GlobalTheory.twistZ (GlobalTheory.twistZ F L (-1)) L j) + chi k (GlobalTheory.twistZ (GlobalTheory.cut F hL t) L j) :=
    have := chi_twist_shortExact (shortExact_cutComplex F hL t) hj'
      (hF.twist (Twist.isLB_lbZPow hL (-1)) _ hj') (hF.cut hL t _ hj')
    this
  have e₁ := (chi_congr k e).trans (chi_eq_hdim_zero k (h (j - 1) (by omega)))
  have e₂ := chi_eq_hdim_zero k (h j (by omega))
  have e₃ := chi_eq_hdim_zero k (hc j hj)
  exact Int.natCast_inj.1 (e₂.symm.trans (key.trans
    ((congrArg₂ (· + ·) e₁ e₃).trans (Nat.cast_add _ _).symm)))

end GlobalTheory.HSCore
