import Mathlib
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExists
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PtsIntZero

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar.Top

def RootFlatOnHodge : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H)
    (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
    (bad : Finset ℕ) (M : RootModel (CMType H) (D.p + D.q))
    (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys)
    (o : RootOrigin Y bad M Fx),
    IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → (∀ r : ℕ, r ∈ bad ↔ r.Prime ∧ (r : ℤ) ∣ 2 * discr E * l.M') →
      o.𝔐.OmVB → ∀ τ, ∃ R : RootFlat M τ, NearRecord (D.p + D.q) bad (hostRd E) (hostLval H) R.ht

namespace OnHodge

section Tower

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {Xo : ∀ l : Level H, Moduli D l} {l : Level H} {c : Coeff l} {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)}

theorem hostRd_eq (E : Type) [Field E] [NumberField E] : hostRd E = rootDiscr E := by
  simp [hostRd, rootDiscr_def]

theorem S_two {T : RootTower (CMType H) (D.p + D.q)} (o : TowerOrigin Y T) : o.S 2 = T.bad := by
  ext r
  rw [o.S_iff, RootTower.InS]
  refine ⟨fun h => h.2.elim (fun h2 => ?_) id, fun h => ⟨((o.bad_iff r).1 h).1, Or.inr h⟩⟩
  obtain rfl : r = 2 := le_antisymm h2 h.1.two_le
  exact T.two_mem

theorem tower (h : RootFlatOnHodge) [IsAbelianGalois ℚ E] (hY : IsGlobal Xo l c Y)
    {T : RootTower (CMType H) (D.p + D.q)} (hT : IsTowerOf Y T) (a : T.Comp) (τ : CMType H) :
    ∃ R : RootFlat (T.M 2 a) τ, NearRecord (D.p + D.q) T.bad (hostRd E) (hostLval H) R.ht := by
  obtain ⟨o, ho⟩ := hT
  have h1 := T.j_pos
  have h2 := T.j_lt
  have h3 := o.j_eq
  rw [← S_two o]
  exact h E H D Xo l c Y (o.S 2) (T.M 2 a) (o.Sys a) (o.Fx a) (o.Or 2 a) hY (by omega) (by omega)
    (fun r => by rw [S_two o]; exact o.bad_iff r) (ho 2 a) τ

end Tower

theorem const_le : Real.eulerMascheroniConstant + Real.log (2 * Real.pi) + 2 * Real.log 2 ≤ 2 * Real.log 7 := by
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hπ := Real.pi_lt_d4
  have hπ0 := Real.pi_pos
  have he : Real.exp (2 / 3) ≤ 1.9496 := by
    have h3 : Real.exp (2 / 3) ^ 3 = Real.exp 1 ^ 2 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
    have h1 := Real.exp_one_lt_d9
    have h0 := Real.exp_pos 1
    refine le_of_pow_le_pow_left₀ three_ne_zero (by norm_num) ?_
    rw [h3]; nlinarith
  have h : Real.log (Real.exp (2 / 3) * (2 * Real.pi) * 2 ^ 2) ≤ Real.log (7 ^ 2) :=
    Real.log_le_log (by positivity) (by nlinarith [Real.exp_pos (2 / 3)])
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_exp,
    Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

theorem value_bound (p q : ℕ) (lK l L : ℝ) (h7 : Real.log 7 / 2 ≤ lK) (hl : lK ≤ l) :
    |((p : ℝ) - q) / 2 * (Real.eulerMascheroniConstant + Real.log (2 * Real.pi) - l - L) + q * (2 * lK - l)| +
      ((p + q : ℕ) : ℝ) * Real.log 2 ≤ ((p + q : ℕ) : ℝ) * (3 / 2 * l + |L| / 2) := by
  have hc := const_le
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h4 : 2 * Real.log 2 ≤ Real.log (2 * Real.pi) := by
    have : Real.log (2 ^ 2) ≤ Real.log (2 * Real.pi) :=
      Real.log_le_log (by norm_num) (by linarith [Real.pi_gt_three])
    rw [Real.log_pow] at this
    exact_mod_cast this
  have hL := le_abs_self L
  have hL' := neg_abs_le L
  have hp : (0 : ℝ) ≤ p := p.cast_nonneg
  have hq : (0 : ℝ) ≤ q := q.cast_nonneg
  set c := Real.eulerMascheroniConstant + Real.log (2 * Real.pi) with hcdef
  set b := 3 / 2 * l + |L| / 2 - Real.log 2 with hb
  have a1 : 0 ≤ b - (c - l - L) / 2 := by linarith
  have a2 : 0 ≤ b + (c - l - L) / 2 := by linarith
  have a3 : 0 ≤ b - (-(c - l - L) / 2 + 2 * lK - l) := by linarith
  have a4 : 0 ≤ b + (-(c - l - L) / 2 + 2 * lK - l) := by linarith
  have : |((p : ℝ) - q) / 2 * (c - l - L) + q * (2 * lK - l)| ≤ (p + q) * b :=
    abs_le.2 ⟨by nlinarith [mul_nonneg hp a2, mul_nonneg hq a4], by nlinarith [mul_nonneg hp a1, mul_nonneg hq a3]⟩
  push_cast
  nlinarith

end OnHodge

end GlobalTheory.CompanionTheory.Ar.Flat
