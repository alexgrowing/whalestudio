import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.DfcHigh

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf.G5

variable {D : D7} {L : SizeData₂ D}

def lX (s : Scale) : ℝ := Real.log s.X' * (1 + Real.log s.X')

structure PrimeSumNumericFacts (D : D7) (L : SizeData₂ D) (K : Consts) (C bo : ℝ) : Prop where

  one_le_card_tops : (1 : ℝ) ≤ (D.host.TT.card : ℝ)

  n1 : c1 L C * (L.sc.X'' D.R.n + 2) ≤ L.sc.a / L.sc.x / 40

  n1' : cfl D L.sc C * (L.sc.X'' D.R.n + 2) ≤ L.sc.a / L.sc.x / 40

  n2 : Real.log 4 * L.sc.p0 D.R.k * c2 L C ≤ L.sc.a / L.sc.x / 40

  n3 : Real.log 4 * L.sc.X' * c3 L C bo ≤ 3 / 2 * (L.sc.a / L.sc.x)

  n4 : lX L.sc * c4 K L C ≤ L.sc.a / L.sc.x / 40

  n5 : 120 ≤ L.sc.x

  n7 : L.sc.x ^ (-2 + L.sc.eps) ≤ 1 / L.sc.x / 120

  n9 : (L.sc.X'' D.R.n * thS L + 2) * (Real.log (2 * L.sc.X'' D.R.n) * (thW D L.sc * L.sc.w'' D.R.n + L.Sc)) ≤
    L.sc.a / L.sc.x / 40

theorem first_constant_nonneg (L : SizeData₂ D) (C : ℝ) (hC : 0 ≤ C) : 0 ≤ c1 L C := by
  unfold c1 cG
  have := L.Sc_pos
  have := L.etaSz_pos
  have ha := sc_one_lt_a L.sc
  exact mul_nonneg (mul_nonneg hC (by linarith)) (Real.log_nonneg (by linarith))

theorem second_constant_nonneg (L : SizeData₂ D) (C : ℝ) (hC : 0 ≤ C) : 0 ≤ c2 L C := by
  unfold c2
  have hk := k_ge D
  have hx := sc_x_pos L.sc
  have ha := sc_one_lt_a L.sc
  have hlx := logx_nonneg L.sc
  have hb' := sc_b'_nonneg L.sc
  have h1 : 0 ≤ C * (rG L.sc : ℝ) * L.sc.b' * Real.log L.sc.x :=
    mul_nonneg (mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) hb') hlx
  have h2 : 0 ≤ C * Real.log L.sc.x * (L.sc.a * ((((D.R.k : ℝ) * L.sc.x ^ Scale.A) ^ 4)⁻¹)) :=
    mul_nonneg (mul_nonneg hC hlx) (mul_nonneg (by linarith) (by positivity))
  linarith

theorem fourth_constant_nonneg (K : Consts) (hK : 0 ≤ K.La) (L : SizeData₂ D) (C : ℝ) (hC : 0 ≤ C) : 0 ≤ c4 K L C := by
  unfold c4
  have hk := k_ge D
  have ha := sc_one_lt_a L.sc
  have hLa := La_nonneg K hK L.sc
  have hP0 := p0_pos D L.sc
  exact mul_nonneg (mul_nonneg hC (logx_nonneg _))
    (add_nonneg (div_nonneg (mul_nonneg hLa (by linarith)) (by linarith)) (div_nonneg (by linarith) hP0.le))

theorem cfl_nonneg (D : D7) (s : Scale) (C : ℝ) (hC : 0 ≤ C) : 0 ≤ cfl D s C := by
  unfold cfl
  have hla : 0 ≤ Real.log s.a := Real.log_nonneg (sc_one_lt_a s).le
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) (add_nonneg (mul_nonneg (by positivity) hla) (by positivity))

theorem one_le_X' (s : Scale) : 1 ≤ s.X' := by
  unfold Scale.X'; exact Real.one_le_exp (Real.rpow_nonneg (sc_x_pos s).le _)

structure Sets (X : Inst D L) (K : Consts) (A3 A4 PS : Finset ℕ) (badf : ℕ → ℝ) : Prop where
  hA3 : ∀ p : ℕ, p.Prime → IsResidueClassZero D p → (p : ℝ) < L.sc.X' →
      (addOrderOf (hP D p) : ℝ) < L.sc.x ^ (L.sc.eps / 4) → p ∈ A3
  hA4 : ∀ p : ℕ, p.Prime → (p : ℝ) < L.sc.X' → InBand D K L.sc p → p ∈ A4
  hPS : ∀ p, Cand D L K p → p ∈ PS
  hPSsub : PS ⊆ prB L.sc.X'
  hbad : ∀ p, Cand D L K p →
      ((D.host.TT \ D.host.TT.filter (fun t => X.bs (stepP D p) t ∈ goodReps X p)).card : ℝ) ≤ badf p
  hbad0 : ∀ p, 0 ≤ badf p
  s3 : ∑ p ∈ A3, Real.log p / p ≤ L.sc.x ^ (-hG L.sc + L.sc.eps)
  s4 : ∑ p ∈ A4, Real.log p / p ≤ L.sc.x ^ (-1 : ℝ)
  s2 : ∑ p ∈ PS, Real.log p / p * badf p ≤ (D.host.TT.card : ℝ) * L.sc.x ^ (-2 + L.sc.eps)

def E1 (X : Inst D L) (K : Consts) (C bo : ℝ) (a b : HH D → ℤ) (A3 A4 PS : Finset ℕ) (badf : ℕ → ℝ) (p : ℕ) : ℝ :=
  (if p ∈ prB (L.sc.X'' D.R.n + 1) then (1 : ℝ) else 0) *
      ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * c1 L C + (D.R.m : ℝ) * cfl D L.sc C) +
  (if p ∈ prB (L.sc.p0 D.R.k) then Real.log p else 0) * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * c2 L C) +
  (if p ∈ prB L.sc.X' then Real.log p else 0) * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * c3 L C bo) +
  (if p ∈ prB L.sc.X' then Real.log p / p else 0) * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * c4 K L C) +
  (if p ∈ A3 then Real.log p / p else 0) * (3 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a) +
  (if p ∈ A4 then Real.log p / p else 0) * (3 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a) +
  (if p ∈ PS then Real.log p / p * badf p else 0) * (3 * (D.R.m : ℝ) * L.sc.a) +
  (if p ∈ candF D L K then Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p) else 0) *
      (4 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a)

theorem low_le (X : Inst D L) (K : Consts) (hK : K.Nonneg) (P : ParameterChoice' D L) (C bo : ℝ) (hC : 0 ≤ C) (hbo : 0 ≤ bo)
    {a b : HH D → ℤ} (h : InWin L a b) (hG : GainBoundAt X K C bo a b)
    (hSig : ∀ p, Cand D L K p → 0 ≤ Sig X K a b p)
    {A3 A4 PS : Finset ℕ} {badf : ℕ → ℝ} (T : Sets X K A3 A4 PS badf)
    (p : ℕ) (hp : p.Prime) (hc0 : IsResidueClassZero D p) (hpX : (p : ℝ) ≤ L.sc.X'' D.R.n) :
    Real.log p * max 0 (Dfc X K a b p) ≤ E1 X K C bo a b A3 A4 PS badf p := by
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have ha := sc_one_lt_a L.sc
  have hm : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hN : (0 : ℝ) ≤ (D.host.TT.card : ℝ) := Nat.cast_nonneg _
  obtain ⟨hlo0, hlo⟩ := lo_bounds K hK.1 L C bo hC hbo p hp hc0
  obtain ⟨hfl0, hfl⟩ := fl_bounds D L.sc C hC p hp
  have hio := io_le X K hK P h hSig p
  have hsd := sdiff_le X K hSig A3 A4 PS badf T.hA3 T.hA4 T.hPS T.hbad T.hbad0 p hp hc0
  have hd := dfc_le P X K C bo h hG p hp hc0 hpX hlo0
  have m1 : p ∈ prB (L.sc.X'' D.R.n + 1) := mem_prB.2 ⟨hp, by linarith⟩
  have hsd0 : 0 ≤ Real.log p / p * ((D.host.TT \ TTP X K a b p).card : ℝ) :=
    mul_nonneg (lp_nonneg p) (Nat.cast_nonneg _)
  have hiob : 0 ≤ (if p ∈ candF D L K then Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p) else 0) *
        (((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a) := by
    split_ifs with hc
    · have := hSig p (cand_of_mem hc)
      have := dropI_nonneg X K a b p
      have := lp_nonneg p
      positivity
    · simp
  have k1 := mul_le_mul_of_nonneg_left hsd (by positivity : (0 : ℝ) ≤ 3 * (D.R.m : ℝ) * L.sc.a)
  have k2 := mul_le_mul_of_nonneg_left hlo (mul_nonneg hm hN)
  have k3 := mul_le_mul_of_nonneg_left hfl hm
  have k4 := mul_le_mul_of_nonneg_left hd hl
  have k10 : 0 ≤ 3 * (D.R.m : ℝ) * L.sc.a * (Real.log p / p * ((D.host.TT \ TTP X K a b p).card : ℝ)) :=
    mul_nonneg (by positivity) hsd0
  have k20 : 0 ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) * (Real.log p * lo K L C bo p) :=
    mul_nonneg (mul_nonneg hm hN) (mul_nonneg hl hlo0)
  have k30 : 0 ≤ (D.R.m : ℝ) * (Real.log p * fl D L.sc C p) := mul_nonneg hm (mul_nonneg hl hfl0)
  have e : Real.log p * ((D.R.m : ℝ) * (((D.host.TT \ TTP X K a b p).card : ℝ) * (3 * L.sc.a / p)) +
      (D.R.m : ℝ) * ((D.host.TT.card : ℝ) * lo K L C bo p) + (D.R.m : ℝ) * fl D L.sc C p + ioP X K a b p) =
      3 * (D.R.m : ℝ) * L.sc.a * (Real.log p / p * ((D.host.TT \ TTP X K a b p).card : ℝ)) +
      (D.R.m : ℝ) * (D.host.TT.card : ℝ) * (Real.log p * lo K L C bo p) +
      (D.R.m : ℝ) * (Real.log p * fl D L.sc C p) + Real.log p * ioP X K a b p := by ring
  rw [e] at k4
  rw [mul_max_of_nonneg _ _ hl, mul_zero]
  unfold E1
  rw [if_pos m1]
  apply max_le <;> linarith

end Formalism.MainNotions.AuxBlock8.Pf.G5

end
