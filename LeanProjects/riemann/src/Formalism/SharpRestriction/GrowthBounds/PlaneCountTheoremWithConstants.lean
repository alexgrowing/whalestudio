import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments
import Formalism.SharpRestriction.GrowthBounds.CountingStatementReduction
import Formalism.SharpRestriction.GrowthBounds.PathWeight
import Formalism.SharpRestriction.GrowthBounds.PolBridge
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.CMFieldLemmas
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.Joints
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.Lemmas
import Formalism.SharpRestriction.GrowthBounds.GLWeightTheory
import Formalism.SharpRestriction.GrowthBounds.TopChoiceBounds
import Formalism.SharpRestriction.GrowthBounds.CornerGLContinuity
import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Formalism.SharpRestriction.GrowthBounds.ProofLW
import Formalism.SharpRestriction.GrowthBounds.SelectionLemmas
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSk
import Formalism.SharpRestriction.GrowthBounds.ProjectionOfIsotypicDecomposition
import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeMapFractionField
import Formalism.LocalRingCardinality.HostCls
import Development.AutomorphicArithmetic.OrbitLabellings.EvenAddOrderOfHPOfPowLe
import Development.AutomorphicArithmetic.OrbitLabellings.GalEArithFrobEqIotaHP
import Development.AutomorphicArithmetic.PrimeDiscriminants.SplitLow
import Lemmata.GeneralBFactUpperBis.Imports

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions

namespace Formalism.MainNotions.G

variable {D : D7} {L : SizeData₂ D}

theorem sc_x_pos (s : Scale) : 0 < s.x := lt_trans one_pos s.one_lt_alt

theorem sc_one_le_b (s : Scale) : 1 ≤ s.b := by
  unfold Scale.b Scale.L
  exact Real.one_le_exp (Real.rpow_nonneg (sc_x_pos s).le _)

theorem sc_one_lt_a (s : Scale) : 1 < s.a := by
  unfold Scale.a
  nlinarith [s.one_lt_alt, sc_one_le_b s]

theorem sc_b'_nonneg (s : Scale) : 0 ≤ s.b' := by
  unfold Scale.b' Scale.X'
  exact div_nonneg (le_trans zero_le_one (sc_one_lt_a s).le) (Real.exp_pos _).le

theorem sc_w''_nonneg (s : Scale) (n : ℕ) : 0 ≤ s.w'' n := by
  unfold Scale.w''
  exact div_nonneg (sc_b'_nonneg s) (mul_nonneg (sc_x_pos s).le (Nat.cast_nonneg n))

theorem sc_delta1_pos (s : Scale) : 0 < s.delta1 := by
  unfold Scale.delta1
  exact Real.rpow_pos_of_pos (sc_x_pos s) _

theorem rG_eq (s : Scale) : rG s = Formalism.MainNotions.rG s.eps := rfl

theorem exponent_ge_least_exponent (L : SizeData₂ D) (p : ℕ) (hp : p.Prime) (h0 : (p : ℝ) < L.sc.p0 D.R.k) :
    leastPowerExponent L p ≤ L1 D L.sc p := by
  have hx := sc_x_pos L.sc
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := lt_trans one_pos hp1
  set y : ℝ := L.sc.x ^ Scale.A with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow L.sc.one_lt_alt.le (by unfold Scale.A; norm_num)
  have hy3 : L.sc.x ^ (3 * Scale.A) = y ^ 3 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    push_cast
    ring
  have hk : (1 : ℝ) ≤ (D.R.k : ℝ) := by
    rcases Nat.eq_zero_or_pos D.R.k with h | h
    · exfalso
      unfold Scale.p0 at h0
      rw [h] at h0
      simp at h0
      linarith
    · exact_mod_cast h
  have hp0' : (p : ℝ) < (D.R.k : ℝ) ^ 2 * y := h0
  have hz1 : 1 ≤ (D.R.k : ℝ) ^ 2 * y ^ 3 := by
    have h1 : 1 ≤ (D.R.k : ℝ) ^ 2 := one_le_pow₀ hk
    have h2 : 1 ≤ y ^ 3 := one_le_pow₀ hy1
    nlinarith
  have hlog : Real.logb p ((D.R.k : ℝ) ^ 2 * y ^ 3) + 1 ≤ Real.logb p (((D.R.k : ℝ) * y) ^ 4) := by
    have h1 : Real.logb p ((D.R.k : ℝ) ^ 2 * y ^ 3) + 1 = Real.logb p ((D.R.k : ℝ) ^ 2 * y ^ 3 * p) := by
      rw [Real.logb_mul (by positivity) hp0.ne', Real.logb_self_eq_one hp1]
    rw [h1]
    apply Real.logb_le_logb_of_le hp1 (by positivity)
    have h2 : ((D.R.k : ℝ) * y) ^ 4 = (D.R.k : ℝ) ^ 2 * y ^ 3 * ((D.R.k : ℝ) ^ 2 * y) := by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left hp0'.le (by positivity)
  unfold leastPowerExponent L1
  rw [hy3, ← Nat.ceil_add_one (Real.logb_nonneg hp1 hz1)]
  exact Nat.ceil_mono hlog

theorem lo_le_loG (K : Consts) (L : SizeData₂ D) (hK : 0 ≤ K.La) (hLa : La K L.sc = L.LaG) (C bo : ℝ) (p : ℕ)
    (hp : p.Prime) : lo K L C bo p ≤ loG L (4 * |C| + 1) bo p := by
  have hx := sc_x_pos L.sc
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := lt_trans one_pos hp1
  have habs := abs_nonneg C
  have hle := le_abs_self C
  set C' : ℝ := 4 * |C| + 1 with hC'
  have hCC' : C ≤ C' := by linarith
  have hC'1 : 1 ≤ C' := by linarith
  have hC'0 : 0 ≤ C' := by linarith
  have ha := sc_one_lt_a L.sc
  have hlg : 0 ≤ Real.logb p (2 * L.sc.a) := Real.logb_nonneg hp1 (by linarith)
  have hlx : 0 ≤ Real.log L.sc.x := Real.log_nonneg L.sc.one_lt_alt.le
  have hb' := sc_b'_nonneg L.sc
  have hw := sc_w''_nonneg L.sc D.R.n
  have hd := sc_delta1_pos L.sc
  have hSc := L.Sc_pos
  have hη := L.etaSz_pos
  have hk : (0 : ℝ) ≤ (D.R.k : ℝ) := Nat.cast_nonneg _
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hLaG : 0 ≤ L.LaG := by
    rw [← hLa]
    unfold La
    exact mul_nonneg (mul_nonneg hK (by positivity)) (Real.log_nonneg ha.le)

  have hcp : C * (cG L + L.etaSz) * Real.logb p (2 * L.sc.a) ≤
      C' * (L.Sc + D.R.k + L.etaSz) * Real.logb p (2 * L.sc.a) := by
    apply mul_le_mul_of_nonneg_right _ hlg
    unfold cG
    have h1 : C * (4 * L.Sc + L.etaSz) ≤ |C| * (4 * L.Sc + L.etaSz) :=
      mul_le_mul_of_nonneg_right hle (by linarith)
    have h2 := mul_nonneg habs hη.le
    have h3 := mul_nonneg habs hk
    have h4 := mul_nonneg habs hSc.le
    rw [hC']
    nlinarith

  have hpr : (if IsResidueClassZero D p then
      (if (p : ℝ) < L.sc.p0 D.R.k then C * (rG L.sc : ℝ) * L.sc.b' * Real.log L.sc.x
       else if (p : ℝ) < L.sc.X' then
         L.sc.b' / L.sc.x + L.etaSz + C * L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1 + bo
       else 0) else 0) ≤
      (if D.host.cls p = PrimeClass.inertClass then
      (if (p : ℝ) < L.sc.p0 D.R.k then C' * (Formalism.MainNotions.rG L.sc.eps : ℝ) * L.sc.b' * Real.log L.sc.x
       else if (p : ℝ) < L.sc.X' then
         C' * (L.sc.b' / L.sc.x + L.etaSz + L.Sc + (L.sc.w'' D.R.n + D.R.t) * Real.log L.sc.x / L.sc.delta1) + bo
       else 0) else 0) := by
    by_cases hc : D.host.cls p = PrimeClass.inertClass
    · rw [if_pos hc, if_pos hc]
      by_cases h0 : (p : ℝ) < L.sc.p0 D.R.k
      · rw [if_pos h0, if_pos h0, ← rG_eq]
        have h1 : 0 ≤ (rG L.sc : ℝ) * L.sc.b' * Real.log L.sc.x :=
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hb') hlx
        nlinarith [mul_nonneg (sub_nonneg.2 hCC') h1]
      · rw [if_neg h0, if_neg h0]
        by_cases h1 : (p : ℝ) < L.sc.X'
        · rw [if_pos h1, if_pos h1]
          have e1 : 0 ≤ L.sc.b' / L.sc.x := div_nonneg hb' hx.le
          have e2 : 0 ≤ L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1 := div_nonneg (mul_nonneg hw hlx) hd.le
          have e3 : 0 ≤ (D.R.t : ℝ) * Real.log L.sc.x / L.sc.delta1 := div_nonneg (mul_nonneg ht hlx) hd.le
          have e4 : C * L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1 =
              C * (L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1) := by ring
          have e5 : (L.sc.w'' D.R.n + D.R.t) * Real.log L.sc.x / L.sc.delta1 =
              L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1 + (D.R.t : ℝ) * Real.log L.sc.x / L.sc.delta1 := by
            ring
          rw [e4, e5]
          nlinarith [mul_nonneg (sub_nonneg.2 hCC') e2, mul_nonneg (sub_nonneg.2 hC'1) e1,
            mul_nonneg (sub_nonneg.2 hC'1) hη.le, mul_nonneg hC'0 hSc.le, mul_nonneg hC'0 e3]
        · rw [if_neg h1, if_neg h1]
    · rw [if_neg hc, if_neg hc]

  have hor : (if IsResidueClassZero D p ∧ (p : ℝ) < L.sc.X' then
      C * Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) +
        (if (p : ℝ) < L.sc.p0 D.R.k then L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ)) else L.sc.a / (p : ℝ) ^ 2))
      else 0) ≤
      (if D.host.cls p = PrimeClass.inertClass ∧ (p : ℝ) < L.sc.X' then
      C' * Real.log L.sc.x * (L.LaG * L.sc.a / ((p : ℝ) * D.R.k) +
        (if (p : ℝ) < L.sc.p0 D.R.k then L.sc.a * (p : ℝ) ^ (-(leastPowerExponent L p : ℝ)) else L.sc.a / (p : ℝ) ^ 2))
      else 0) := by
    by_cases hc : D.host.cls p = PrimeClass.inertClass ∧ (p : ℝ) < L.sc.X'
    · rw [if_pos hc, if_pos hc, hLa]
      have e1 : 0 ≤ L.LaG * L.sc.a / ((p : ℝ) * D.R.k) :=
        div_nonneg (mul_nonneg hLaG (by linarith)) (mul_nonneg hp0.le hk)
      have key : ∀ Z Z' : ℝ, 0 ≤ Z → Z ≤ Z' →
          C * Real.log L.sc.x * (L.LaG * L.sc.a / ((p : ℝ) * D.R.k) + Z) ≤
            C' * Real.log L.sc.x * (L.LaG * L.sc.a / ((p : ℝ) * D.R.k) + Z') := by
        intro Z Z' hZ hZZ
        exact mul_le_mul (mul_le_mul_of_nonneg_right hCC' hlx) (by linarith) (by linarith)
          (mul_nonneg hC'0 hlx)
      by_cases h0 : (p : ℝ) < L.sc.p0 D.R.k
      · rw [if_pos h0, if_pos h0]
        apply key
        · exact mul_nonneg (by linarith) (Real.rpow_nonneg hp0.le _)
        · apply mul_le_mul_of_nonneg_left _ (by linarith)
          apply Real.rpow_le_rpow_of_exponent_le hp1.le
          have := exponent_ge_least_exponent L p hp h0
          have h2 : (leastPowerExponent L p : ℝ) ≤ (L1 D L.sc p : ℝ) := by exact_mod_cast this
          linarith
      · rw [if_neg h0, if_neg h0]
        exact key _ _ (div_nonneg (by linarith) (by positivity)) le_rfl
    · rw [if_neg hc, if_neg hc]
  unfold lo loG
  exact add_le_add (add_le_add hcp hpr) hor

theorem fl_le_flG (L : SizeData₂ D) (C : ℝ) (p : ℕ) (hp : p.Prime) :
    fl D L.sc C p ≤ flG L (4 * |C| + 1) p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlg : 0 ≤ Real.logb p L.sc.a := Real.logb_nonneg hp1 (sc_one_lt_a L.sc).le
  have hCC' : C ≤ 4 * |C| + 1 := by linarith [abs_nonneg C, le_abs_self C]
  have hf : (0 : ℝ) ≤ (D.R.f : ℝ) := Nat.cast_nonneg _
  unfold fl flG Nm
  have e1 : 0 ≤ (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * Real.logb p L.sc.a :=
    mul_nonneg (mul_nonneg hf (by positivity)) hlg
  have e2 : 0 ≤ (D.R.f : ℝ) * Real.logb p L.sc.a ^ 2 := mul_nonneg hf (by positivity)
  nlinarith [mul_nonneg (sub_nonneg.2 hCC') e1, mul_nonneg (sub_nonneg.2 hCC') e2]

theorem aL_top (L : SizeData₂ D) (t : D.host.TT) : aL L (t : HH D) = L.aT t := by
  unfold aL
  rw [dif_pos t.2]

theorem ask_eq_askP (X : Inst D L) (p : ℕ) (hp : p.Prime)
    (hw : ∀ j (t : D.host.TT) e, L.wPart j t p e = fill X (bL L) j (partner D p t e)) (j : ℕ) (t : D.host.TT) :
    L.vonMangoldtClassSum j t p = askP X (aL L) (bL L) p j (t : HH D) := by
  unfold SizeData₂.vonMangoldtClassSum askP
  rw [tsum_eq_sum (s := Finset.range (Nat.log p (L.aT t).toNat + 2))]
  · apply Finset.sum_congr rfl
    intro i _
    rw [aL_top, hw]
  · intro i hi
    rw [Finset.mem_range, not_lt] at hi
    by_cases ho : Odd i
    · rw [if_pos ho, aL_top, ← hw]
      apply max_eq_left
      have h1 : (L.aT t).toNat < p ^ i :=
        lt_of_lt_of_le (Nat.lt_pow_succ_log_self hp.one_lt _) (Nat.pow_le_pow_right hp.pos (by omega))
      have h2 : (L.aT t : ℝ) ≤ ((L.aT t).toNat : ℝ) := by exact_mod_cast Int.self_le_toNat (L.aT t)
      have h3 : (((L.aT t).toNat : ℕ) : ℝ) < (p : ℝ) ^ i := by exact_mod_cast h1
      have h4 : (0 : ℝ) < (p : ℝ) ^ i := by have := hp.pos; positivity
      have h5 : (L.aT t : ℝ) / (p : ℝ) ^ i < 1 := by rw [div_lt_one h4]; linarith
      have := L.wPart_ge j t p i
      linarith
    · rw [if_neg ho]

theorem vUnit_pos {p : ℕ} (G : GAtP p) (v : Fin G.P.nV) : 0 < vUnit G := by
  have S := G.P.setting v
  have hinjW : Function.Injective (algebraMap (G.P.W v) (G.P.Qq v)) := by
    have := S.frac_alt
    exact IsFractionRing.injective _ _
  have hinjO : Function.Injective (algebraMap G.O G.Kf) := by
    have := S.frac_O
    exact IsFractionRing.injective _ _
  have hinj : Function.Injective (G.P.j v) := by
    intro a b hab
    apply hinjW
    apply (G.P.ι v).injective
    rw [S.ι_comp, S.ι_comp, hab]
  have hloc : IsLocalHom (G.P.j v) := S.finite.to_isIntegral.isLocalHom hinj
  have hjp : G.P.j v (p : G.P.W v) = (p : G.O) := map_natCast _ _
  have hne : (p : G.O) ≠ 0 := by
    rw [← hjp]
    intro h
    exact S.p_unif.ne_zero (hinj (by rw [h, map_zero]))
  have hnu : ¬ IsUnit (p : G.O) := by
    rw [← hjp]
    intro h
    exact S.p_unif.not_isUnit (hloc.map_nonunit _ h)
  unfold vUnit
  have : 0 < (IsDiscreteValuationRing.addVal G.O (p : G.O)).toNat := by
    apply ENat.toNat_pos
    · intro h
      exact hnu (IsDiscreteValuationRing.addVal_eq_zero_iff.1 h)
    · intro h
      exact hne (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
  exact_mod_cast this

theorem X'_le_X'' (s : Scale) (n : ℕ) (hn : 1 ≤ n) : s.X' ≤ s.X'' n := by
  have hx := sc_x_pos s
  have ha : 0 < s.a := lt_trans one_pos (sc_one_lt_a s)
  have hX : 0 < s.X' := by unfold Scale.X'; exact Real.exp_pos _
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h : s.X'' n = s.X' * (s.x * n) := by
    unfold Scale.X'' Scale.w'' Scale.b'
    field_simp
  rw [h]
  have : 1 ≤ s.x * n := by nlinarith [s.one_lt_alt]
  nlinarith

theorem cand_of_VV_ne (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) (h : VV X K a b p ≠ ∅) :
    Cand D L K p := by
  unfold VV at h
  by_contra hc
  exact h (if_neg (fun hh => hc hh.1))

def ServedGIdx (X : Inst D L) (K : Consts) : Prop :=
  ∀ (u : D.what₂.Word) (p : ℕ), VV X K (aL L) (bL L) p ≠ ∅ → p ≠ (D.mem u).A.T → GIdx D.host (D.mem u).A.T p

def SvBound (X : Inst D L) (K : Consts) : Prop :=
  ∀ p, ∀ t0 ∈ VV X K (aL L) (bL L) p,
    Sv X K (aL L) (bL L) p t0 ≤ 2 * (D.R.m : ℝ) * (Nv X p t0 : ℝ) * L.sc.a / p

def FrobNe (D : D7) : Prop := ∀ p : ℕ, p.Prime → IsResidueClassZero D p → HEv D p → HNeZero D.host p

def LevelPrimesNotClassZero (D : D7) : Prop := ∀ p ∈ D.host.levelPrimes, ¬ IsResidueClassZero D p

theorem servedGIdx_of (X : Inst D L) (K : Consts) (h4 : 4 ≤ ⌊L.sc.x ^ (L.sc.ez / 5)⌋₊) (hF : FrobNe D)
    (hLv : LevelPrimesNotClassZero D) : ServedGIdx X K := by
  intro u p hV hpT
  obtain ⟨hp, _, hc0, hord, _⟩ := cand_of_VV_ne X K _ _ _ hV
  refine ⟨hp, ?_, hc0, hF p hp hc0 (UpperTheory.even_addOrderOf_hP_of_pow_le.2 D L p hord), fun h => hLv p h hc0, ?_⟩
  · by_contra h
    have hp4 : p ≤ D.host.splitBound := le_trans (by omega) (le_trans h4 L.split_tie)
    have hc0' : primeClass D.host.toHostRaw p = PrimeClass.inertClass := hc0
    obtain ⟨hs, -, -, hj, -⟩ := (primeClass_eq_inert_iff D.host.toHostRaw).1 hc0'
    have hne2 : p ≠ 2 := by
      rintro rfl
      exact hs D.host.two_mem_small
    exact hj (D.host.split_small p hp hne2 hp4)
  · exact fun h => hpT ((Nat.prime_dvd_prime_iff_eq hp (D.mem u).A.T_prime).1 h)

theorem Nm_le_Sc (P : ParameterChoice' D L) : (5 : ℝ) ≤ (D.R.k : ℝ) ∧ (D.R.N D.R.m : ℝ) ≤ L.Sc ∧ 100 ≤ L.Sc := by
  have hm : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast D.R.two_le_m
  have hk : (5 : ℝ) ≤ (D.R.k : ℝ) := by
    have := D.R.m_add_three_le_k
    have h2 := D.R.two_le_m
    exact_mod_cast (by omega : 5 ≤ D.R.k)
  have hNk : (D.R.k : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
    have : D.R.k ≤ D.R.N D.R.m := by unfold Ranks.N; omega
    exact_mod_cast this
  have h := P.Del_ge.2.2.2
  have hm10 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := one_le_pow₀ (by linarith)
  have hN0 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) := Nat.cast_nonneg _
  have hND : (D.R.N D.R.m : ℝ) ≤ (D.s.Del : ℝ) := by
    have := mul_le_mul_of_nonneg_left hm10 hN0
    linarith
  have hD : (5 : ℝ) ≤ (D.s.Del : ℝ) := by linarith
  have hkD : 5 * (D.s.Del : ℝ) ≤ (D.R.k : ℝ) * (D.s.Del : ℝ) := mul_le_mul_of_nonneg_right hk (by linarith)
  refine ⟨hk, ?_, ?_⟩ <;> rw [L.Sc_eq] <;> nlinarith

theorem kaJ_le (P : ParameterChoice' D L) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) : kaJ D j ≤ L.Sc := by
  obtain ⟨hk, hN, _⟩ := Nm_le_Sc P
  have hj2 : (j : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast (Finset.mem_Icc.1 hj).2
  have hNe : (D.R.N D.R.m : ℝ) = (D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) := by
    unfold Ranks.N; push_cast; ring
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) + 1 := by positivity
  have h1 := mul_le_mul_of_nonneg_right hj2 ht
  unfold kaJ
  nlinarith

theorem w''_le (s : Scale) (n : ℕ) (hn : 1 ≤ n) : s.w'' n ≤ s.b' / s.x ∧ s.b' / s.x ≤ s.b' := by
  have hx := sc_x_pos s
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hb := sc_b'_nonneg s
  constructor
  · unfold Scale.w''
    apply div_le_div_of_nonneg_left hb hx
    nlinarith
  · exact div_le_self hb s.one_lt_alt.le

theorem two_b'_le_a (s : Scale) : 2 * s.b' ≤ s.a := by
  have hX : 2 ≤ s.X' := by
    unfold Scale.X'
    have h1 : 1 ≤ s.x ^ (s.eps / 3) := Real.one_le_rpow s.one_lt_alt.le (by have := s.eps_pos; positivity)
    have := Real.add_one_le_exp (s.x ^ (s.eps / 3))
    linarith
  have hb := sc_b'_nonneg s
  have h : s.b' * s.X' = s.a := by
    unfold Scale.b'
    exact div_mul_cancel₀ _ (by linarith)
  nlinarith

theorem fill_nonneg (X : Inst D L) (j : ℕ) (z : Bool × HH D) : 0 ≤ fill X (bL L) j z := by
  have hb := sc_b'_nonneg L.sc
  have hx := sc_x_pos L.sc
  unfold fill
  by_cases ht : z.1 = false ∧ z.2 ∈ D.host.TT
  · rw [if_pos ht]
    have h1 := (X.off_top j z ht).1
    have h2 : L.sc.b' ≤ (bL L z.2 : ℝ) := by
      unfold bL
      rw [dif_pos ht.2]
      exact L.bT_ge _
    have h3 : 0 ≤ L.sc.b' / L.sc.x := div_nonneg hb hx.le
    linarith
  · rw [if_neg ht]
    by_cases hth : IsThickPl D z
    · have := (X.off_thick j z hth).1
      have := sc_one_le_b L.sc
      linarith
    · have := (X.off_thin j z ⟨ht, hth⟩).1
      have := sc_w''_nonneg L.sc D.R.n
      linarith

theorem ceil_bound (S B R : ℝ) (hSB : S ≤ B) (h : (B = 0 ∧ R = 0) ∨ B + 1 ≤ R) : ((⌈S⌉ : ℤ) : ℝ) ≤ R := by
  rcases h with ⟨hB, hR⟩ | h
  · have h1 : ⌈S⌉ ≤ 0 := Int.ceil_le.2 (by rw [Int.cast_zero]; linarith)
    have h2 : ((⌈S⌉ : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h1
    linarith
  · have := Int.ceil_lt_add_one S
    linarith

theorem fin_arith (m N q : ℝ) (hm : 2 ≤ m) (hN : 1 ≤ N) (hq : 500 ≤ q) :
    m * (8 / 5 * (N * q)) + 1 ≤ 2 * (m * (N * q)) := by
  have h2 : 500 ≤ N * q := by nlinarith
  have h3 : 1000 ≤ m * (N * q) := by nlinarith
  linarith

theorem svBound_of (X : Inst D L) (K : Consts) (hK : K.Nonneg) (P : ParameterChoice' D L) : SvBound X K := by
  classical
  intro p t0 ht0
  obtain ⟨hp, hpX, -⟩ := cand_of_VV_ne X K _ _ _ (Finset.ne_empty_of_mem ht0)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hdl1, hdl2, hPr1, _⟩ := hK
  obtain ⟨hk, hN, hSc⟩ := Nm_le_Sc P
  have hn : 1 ≤ D.R.n := D.R.n_pos'
  obtain ⟨hw1, hw2⟩ := w''_le L.sc D.R.n hn
  have hkS := P.kS_le
  have hab := two_b'_le_a L.sc
  have hx := sc_x_pos L.sc
  have ha := sc_one_lt_a L.sc
  have hb' := sc_b'_nonneg L.sc
  have hw0 := sc_w''_nonneg L.sc D.R.n
  have hη := L.etaSz_pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hkSc : 5 * L.Sc ≤ (D.R.k : ℝ) * L.Sc := mul_le_mul_of_nonneg_right hk (by linarith)
  have hw500 : 500 ≤ L.sc.w'' D.R.n := by linarith
  have hlg : 0 ≤ Real.logb p (2 * L.sc.a) := Real.logb_nonneg hp1 (by linarith)
  have hNm0 : 0 ≤ Nm D := by unfold Nm; exact Nat.cast_nonneg _
  have hcG : 0 ≤ cG L := by unfold cG; linarith
  have hTT : ∀ s ∈ topsOn X p t0, s ∈ D.host.TT := fun s hs => (Finset.mem_filter.1 hs).1

  have hal : ∀ s ∈ topsOn X p t0, 0 ≤ al L (aL L) s ∧ al L (aL L) s ≤ 6 / 5 * L.sc.a := by
    intro s hs
    have h1 : aL L s = L.aT ⟨s, hTT s hs⟩ := by unfold aL; rw [dif_pos (hTT s hs)]
    obtain ⟨h2, h3⟩ := L.aT_win ⟨s, hTT s hs⟩
    have h4 : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a / 5 := by
      apply div_le_div_of_nonneg_left (by linarith) (by norm_num)
      have : 1 ≤ L.sc.x ^ (Scale.A / 2) := Real.one_le_rpow L.sc.one_lt_alt.le (by unfold Scale.A; norm_num)
      nlinarith
    unfold al cG
    rw [h1]
    constructor <;> linarith
  have hdl : 0 ≤ dl X K p t0 := by
    unfold dl
    have h1 : 0 ≤ K.dl1 * (nP D p : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a) :=
      mul_nonneg (mul_nonneg (mul_nonneg hdl1 (Nat.cast_nonneg _)) (by positivity)) hlg
    have h2 : 0 ≤ K.dl2 * (Nv X p t0 : ℝ) * Real.logb p (2 * L.sc.a) ^ 2 :=
      mul_nonneg (mul_nonneg hdl2 (Nat.cast_nonneg _)) (by positivity)
    linarith
  have hgU : ∀ j ∈ SizeData₂.lifts D,
      gU X K (aL L) (bL L) p j t0 ≤ gam p * ∑ s ∈ topsOn X p t0, al L (aL L) s := by
    intro j hj
    unfold gU
    refine le_trans (sub_le_self _ hdl) (sub_le_self _ ?_)
    apply Finset.sum_nonneg
    intro s hs
    apply tsum_nonneg
    intro e
    split_ifs
    · apply le_min
      · exact div_nonneg (hal s (Finset.mem_filter.1 hs).1).1 (by positivity)
      · unfold capU fillG cG
        have := fill_nonneg X j (partner D p s e)
        have := kaJ_le P j hj
        linarith
    · exact le_rfl
  have hbase : 0 ≤ L.sc.w'' D.R.n + L.etaSz + cG L + Nm D := by linarith
  have hPr : ∀ j ∈ SizeData₂.lifts D, 0 ≤ Pr X K (bL L) p j t0 := by
    intro j hj
    unfold Pr
    split_ifs with h0
    · apply add_nonneg
      · apply Finset.sum_nonneg
        intro s hs
        have hs' := hTT s (Finset.mem_filter.1 hs).1
        have h1 : fill X (bL L) j (false, s) = (bL L s : ℝ) + X.off j (false, s) := by
          unfold fill
          rw [if_pos ⟨rfl, hs'⟩]
        have h2 := (X.off_top j (false, s) ⟨rfl, hs'⟩).1
        have h3 := kaJ_le P j hj
        unfold fillG
        rw [h1]
        linarith
      · exact mul_nonneg (mul_nonneg hPr1 (Nat.cast_nonneg _)) hbase
    · exact mul_nonneg (Nat.cast_nonneg _)
        (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (mul_nonneg (Nat.cast_nonneg _) hbase))
  have hgam : 0 ≤ gam p ∧ gam p * L.sc.a ≤ 4 / 3 * (L.sc.a / p) := by
    have hp4 : (4 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
    have hd : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by linarith
    unfold gam
    refine ⟨div_nonneg hp0.le hd.le, ?_⟩
    have h1 : (p : ℝ) / ((p : ℝ) ^ 2 - 1) ≤ 4 / 3 * (1 / p) := by
      rw [div_le_iff₀ hd]
      field_simp
      nlinarith
    have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ L.sc.a)
    calc (p : ℝ) / ((p : ℝ) ^ 2 - 1) * L.sc.a ≤ 4 / 3 * (1 / p) * L.sc.a := h2
      _ = 4 / 3 * (L.sc.a / p) := by ring
  have hsum : ∑ s ∈ topsOn X p t0, al L (aL L) s ≤ (Nv X p t0 : ℝ) * (6 / 5 * L.sc.a) := by
    unfold Nv
    rw [← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ (fun s hs => (hal s hs).2)
  set q : ℝ := L.sc.a / p with hq
  have hq0 : L.sc.b' ≤ q := by
    have hX : 0 < L.sc.X' := by unfold Scale.X'; exact Real.exp_pos _
    rw [hq]
    unfold Scale.b'
    exact div_le_div_of_nonneg_left (by linarith) hp0 hpX.le
  have hterm : ∀ j ∈ SizeData₂.lifts D,
      max 0 (gU X K (aL L) (bL L) p j t0 - Pr X K (bL L) p j t0 - max (g0 X K (aL L) (bL L) p j t0) 0) ≤
        8 / 5 * ((Nv X p t0 : ℝ) * q) := by
    intro j hj
    have hNv : (0 : ℝ) ≤ (Nv X p t0 : ℝ) := Nat.cast_nonneg _
    have h1 := hgU j hj
    have h2 := hPr j hj
    have h3 : 0 ≤ max (g0 X K (aL L) (bL L) p j t0) 0 := le_max_right _ _
    have h4 := mul_le_mul_of_nonneg_left hsum hgam.1
    have h5 := mul_le_mul_of_nonneg_left hgam.2 hNv
    have h6 : 0 ≤ (Nv X p t0 : ℝ) * q := mul_nonneg hNv (by linarith)
    apply max_le (by linarith)
    nlinarith
  have htot : ∑ j ∈ SizeData₂.lifts D,
      max 0 (gU X K (aL L) (bL L) p j t0 - Pr X K (bL L) p j t0 - max (g0 X K (aL L) (bL L) p j t0) 0) ≤
        (D.R.m : ℝ) * (8 / 5 * ((Nv X p t0 : ℝ) * q)) := by
    have h := Finset.sum_le_card_nsmul _ _ _ hterm
    have hc : (SizeData₂.lifts D).card = D.R.m := by unfold SizeData₂.lifts; simp
    rw [hc, nsmul_eq_mul] at h
    exact h
  have hR : 2 * (D.R.m : ℝ) * (Nv X p t0 : ℝ) * L.sc.a / p = 2 * ((D.R.m : ℝ) * ((Nv X p t0 : ℝ) * q)) := by
    rw [hq]; ring
  rw [hR]
  unfold Sv
  apply ceil_bound _ _ _ htot
  rcases Nat.eq_zero_or_pos (Nv X p t0) with h0 | h0
  · left
    have h0' : (Nv X p t0 : ℝ) = 0 := by exact_mod_cast h0
    rw [h0']
    constructor <;> ring
  · right
    have hm : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast D.R.two_le_m
    have hNv : (1 : ℝ) ≤ (Nv X p t0 : ℝ) := by exact_mod_cast h0
    have hq500 : 500 ≤ q := by linarith
    exact fin_arith _ _ _ hm hNv hq500

def NuServed (X : Inst D L) (K : Consts) : Prop :=
  ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl), VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅ →
    D.what₂.places.resChar w ≠ (D.mem u).A.T →
    DV.LocLe (D.plEq w) ⌊DV.ur D w (tauP X K (aL L) (bL L) (D.what₂.places.resChar w))⌋₊ (L.NuLat u) (DV.MramL D u)

section Descent

open IsDedekindDomain

variable {A K : Type} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  (w : HeightOneSpectrum A)
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {ι : Type} [Fintype ι] (b : Module.Basis ι K V)
  {O Kf Fn : Type} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup Fn] [Module Kf Fn] [Module O Fn]
  [IsScalarTower O Kf Fn] (φ : K →+* Kf) (cmp : V →+ Fn)

abbrev locW : Subalgebra A K := Localization.subalgebra.ofField K _ w.asIdeal.primeCompl_le_nonZeroDivisors

theorem exists_smul_mem_of_mem_span (Lat : Submodule A V) (v : V)
    (hv : v ∈ Submodule.span (locW (K := K) w) (Lat : Set V)) : ∃ s : A, s ∉ w.asIdeal ∧ s • v ∈ Lat := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, by rwa [one_smul]⟩
  | zero => exact ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, by rw [smul_zero]; exact Lat.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, ?_⟩
    rw [smul_add]
    refine Lat.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Lat.smul_mem t hsx
    · rw [mul_smul]; exact Lat.smul_mem s hty
  | smul r x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨r, a, t, ht, rfl⟩ := r
    have ht0 : algebraMap A K t ≠ 0 := by
      intro h0
      have : (t : A) = 0 := (IsFractionRing.injective A K) (by rw [h0, map_zero])
      exact ht (by rw [this]; exact w.asIdeal.zero_mem)
    refine ⟨t * s, fun h => (w.isPrime.mem_or_mem h).elim ht hs, ?_⟩
    have : (t * s) • ((⟨algebraMap A K a * (algebraMap A K t)⁻¹, a, t, ht, rfl⟩ : locW (K := K) w) • x) =
        a • (s • x) := by
      rw [Subalgebra.smul_def]
      simp only
      rw [← algebraMap_smul K (t * s), ← algebraMap_smul K a, ← algebraMap_smul K s, smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [this]
    exact Lat.smul_mem a hsx

include b in
theorem cmp_expand (hs : ∀ a x, cmp (a • x) = φ a • cmp x) (x : V) :
    cmp x = ∑ a, φ (b.repr x a) • cmp (b a) := by
  conv_lhs => rw [← b.sum_repr x]
  rw [map_sum]
  exact Finset.sum_congr rfl fun a _ => hs _ _

theorem cmp_inj (hs : ∀ a x, cmp (a • x) = φ a • cmp x) (hli : LinearIndependent Kf (fun a => cmp (b a))) :
    Function.Injective cmp := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [cmp_expand b φ cmp hs x] at hx
  have h := Fintype.linearIndependent_iff.1 hli _ hx
  apply b.repr.injective
  ext a
  simpa using h a

theorem descent (hφ : ∀ x : K, w.valuation K x ≤ 1 ↔ φ x ∈ Set.range (algebraMap O Kf))
    (hs : ∀ a x, cmp (a • x) = φ a • cmp x) (hli : LinearIndependent Kf (fun a => cmp (b a)))
    (Lat : Submodule A V) (hfg : Lat.FG) (v : V) (hv : cmp v ∈ Submodule.span O (cmp '' (Lat : Set V))) :
    ∃ s : A, s ∉ w.asIdeal ∧ s • v ∈ Lat := by
  exact Bl.general_b_fact_upper_bis.goal1 w b φ cmp hφ hs hli Lat hfg v hv

end Descent

theorem level_primes_not_class_zero (P : ParameterChoice' D L) : LevelPrimesNotClassZero D := by
  intro p hp hc
  have h := P.level_split p hp
  rw [hc] at h
  exact absurd h (by simp)

theorem frobNe (D : D7) : FrobNe D := by
  intro p hp hc0 hev P _ _ σ hσ
  rw [(UpperTheory.galE_arithFrob_eq_iota_hP D p hp hc0 P σ hσ).2]
  exact hev

theorem val_le_one_iff (D : D7) (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    (D.plEq w).valuation D.what₂.LL x ≤ 1 ↔ (0 : WithTop ℤ) ≤ D.what₂.places.val w x := by
  by_cases hx : x = 0
  · subst hx; simp
  · have hv0 : (D.plEq w).valuation D.what₂.LL x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
    rw [D.val_eq w x hx]
    unfold vAdd
    have h1 : ((0 : WithTop ℤ) ≤ ((-WithZero.log ((D.plEq w).valuation D.what₂.LL x) : ℤ) : WithTop ℤ)) ↔
        WithZero.log ((D.plEq w).valuation D.what₂.LL x) ≤ 0 := by
      rw [← WithTop.coe_zero, WithTop.coe_le_coe]; omega
    rw [h1]
    conv_lhs => rw [← WithZero.exp_log hv0, ← WithZero.exp_zero, WithZero.exp_le_exp]

theorem resChar_mem_pow (D : D7) (w : D.what₂.places.Pl) :
    ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal ^ D.what₂.places.ramIdx w := by
  have hv := D.what₂.places.val_resChar w
  have hne : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 := by
    exact_mod_cast (D.what₂.places.resChar_prime w).ne_zero
  rw [D.val_eq w _ hne] at hv
  have hv' : vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) =
      ((D.what₂.places.ramIdx w : ℕ) : ℤ) := by exact_mod_cast hv
  rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem, ← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := D.what₂.LL)]
  have hx : algebraMap (𝓞 D.what₂.LL) D.what₂.LL ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) =
      ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by simp
  change (D.plEq w).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL _) ≤ _
  rw [hx]
  have hv0 : (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hne
  unfold vAdd at hv'
  rw [← WithZero.exp_log hv0, WithZero.exp_le_exp]
  omega

theorem nuServed_of (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D) (hdef : c.NuServedDef X Y K)
    (hServed : ServedGIdx X K) : NuServed X K := by
  intro u w hV hw x hx
  have hg := hServed u _ hV hw
  have h1 : c.cmp u w hg (D.nuIn u x) ∈ NP X Y K u w hg :=
    (hdef u w hg hV x).1 ⟨1, (Ideal.ne_top_iff_one _).1 (D.plEq w).isPrime.ne_top, by rwa [one_smul]⟩
  unfold NP at h1
  obtain ⟨⟨_, y, hy, hyx⟩, _⟩ := h1
  set T : ℕ := ⌈tauP X K (aL L) (bL L) (D.what₂.places.resChar w)⌉.toNat with hT
  have hpL : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 := by
    exact_mod_cast (D.what₂.places.resChar_prime w).ne_zero
  have hpK : ((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).Kf) ≠ 0 := by
    rw [← map_natCast (c.embW u w hg)]
    exact (map_ne_zero _).2 hpL
  have hyx' : ((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).Kf) ^ T • y = c.cmp u w hg (D.nuIn u x) := by
    rw [← hyx]
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [← map_natCast (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf), ← map_pow, algebraMap_smul]
  set x' : (D.div.Nu u).V := (((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ^ T)⁻¹ • x with hx'
  have hz : c.cmp u w hg (D.nuIn u x') = y := by
    rw [hx', map_smul, c.cmp_smul, ← hyx', map_inv₀, map_pow, map_natCast, inv_smul_smul₀ (pow_ne_zero _ hpK)]
  rw [SetLike.mem_coe, ← c.cmp_M u w hg, ← hz] at hy
  obtain ⟨s, hs, hsz⟩ := descent (D.plEq w) ((D.fm u).lat 0).b (c.embW u w hg) (c.cmp u w hg)
    (fun a => (val_le_one_iff D w a).trans (c.embW_int u w hg a)) (c.cmp_smul u w hg) (c.cmp_li u w hg)
    ((D.fm u).lat 0).L ((D.fm u).lat_good 0).2.1 _ hy
  refine ⟨s, hs, ?_⟩
  have hsx : s • x = (((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ^ T) • (s • x') := by
    rw [smul_comm, hx', ← algebraMap_smul D.what₂.LL ((((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL)) ^ T), map_pow,
      map_natCast, smul_inv_smul₀ (pow_ne_zero _ hpL)]
  rw [hsx]
  refine Submodule.smul_mem_smul ?_ ?_
  · have hle : ⌊DV.ur D w (tauP X K (aL L) (bL L) (D.what₂.places.resChar w))⌋₊ ≤ D.what₂.places.ramIdx w * T := by
      apply Nat.floor_le_of_le
      unfold DV.ur
      push_cast
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      have h2 : ((⌈tauP X K (aL L) (bL L) (D.what₂.places.resChar w)⌉ : ℤ) : ℝ) ≤ (T : ℝ) := by
        exact_mod_cast Int.self_le_toNat _
      exact le_trans (Int.le_ceil _) h2
    apply Ideal.pow_le_pow_right hle
    rw [pow_mul]
    exact Ideal.pow_mem_pow (resChar_mem_pow D w) T
  · change (D.nuIn u).restrictScalars (𝓞 D.what₂.LL) (s • x') ∈ ((D.fm u).lat 0).L
    rw [map_smul]
    exact hsz

def LenServed (X : Inst D L) (Y : LatInst D) (K : Consts) : Prop :=
  ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅ →
    ∃ l : ℕ, Module.length (D.gat u w hg).O
        (↥((D.gat u w hg).M ⊓ Y.Vram u w hg) ⧸
          (NP X Y K u w hg).comap ((D.gat u w hg).M ⊓ Y.Vram u w hg).subtype) = l ∧
      (l : ℝ) = (L.lenMN u w : ℝ) * vUnit (D.gat u w hg)

theorem linkG_at_core (X : Inst D L) (Y : LatInst D) (K : Consts) (hK : K.Nonneg) (C bo : ℝ) (hT : GatTies D)
    (hfill : ∀ w, ParametersFill X K w)
    (hlat0 : ∀ w (u : D.what₂.Word), VV X K (aL L) (bL L) (D.what₂.places.resChar w) = ∅ →
      D.what₂.places.resChar w ≠ (D.mem u).A.T → L.lenMN u w = 0)
    (hlen : LenServed X Y K)
    (hsupp : ∀ w, ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n → w ∈ L.supp)
    (hTied : LatTied hT X Y) (hNu : DV.NuDef D L)
    (h1 : AuxBlock8.Conclusion1 D L X K C bo) (h2 : AuxBlock8.Conclusion2 D L X K) (h0 : AuxBlock8.Conclusion0 D L X) (hG1 : AuxBlock8.admG1 D L X Y K)
    (hServed : ServedGIdx X K) (hSv : SvBound X K) (hIncl : NuServed X K) :
    LinkG_at X K (4 * |C| + 1) bo := by
  refine ⟨?_, hSv, ?_, served_orbits_in_set X K _ _, h2⟩
  · intro u w hw
    obtain ⟨_, _, _, _, htau, hio, _⟩ := hfill w
    by_cases hV : VV X K (aL L) (bL L) (D.what₂.places.resChar w) = ∅
    · have ht0 : L.tau w = 0 := by rw [htau]; unfold tauP; rw [if_pos hV]
      have hi0 : L.io w = 0 := by
        rw [hio]; unfold ioP
        rw [dif_neg (by rw [hV]; exact Finset.not_nonempty_empty)]
      have hl0 := hlat0 w u hV hw
      refine ⟨?_, ?_, fun _ => ⟨ht0, hi0, hl0⟩⟩
      · rw [ht0]
        have h0 : ⌊DV.ur D w 0⌋₊ = 0 := by unfold DV.ur; simp
        rw [h0]
        exact hNu.1 u w hw
      · rw [hl0, ht0, hi0]
        simp
    · refine ⟨by rw [htau]; exact hIncl u w hV hw, ?_, fun h => absurd h hV⟩
      have hg := hServed u _ hV hw
      obtain ⟨_, ⟨l, hl, hle⟩, _⟩ := hG1 hT hTied u w hg
      obtain ⟨l', hl', heq⟩ := hlen u w hg hV
      have hll : l = l' := by
        have := hl.symm.trans hl'
        exact_mod_cast this
      subst hll
      have hv := vUnit_pos (D.gat u _ hg) (Y.vOf u _ hg 0)
      have hd : ((D.gat u _ hg).d : ℝ) = (D.duS u : ℝ) := by rw [D.gat_d]; rfl
      rw [htau, hio]
      rw [heq, hd] at hle
      have h3 : (L.lenMN u w : ℝ) * vUnit (D.gat u _ hg) ≤
          ((D.duS u : ℝ) * (tauP X K (aL L) (bL L) (D.what₂.places.resChar w) +
            ioP X K (aL L) (bL L) (D.what₂.places.resChar w))) * vUnit (D.gat u _ hg) := by
        linarith
      exact le_of_mul_le_mul_right h3 hv
  · intro w hin hX
    have hp := D.what₂.places.resChar_prime w
    have hws := hsupp w hX
    have hin' : IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w) := hin.symm
    obtain ⟨_, hwp, hTT, hF, htau, _, hLa⟩ := hfill w
    have hgain := hF hws hin'
    obtain ⟨hA, hB⟩ := h1 _ hp hin' hX
    refine ⟨fun j hj => by rw [hgain j hj]; exact hA j hj, ?_⟩
    rw [htau, Finset.sum_congr rfl hgain]
    refine le_trans ?_ hB
    have hlo := lo_le_loG K L hK.1 hLa C bo _ hp
    have hsum : ∀ j ∈ SizeData₂.lifts D,
        ∑ t ∈ L.TTw w, (L.vonMangoldtClassSum j t (D.what₂.places.resChar w) -
          loG L (4 * |C| + 1) bo (D.what₂.places.resChar w)) ≤
        ∑ s ∈ TTP X K (aL L) (bL L) (D.what₂.places.resChar w),
          (askG X (aL L) (bL L) (D.what₂.places.resChar w) j s - lo K L C bo (D.what₂.places.resChar w)) := by
      intro j hj
      rw [← hTT, Finset.sum_map]
      apply Finset.sum_le_sum
      intro t _
      rw [ask_eq_askP X _ hp hwp j t]
      have haw : ∀ s ∈ D.host.TT, (aL L s : ℝ) ≤ 2 * L.sc.a := by
        intro s hs
        have h1 : aL L s = L.aT ⟨s, hs⟩ := by unfold aL; rw [dif_pos hs]
        obtain ⟨_, h2⟩ := L.aT_win ⟨s, hs⟩
        have h3 : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a := by
          have ha := sc_one_lt_a L.sc
          have hk : (1 : ℝ) ≤ (D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2) := by
            have hk1 : (1 : ℝ) ≤ (D.R.k : ℝ) := by
              have := D.R.m_add_three_le_k
              exact_mod_cast (show 1 ≤ D.R.k by omega)
            have hx1 : 1 ≤ L.sc.x ^ (Scale.A / 2) := Real.one_le_rpow L.sc.one_lt_alt.le (by unfold Scale.A; norm_num)
            nlinarith
          exact div_le_self (by linarith) hk
        rw [h1]
        linarith
      have hbw : ∀ s ∈ D.host.TT, (0 : ℝ) ≤ (bL L s : ℝ) := by
        intro s hs
        have h1 : bL L s = L.bT ⟨s, hs⟩ := by unfold bL; rw [dif_pos hs]
        rw [h1]
        exact le_trans (sc_b'_nonneg L.sc) (L.bT_ge ⟨s, hs⟩)
      have hPG := (h0 (aL L) (bL L) haw hbw _ hp hin' j hj t.1 t.2).1
      simp only [Function.Embedding.coe_subtype]
      linarith
    have hfl := fl_le_flG L C _ hp
    have hm : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
    have h4 := Finset.sum_le_sum hsum
    have h5 := mul_le_mul_of_nonneg_left hfl hm
    linarith

theorem linkG_at_of (X : Inst D L) (Y : LatInst D) (K : Consts) (hK : K.Nonneg) (C bo : ℝ) (hT : GatTies D)
    (hfill : ∀ w, ParametersFill X K w) (hlat : ∀ w, LatticeLengthsAtPlace X Y K w)
    (hsupp : ∀ w, ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n → w ∈ L.supp)
    (hTied : LatTied hT X Y) (hNu : DV.NuDef D L)
    (h1 : AuxBlock8.Conclusion1 D L X K C bo) (h2 : AuxBlock8.Conclusion2 D L X K) (h0 : AuxBlock8.Conclusion0 D L X) (hG1 : AuxBlock8.admG1 D L X Y K)
    (hServed : ServedGIdx X K) (hSv : SvBound X K) (hIncl : NuServed X K) :
    LinkG_at X K (4 * |C| + 1) bo :=
  linkG_at_core X Y K hK C bo hT hfill (fun w => (hlat w).2)
    (fun u w hg hV => (hlat w).1 (hsupp w (le_trans (cand_of_VV_ne X K _ _ _ hV).2.1.le
      (X'_le_X'' L.sc D.R.n D.R.n_pos'))) u hg)
    hsupp hTied hNu h1 h2 h0 hG1 hServed hSv hIncl

def Ev {eps : ℝ} (Fm : FamP eps) (P : ∀ x, Fm.Ix x → Prop) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i, P x i

theorem Ev.and {eps : ℝ} {Fm : FamP eps} {P Q : ∀ x, Fm.Ix x → Prop} (hP : Ev Fm P) (hQ : Ev Fm Q) :
    Ev Fm (fun x i => P x i ∧ Q x i) := by
  obtain ⟨a, ha⟩ := hP
  obtain ⟨b, hb⟩ := hQ
  exact ⟨max a b, fun x hx i => ⟨ha x (le_trans (le_max_left _ _) hx) i, hb x (le_trans (le_max_right _ _) hx) i⟩⟩

theorem Ev.x1 {eps : ℝ} (Fm : FamP eps) : Ev Fm (fun x _ => Fm.x1 < x) :=
  ⟨Fm.x1 + 1, fun x hx _ => by linarith⟩

def FamilyFirstGrowthBound {eps : ℝ} (Fm : FamP eps) : Prop :=
  Ev Fm fun x i => AuxBlock8.admG1 (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK

theorem servedGIdx_ev {eps : ℝ} (Fm : FamP eps) : Ev Fm fun x i => ServedGIdx (Fm.Gx x i) Fm.GK := by
  obtain ⟨x0, h⟩ := Ev.x1 Fm
  refine ⟨max x0 (((4 : ℕ) : ℝ) ^ (5 / Fm.ez)), fun x hx i => ?_⟩
  have hx1 := h x (le_trans (le_max_left _ _) hx) i
  have he : 0 < Fm.ez := by rw [← Fm.L_ez x i]; exact (Fm.L x i).sc.ez_pos
  apply servedGIdx_of _ _ _ (frobNe _) (level_primes_not_class_zero (Fm.params x hx1 i))
  refine UpperTheory.Host.le_floor_ez _ he (Fm.L_ez x i).ge 4 ?_
  rw [Fm.L_x x i hx1]
  exact le_trans (le_max_right _ _) hx

theorem svBound_ev {eps : ℝ} (Fm : FamP eps) : Ev Fm fun x i => SvBound (Fm.Gx x i) Fm.GK := by
  obtain ⟨x0, h⟩ := Ev.x1 Fm
  exact ⟨x0, fun x hx i => svBound_of _ _ Fm.GK_nonneg (Fm.params x (h x hx i) i)⟩

theorem nuServed_ev {eps : ℝ} (Fm : FamP eps) : Ev Fm fun x i => NuServed (Fm.Gx x i) Fm.GK := by
  obtain ⟨x0, h⟩ := (servedGIdx_ev Fm).and (Ev.x1 Fm)
  exact ⟨x0, fun x hx i => nuServed_of _ (Fm.Gy x i) _ (Fm.ex x (h x hx i).2 i).cmp (Fm.ex x (h x hx i).2 i).lat.served
    (h x hx i).1⟩

def NPDescF {eps : ℝ} (Fm : FamP eps) : Prop :=
  Ev Fm fun x i => ∀ hx : Fm.x1 < x, (Fm.ex x hx i).cmp.NPDesc (Fm.Gx x i) (Fm.Gy x i) Fm.GK

theorem sizeDataLat_ev {eps : ℝ} (Fm : FamP eps) (hd : NPDescF Fm) :
    Ev Fm fun x i => ∀ w, LatticeLengthsAtPlace (Fm.Gx x i) (Fm.Gy x i) Fm.GK w := by
  obtain ⟨x0, h⟩ := hd.and (Ev.x1 Fm)
  refine ⟨x0, fun x hx i w => ?_⟩
  obtain ⟨hdd, hx1⟩ := h x hx i
  exact LatCmp.sizeDataLat_of_latDefs (Fm.ex x hx1 i).cmp (Fm.gatT x i) _ _ _ (Fm.nuDef x hx1 i) (Fm.ex x hx1 i).lat
    (Fm.ex x hx1 i).nu_unserved (hdd hx1) w

theorem link_of_family_theorem {eps : ℝ} (Fm : FamP eps) (hP : AuxBlock8.ConclusionOnFamily Fm Fm.GK Fm.Gx) (hG1 : FamilyFirstGrowthBound Fm)
    (hFl : NPDescF Fm) : LinkG Fm := by
  obtain ⟨C, δ, hδ, hP'⟩ := hP
  have hP'' : Ev Fm fun x i => AuxBlock8.Conclusion₂ (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Fm.GK C ((Fm.L x i).sc.b ^ δ x) := hP'
  obtain ⟨x0, h⟩ := (((((hP''.and hG1).and (servedGIdx_ev Fm)).and (svBound_ev Fm)).and (nuServed_ev Fm)).and
    (sizeDataLat_ev Fm hFl)).and (Ev.x1 Fm)
  refine ⟨4 * |C| + 1, x0, δ, hδ, fun x hx i => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨hp, hg⟩, hs⟩, hv⟩, hi⟩, hf⟩, hx1⟩ := h x hx i
  exact linkG_at_of (Fm.Gx x i) (Fm.Gy x i) Fm.GK Fm.GK_nonneg C _ (Fm.gatT x i) (Fm.fills x hx1 i)
    hf (Fm.supp_sat x hx1 i) (Fm.latTied x hx1 i) (Fm.nuDef x hx1 i) hp.1 hp.2.1 hp.2.2.2.2.1 hg hs hv hi

theorem exists_place (D : D7) : Nonempty D.what₂.places.Pl := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.what₂.LL)
  exact ⟨D.plEq.symm ⟨M, hM.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField D.what₂.LL)⟩⟩

theorem eventually_sizes_admitted {eps : ℝ} (Fm : FamP eps) :
    Ev Fm fun x i => AuxBlock8.TypePrimeSizeConds (Fm.D x i) (Fm.L x i) Fm.GK := by
  obtain ⟨x0, h⟩ := Ev.x1 Fm
  refine ⟨x0, fun x hx i => ?_⟩
  have hx1 := h x hx i
  obtain ⟨w⟩ := exists_place (Fm.D x i)
  obtain ⟨_, _, _, _, _, _, hLa⟩ := Fm.fills x hx1 i w
  have P := Fm.params x hx1 i
  obtain ⟨hk, hN, hSc⟩ := Nm_le_Sc P
  have hkS := P.kS_le
  have hkSc : 5 * (Fm.L x i).Sc ≤ ((Fm.D x i).R.k : ℝ) * (Fm.L x i).Sc := mul_le_mul_of_nonneg_right hk (by linarith)
  refine ⟨Fm.sizes x hx1 i, ?_, ?_⟩
  · rw [hLa]
    exact P.S_le
  · unfold Nm
    linarith

def Adm1F {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ C : ℝ, 0 < C ∧ Ev Fm fun x i => AuxBlock8.adm1 (Fm.D x i) (Fm.L x i) (Fm.Gx x i) C

def Adm2F {eps : ℝ} (Fm : FamP eps) : Prop :=
  Ev Fm fun x i => AuxBlock8.adm2 (Fm.D x i) (Fm.L x i) (Fm.Gx x i)

def Adm3F {eps : ℝ} (Fm : FamP eps) : Prop := Ev Fm fun x i => AuxBlock8.adm3 (Fm.D x i) (Fm.L x i)

def Adm4F {eps : ℝ} (Fm : FamP eps) : Prop := Ev Fm fun x i => AuxBlock8.ArchimedeanSignatureMatching (Fm.D x i) (Fm.L x i) Fm.GK

def Adm5F {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ δ > 0, Ev Fm fun x i => AuxBlock8.adm5 (Fm.D x i) (Fm.L x i) Fm.GK δ

def Adm6F {eps : ℝ} (Fm : FamP eps) : Prop := Ev Fm fun x i => AuxBlock8.adm6 (Fm.D x i) (Fm.L x i) Fm.GK

def Adm7F {eps : ℝ} (Fm : FamP eps) : Prop :=
  Ev Fm fun x i => AuxBlock8.adm7 (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Fm.GK

def Adm8F {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ Ev Fm fun x i => AuxBlock8.adm8 (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Fm.GK C

def Adm9F {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ Ev Fm fun x i => AuxBlock8.adm9 (Fm.D x i) (Fm.L x i) (Fm.Gx x i) C

def AdmUF {eps : ℝ} (Fm : FamP eps) : Prop :=
  Ev Fm fun x i => AuxBlock8.unitBoundAtTwistedPlaces (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK

theorem family_admitted_of_parts {eps : ℝ} (Fm : FamP eps) (h1 : Adm1F Fm) (h2 : Adm2F Fm) (h3 : Adm3F Fm) (h4 : Adm4F Fm)
    (h5 : Adm5F Fm) (h6 : Adm6F Fm) (h7 : Adm7F Fm) (h8 : Adm8F Fm) (h9 : Adm9F Fm) (hU : AdmUF Fm)
    (hG1 : FamilyFirstGrowthBound Fm) : AuxBlock8.AdmF Fm Fm.GK Fm.Gx Fm.Gy := by
  obtain ⟨C31, hC31, h1⟩ := h1
  obtain ⟨Cm, hCm, h8⟩ := h8
  obtain ⟨Ce, hCe, h9⟩ := h9
  refine ⟨C31, Ce, Cm, hC31, hCe, hCm, fun δ hδ => ?_⟩
  obtain ⟨x0, h⟩ := (((((((((((h1.and h2).and h3).and h4).and (h5 δ hδ)).and h6).and h7).and h8).and h9).and
    hU).and hG1).and (eventually_sizes_admitted Fm))
  refine ⟨max x0 2, lt_of_lt_of_le one_lt_two (le_max_right _ _), fun x hx i => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, aU⟩, aG⟩, aS⟩ :=
    h x (le_trans (le_max_left _ _) hx) i
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, aU, aG, aS⟩

theorem family_second_bound_of_theorem {eps : ℝ} (Fm : FamP eps) (C : ℝ) (hC0 : 0 ≤ C) (hCk : C ≤ Fm.GK.kII) (hCt : C ≤ Fm.GK.tII)
    (hCL : C ≤ Fm.GK.La) (hCD : C ≤ Fm.GK.DII) (hCs : C ≤ Fm.GK.szII) (hCk' : C ≤ Fm.GK.kII')
    (h14 : tableLineDegreeFive.OrbitValuationBound Fm C) : Adm6F Fm := by
  have h14' : Ev Fm fun x i => tableLineDegreeFive.aux₃ (Fm.D x i) C := h14
  obtain ⟨x0, h⟩ := h14'.and (Ev.x1 Fm)
  refine ⟨x0, fun x hx i => ?_⟩
  obtain ⟨hp, hx1⟩ := h x hx i
  have P := Fm.params x hx1 i
  obtain ⟨hk, _, hSc⟩ := Nm_le_Sc P
  obtain ⟨hw1, hw2⟩ := w''_le (Fm.L x i).sc (Fm.D x i).R.n (Fm.D x i).R.n_pos'
  have hkS := P.kS_le
  have hab := two_b'_le_a (Fm.L x i).sc
  have hkSc : 5 * (Fm.L x i).Sc ≤ ((Fm.D x i).R.k : ℝ) * (Fm.L x i).Sc :=
    mul_le_mul_of_nonneg_right hk (by linarith)
  exact Joints.type_two_hypothesis_of_counts _ _ _ C hC0 hCk hCt hCL hCD hCs hCk' (by unfold cG; linarith) (by unfold cG; linarith) hp

def KapIDefF {eps : ℝ} (Fm : FamP eps) : Prop := Ev Fm fun x i => KapIDef (Fm.Gx x i) Fm.GK

theorem kapIDefF {eps : ℝ} (Fm : FamP eps) : KapIDefF Fm := by
  obtain ⟨x0, h⟩ := Ev.x1 Fm
  exact ⟨x0, fun x hx i => (Fm.ex x (h x hx i) i).kapI_def⟩

theorem family_kappa_bound {eps : ℝ} (Fm : FamP eps) (hX : KapIDefF Fm) : Adm7F Fm := by
  obtain ⟨x0, h⟩ := hX
  exact ⟨x0, fun x hx i => Joints.kappa_share_of_least_serving _ _ _ _ (h x hx i)⟩

theorem family_first_bound_of_theorem {eps : ℝ} (Fm : FamP eps) (CH C : ℝ) (hX : KapIDefF Fm) (hCH0 : 0 ≤ CH)
    (hCHk : CH ≤ Fm.GK.kI) (hCHD : CH ≤ Fm.GK.DI) (hCHr : 2 * CH ≤ Fm.GK.rho) (hC0 : 0 ≤ C)
    (hCt1 : 2 * C ≤ Fm.GK.kappaThresholdOne) (hCt2 : C ≤ Fm.GK.kappaThresholdTwo) (h13 : flipOneThree.Conclusion2Family Fm Fm.GK.La CH C) : Adm8F Fm := by
  obtain ⟨x0, h⟩ := hX
  refine ⟨C, hC0, x0, fun x hx i => ?_⟩
  exact Joints.type_one_hypothesis_of_bounds _ _ _ _ C CH C (h x hx i) Fm.GK_nonneg hCH0 hCHk hCHD hCHr hC0 hCt1 hCt2 le_rfl
    (by unfold cG; have := (Fm.L x i).Sc_pos; linarith) (h13 x i)

def SecondTheoremAtFamily {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ C ≤ Fm.GK.kII ∧ C ≤ Fm.GK.tII ∧ C ≤ Fm.GK.La ∧ C ≤ Fm.GK.DII ∧ C ≤ Fm.GK.szII ∧ C ≤ Fm.GK.kII' ∧
    tableLineDegreeFive.OrbitValuationBound Fm C

def FirstTheoremAtFamily {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ CH C : ℝ, 0 ≤ CH ∧ CH ≤ Fm.GK.kI ∧ CH ≤ Fm.GK.DI ∧ 2 * CH ≤ Fm.GK.rho ∧ 0 ≤ C ∧ 2 * C ≤ Fm.GK.kappaThresholdOne ∧
    C ≤ Fm.GK.kappaThresholdTwo ∧ flipOneThree.Conclusion2Family Fm Fm.GK.La CH C

def FamilyStatementAtOwnConstants {eps : ℝ} (Fm : FamP eps) : Prop :=
  AuxBlock8.AdmF Fm Fm.GK Fm.Gx Fm.Gy → AuxBlock8.ConclusionOnFamily Fm Fm.GK Fm.Gx

theorem family_statement_of_general {eps : ℝ} (Fm : FamP eps) (h : AuxBlock8.KudlaFamilyStatement Fm) : FamilyStatementAtOwnConstants Fm :=
  h Fm.GK Fm.GK_nonneg Fm.Gx Fm.Gy

def LinkHyps {eps : ℝ} (Fm : FamP eps) : Prop :=
  Adm1F Fm ∧ Adm2F Fm ∧ Adm3F Fm ∧ Adm4F Fm ∧ Adm5F Fm ∧ Adm6F Fm ∧ Adm7F Fm ∧ Adm8F Fm ∧ Adm9F Fm ∧ AdmUF Fm ∧
    FamilyFirstGrowthBound Fm ∧ NPDescF Fm

theorem linkG_of {eps : ℝ} (Fm : FamP eps) (hStmt : FamilyStatementAtOwnConstants Fm) (h : LinkHyps Fm) : LinkG Fm := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hU, hG1, hFl⟩ := h
  exact link_of_family_theorem Fm (hStmt (family_admitted_of_parts Fm h1 h2 h3 h4 h5 h6 h7 h8 h9 hU hG1)) hG1 hFl

theorem linkG_closed (𝒞 : FamClass) (h69 : Closed 𝒞 fun Fm _ => AuxBlock8.KudlaFamilyStatement Fm)
    (hA : Closed 𝒞 fun Fm _ => LinkHyps Fm) : Closed 𝒞 fun Fm _ => LinkG Fm :=
  (h69.and hA).imp fun Fm _ _ h => linkG_of Fm (family_statement_of_general Fm h.1) h.2

section Tools

open Formalism.BasicNotions

structure ExtremalProjectorTools : Prop where

  extremalProjectorAlt : ∀ D : D7, CovariantDegrees.adm5 D

theorem tool_statements_hold (h : ExtremalProjectorTools) (D : D7) : CovariantDegrees.Conclusion1 D ∧ CovariantDegrees.Conclusion2 D ∧ CovariantDegrees.HyperplaneRank D := by
  have a : CovariantDegrees.admitted D := ⟨GLWeightTheory.positivity_condition_holds D, GLWeightTheory.weight_condition_from_integral_form D, GLWeightTheory.exponent_condition_holds D, GLWeightTheory.key_positivity_condition D, h.extremalProjectorAlt D⟩
  have h1 := GLWeightTheory.problem_holds D a
  exact ⟨h1, ColumnFamilies.splitting_package_holds D, ColumnFamilies.Top.a2 D⟩

end Tools

section TheoremII

open Formalism.BasicNotions

def SecondTheoremReduced (D : D7) : Prop :=
  ∀ CLa Ck Crk Cdeg : ℝ, tableLineDegreeFive.admitted D CLa Ck Crk Cdeg →
    (∃ CLa' CD Csz : ℝ, 0 < CLa' ∧ 0 < CD ∧ 0 < Csz ∧ SourceCleaning.aux₃ D CLa' CD Csz) →
    (∃ FormalChartAtZero CE C6 C18 : ℝ, 0 < FormalChartAtZero ∧ 0 < CE ∧ 0 < C6 ∧ 0 < C18 ∧ ∀ CH : ℝ, FormalChartAtZero ≤ CH → PlaneGramData.aux₃ D CH CE C6 C18) →
    tableLineDegreeFive.ConclusionE D

theorem criterion_restricted_of_closed (D : D7) (h : tableLineDegreeFive.ClosedFormOfAdmitted D) : SecondTheoremReduced D :=
  fun CLa Ck Crk Cdeg hA _ _ => h CLa Ck Crk Cdeg hA

theorem gauss_binomial_ge (q : ℕ) : ∀ n k : ℕ, k ≤ n → q ^ (k * (n - k)) ≤ Formalism.G0.gaussBinom q n k
  | n, 0, _ => by rw [Formalism.G0.SubspaceCountP.gb_zero_right]; simp
  | 0, k + 1, h => absurd h (by omega)
  | n + 1, k + 1, h => by
    rw [Formalism.G0.SubspaceCountP.gb_succ_succ]
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · have hk : k = n := by omega
      subst hk
      have h1 := gauss_binomial_ge q k k le_rfl
      simp only [Nat.sub_self, Nat.mul_zero, pow_zero] at h1 ⊢
      omega
    · have h1 := gauss_binomial_ge q n (k + 1) (by omega)
      obtain ⟨d, rfl⟩ : ∃ d, n = k + 1 + d := ⟨n - (k + 1), by omega⟩
      have e1 : k + 1 + d + 1 - (k + 1) = d + 1 := by omega
      have e2 : k + 1 + d - (k + 1) = d := by omega
      rw [e2] at h1
      rw [e1]
      calc q ^ ((k + 1) * (d + 1)) = q ^ (k + 1) * q ^ ((k + 1) * d) := by rw [← pow_add]; congr 1; ring
        _ ≤ q ^ (k + 1) * Formalism.G0.gaussBinom q (k + 1 + d) (k + 1) := Nat.mul_le_mul_left _ h1
        _ ≤ _ := Nat.le_add_left _ _

theorem rational_planes_count (D : D7) : SelectionLemmas.ColumnFamilyClosure D := by
  intro FF _ _ k r hr
  have h := Formalism.G0.Top.subspaceCount (F := FF) (W := Fin k → FF) r
  rw [Module.finrank_fin_fun] at h
  have h2 : nPl FF k r = Formalism.G0.countBelow (⊤ : Submodule FF (Fin k → FF)) r :=
    Nat.card_congr (Equiv.subtypeEquivRight fun U => by simp)
  rw [h2, h]
  exact gauss_binomial_ge _ k r hr

structure Loc6 : Prop where

  p14R : ∀ D : D7, SecondTheoremReduced D

  p39B : ∀ D : D7, SelectionLemmas.SecondPartClosed D

  rationalPlanesClauseThree : ∀ D : D7, SelectionLemmas.admB3 D

  rationalPlanesClauseFour : ∀ D : D7, SelectionLemmas.ColumnFamilyLowerSet D

  rationalPlanesClauseFive : ∀ D : D7, SelectionLemmas.GenericProjectionCriterion D

  dualInclusionLattices : DualHeightInclusion
  bePerfect : BePerfect
  lpOneEvery : LPOneEvery
  flatTop : FlatTop
  dualHeightBasis : DualHeightBasis
  hlSpans : HLSpans
  testSide : TestSide

  wittIdent : WittIdent

  criterionClauseElevenB : ∀ D : D7, tableLineDegreeFive.FilteredProjectionCriterion D

  criterionClauseTwentyTwo : ∀ D : D7, tableLineDegreeFive.adm22 D

  criterionClauseThirtyFive : ∀ D : D7, tableLineDegreeFive.FewBadOrbits D

  criterionClauseThirtySix : ∀ D : D7, tableLineDegreeFive.LevelPrimesProviso D

theorem plane_count_theorem_with_constants (h70 : ExtremalProjectorTools) (h : Loc6) (D : D7) : ∃ CLa Ck Crk Cdeg : ℝ, SelectionLemmas.Conclusion2 D CLa Ck Crk Cdeg := by
  obtain ⟨⟨_, hV, _, _, _⟩, ⟨_, hA3, hB1, _, hB3, _, _⟩, hA2⟩ := tool_statements_hold h70 D
  have b : SelectionLemmas.AdmB D := ⟨TopChoiceBounds.symbol_space_orbit_holds D, Joints.valuation_transport_of_lemma D hV.1, h.rationalPlanesClauseThree D, h.rationalPlanesClauseFour D, h.rationalPlanesClauseFive D,
    rational_planes_count D, Joints.degree_bound_gives_symbol_space D hA2, Joints.reducibility_gives_symbol_space D hV, Joints.third_degree_bound_gives_symbol_space D hA3,
    Joints.first_isotypic_gives_symbol_space D hB1, Joints.third_isotypic_gives_symbol_space D hB3, Joints.space_statement_of_lemmas D hA2 hA3 hB1 hB3, Joints.transport_statement_holds D⟩
  obtain ⟨C₀, _, hC⟩ := h.p39B D b
  obtain ⟨Crk, Cdeg, _, _, hp⟩ := hC C₀ C₀ le_rfl le_rfl
  exact ⟨C₀, C₀, Crk, Cdeg, hp⟩

theorem derived_statements_with_constants (h70 : ExtremalProjectorTools) (h : Loc6) (D : D7) (CLa Ck Crk Cdeg : ℝ) (h39 : SelectionLemmas.Conclusion2 D CLa Ck Crk Cdeg) :
    ∃ CLa' CD Csz : ℝ, 0 < CLa' ∧ 0 < CD ∧ 0 < Csz ∧ SourceCleaning.aux₃ D CLa' CD Csz := by
  obtain ⟨⟨⟨hT11, hT12, hT13, hC14, hC15⟩, hV, hE, ⟨hL51, hL52⟩, hL61⟩, ⟨hA1, hA3, hB1, hB2, hB3, hC0, hC1⟩, hA2⟩ :=
    tool_statements_hold h70 D
  exact symbolGeneratorData.stmtE_proved D CLa Ck Crk Cdeg ⟨TopChoiceBounds.localiser_orbit_holds D, h70.extremalProjectorAlt D, Joints.invariant_projection_gives_localiser D hT11,
    Joints.invariant_denominator_gives_localiser D hT12, Joints.integral_invariants_give_localiser D hT13, Joints.corollary_denominator_gives_localiser D hC14,
    Joints.integral_corollary_gives_localiser D hC15, Joints.reducibility_gives_localiser D hV, Joints.first_degree_bound_gives_localiser D hA1, Joints.second_degree_bound_gives_localiser D hA2,
    Joints.third_degree_bound_gives_localiser D hA3, Joints.first_isotypic_gives_localiser D hB1, Joints.second_isotypic_gives_localiser D hB2, Joints.third_isotypic_gives_localiser D hB3,
    Joints.corollary_base_gives_localiser D hC0, Joints.corollary_zero_gives_localiser_hypothesis D hC1, Joints.support_lemma_gives_localiser D hE, Joints.multiplicity_decomposition_gives_localiser D hL51,
    Joints.second_decomposition_gives_localiser D hL52, Joints.lattice_index_gives_localiser D hL61, TopChoiceBounds.symbol_space_orbit_holds D,
    Joints.valuation_transport_of_lemma D hV.1, Joints.space_criterion_of_standard_basis D hA3, Joints.rank_degree_bounds_give_localiser D CLa Ck Crk Cdeg h39⟩

theorem split_theorem_with_constants (h70 : ExtremalProjectorTools) (h : Loc6) (D : D7) :
    ∃ FormalChartAtZero CE C6 C18 : ℝ, 0 < FormalChartAtZero ∧ 0 < CE ∧ 0 < C6 ∧ 0 < C18 ∧ ∀ CH : ℝ, FormalChartAtZero ≤ CH → PlaneGramData.aux₃ D CH CE C6 C18 := by
  obtain ⟨⟨⟨_, _, _, _, hC15⟩, hV, _, ⟨_, hL52⟩, hL61⟩, ⟨_, hA3, _, _, _, _, _⟩, hA2⟩ := tool_statements_hold h70 D
  obtain ⟨FormalChartAtZero, CE, C6, C18, h0, h1, h2, h3, hS⟩ := (Formalism.MainNotions.PlaneGram.stmtE D)
  refine ⟨FormalChartAtZero, CE, C6, C18, h0, h1, h2, h3, fun CH hCH p O _ _ _ _ hSet => hS CH hCH p O hSet ?_⟩
  exact ⟨Joints.isotypic_multiplicity_of_reducibility D hV (Joints.polIsoDecompB_of D (GLWeightTheory.weight_condition_from_integral_form D)) p O hSet,
    ⟨Joints.valuation_clauses_of_lattice_index D hL61.1 p O hSet, Joints.twisted_valuation_second_sentence D p O hSet⟩,
    ⟨Joints.isotypic_coefficient_of_degree_bound D hA2 p O hSet, Joints.third_degree_bound_gives_span_clause D hA3 p O hSet, Joints.span_column_clauses D p O hSet⟩,
    Joints.projection_of_isotypic_decomposition D hC15 hV.2 (Joints.polIsoDecompB_of D (GLWeightTheory.weight_condition_from_integral_form D)) p O hSet, Joints.digit_identity_of_decomposition D hL52.1 p O hSet,
    Joints.derivation_of_lattice_index D hL61.2.1 p O hSet⟩

theorem second_theorem_closed_everywhere (h70 : ExtremalProjectorTools) (h : Loc6) (D : D7) : tableLineDegreeFive.ConclusionE D := by
  obtain ⟨⟨⟨hT11, hT12, hT13, hC14, hC15⟩, hV, hE, ⟨_, hL52⟩, hL61⟩, ⟨hA1, hA3, hB1, hB2, hB3, hC0, hC1⟩, hA2⟩ :=
    tool_statements_hold h70 D
  obtain ⟨CLa, Ck, Crk, Cdeg, h39⟩ := plane_count_theorem_with_constants h70 h D
  exact h.p14R D CLa Ck Crk Cdeg ⟨TopChoiceBounds.orbit_positions_admitted_holds D, TopChoiceBounds.orbit_counts_admitted_holds D, h.dualInclusionLattices, h.bePerfect,
    h.lpOneEvery, h70.extremalProjectorAlt D,
    Joints.invariant_projection_gives_orbit_count D hT11, Joints.invariant_denominator_gives_orbit_count D hT12, Joints.integral_invariants_give_orbit_count D hT13,
    Joints.corollary_denominator_gives_orbit_count D hC14, Joints.integral_invariants_gives_counts D hC15, h.criterionClauseElevenB D, Joints.reducibility_gives_orbit_count D hV,
    Joints.first_degree_bound_gives_orbit_count D hA1, Joints.degree_bound_gives_multiplicity D hA2, Joints.third_degree_bound_gives_orbit_count D hA3,
    Joints.first_isotypic_gives_orbit_count D hB1, Joints.second_isotypic_gives_orbit_count D hB2, Joints.third_isotypic_gives_orbit_count D hB3,
    Joints.corollary_base_gives_orbit_count D hC0, Joints.corollary_zero_gives_orbit_count D hC1, Joints.support_lemma_gives_orbit_count D hE, h.criterionClauseTwentyTwo D,
    Joints.second_decomposition_gives_orbit_count D hL52, Joints.lattice_index_gives_count D hL61, Joints.valuation_transport_of_lemma D hV.1,
    Joints.rank_degree_bounds_give_orbit_count D CLa Ck Crk Cdeg h39, h.wittIdent, h.flatTop, h.dualHeightBasis, h.hlSpans, h.testSide,
    Joints.space_statement_of_lemmas D hA2 hA3 hB1 hB3, TopChoiceBounds.symbol_space_orbit_holds D, Joints.transport_statement_holds D, h.criterionClauseThirtyFive D, h.criterionClauseThirtySix D⟩
    (derived_statements_with_constants h70 h D CLa Ck Crk Cdeg h39) (split_theorem_with_constants h70 h D)

theorem second_theorem_absolute_constant (h70 : ExtremalProjectorTools) (h : Loc6) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ D : D7, tableLineDegreeFive.aux₃ D C₀ := by
  by_cases hne : Nonempty D7
  · obtain ⟨D0⟩ := hne
    obtain ⟨C₀, hC, hp⟩ := second_theorem_closed_everywhere h70 h D0
    exact ⟨C₀, hC.le, fun _ => hp C₀ le_rfl⟩
  · exact ⟨0, le_rfl, fun D => absurd ⟨D⟩ hne⟩

end TheoremII

section TheoremI

open Formalism.BasicNotions

structure Loc8All : Prop where

  p13B : ∀ D : D7, flipOneThree.SecondPartClosed D

  p13A : ∀ D : D7, flipOneThree.IntegralityFromMetricForLargeConstants D

  p15 : ∀ D : D7, ColumnSystems.ExtendedClosedForm D

  windowClauseTwo : ∀ D : D7, ColumnSystems.adm2 D

  windowClauseThree : ∀ D : D7, ColumnSystems.adm3 D

  lWeylV : flipOneThree.WeylV

  lWitt : WittIdent

  tFlatTop : FlatTop

  tFlatHH : ColumnSystems.FlatHH

  hyperLatticeBasis : DualHeightBasis

  hyperDualInclusion : DualHeightInclusion

  tBePerfect : BePerfect

  tHLSpans : HLSpans

  tTestSide : TestSide

  tLPOneEvery : LPOneEvery

  tCartanDomain : flipOneThree.CartanDomain

  tCartanOnto : flipOneThree.CartanOnto

  tKP1 : ∀ D : D7, flipOneThree.ArchimedeanSignatureMatching D

  tKP2 : ∀ D : D7, flipOneThree.adm5 D

  tKP3 : ∀ D : D7, flipOneThree.adm6 D

  tRES : ∀ D : D7, flipOneThree.adm7 D

  thresholdClauseOne : ∀ D : D7, flipOneThree.TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc =>
    ∀ X : flipOneThree.Inst, flipOneThree.adm1 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X

  thresholdClauseThree : ∀ D : D7, flipOneThree.TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc =>
    ∀ X : flipOneThree.Inst, flipOneThree.adm3 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X

  instanceClauseEight : ∀ (D : D7) (X : flipOneThree.Inst), flipOneThree.adm8 D X

theorem thresholds_and {P Q : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop} (hP : flipOneThree.TransportedAlt P) (hQ : flipOneThree.TransportedAlt Q) :
    flipOneThree.TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc =>
      P C0 CYb Cde Ck CD Cb CE1 CE2 Cc ∧ Q C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro Cc hCc
  obtain ⟨A0, hA0, hP⟩ := hP Cc hCc
  obtain ⟨B0, _, hQ⟩ := hQ Cc hCc
  refine ⟨max A0 B0, lt_max_of_lt_left hA0, fun C0 hC0 => ?_⟩
  obtain ⟨A1, hA1, hP⟩ := hP C0 (le_trans (le_max_left _ _) hC0)
  obtain ⟨B1, _, hQ⟩ := hQ C0 (le_trans (le_max_right _ _) hC0)
  refine ⟨max A1 B1, lt_max_of_lt_left hA1, fun CE1 CE2 h1 h2 => ?_⟩
  obtain ⟨A2, hA2, hP⟩ := hP CE1 CE2 (le_trans (le_max_left _ _) h1) (le_trans (le_max_left _ _) h2)
  obtain ⟨B2, _, hQ⟩ := hQ CE1 CE2 (le_trans (le_max_right _ _) h1) (le_trans (le_max_right _ _) h2)
  refine ⟨max A2 B2, lt_max_of_lt_left hA2, fun CYb Cde Ck CD Cb a1 a2 a3 a4 a5 => ?_⟩
  exact ⟨hP CYb Cde Ck CD Cb (le_trans (le_max_left _ _) a1) (le_trans (le_max_left _ _) a2)
      (le_trans (le_max_left _ _) a3) (le_trans (le_max_left _ _) a4) (le_trans (le_max_left _ _) a5),
    hQ CYb Cde Ck CD Cb (le_trans (le_max_right _ _) a1) (le_trans (le_max_right _ _) a2)
      (le_trans (le_max_right _ _) a3) (le_trans (le_max_right _ _) a4) (le_trans (le_max_right _ _) a5)⟩

theorem inequality_admissions_hold (h70 : ExtremalProjectorTools) (h : Loc8All) (D : D7) : ColumnSystems.admitted D := by
  obtain ⟨⟨_, hV, _, ⟨hL51, hL52⟩, hL61⟩, ⟨hA1, hA3, hB1, hB2, hB3, hC0, hC1⟩, hA2⟩ := tool_statements_hold h70 D
  exact ⟨GLWeightTheory.positivity_condition_holds D, h.windowClauseTwo D, h.windowClauseThree D, Joints.reducibility_gives_counting_input D hV, Joints.first_degree_bound_gives_counting_input D hA1,
    Joints.third_degree_bound_gives_counting_input D hA3, Joints.first_isotypic_gives_statement D hB1, Joints.second_isotypic_gives_counting_input D hB2, Joints.isotypic_bound_gives_statement D hB3,
    Joints.corollary_base_gives_counting_input D hC0, Joints.corollary_gives_lattice_count D hC1, Joints.decomposition_gives_log_valuation D hL51, Joints.second_decomposition_gives_counting_input D hL52,
    Joints.lattice_index_gives_counting_input D hL61, Joints.second_degree_bound_gives_counting_input D hA2, h.lWitt, h.tFlatTop, h.tFlatHH, GLWeightTheory.weight_condition_from_integral_form D,
    Joints.corollary_zero_gives_counting_input D hC1⟩

theorem extended_windows_theorem (h70 : ExtremalProjectorTools) (h : Loc8All) (D : D7) : ColumnSystems.Closed (ColumnSystems.ExtendedAllConclusions D) := h.p15 D (inequality_admissions_hold h70 h D)

theorem first_theorem_tools_admitted (h70 : ExtremalProjectorTools) (h : Loc8All) (D : D7) : flipOneThree.AdmT D := by
  obtain ⟨⟨⟨_, hT12, hT13, _, hC15⟩, _, _, _, _⟩, ⟨hA1, hA3, _, _, _, _, _⟩, hA2⟩ := tool_statements_hold h70 D
  exact ⟨Joints.invariant_denominator_gives_exponent_data D hT12, Joints.integral_invariants_give_exponent_data D ⟨hT13, hC15⟩, h70.extremalProjectorAlt D,
    ⟨h.tKP1 D, h.tKP2 D, h.tKP3 D, h.tRES D⟩, Joints.degree_bounds_give_exponent_data D ⟨hA1, hA2, hA3⟩,
    ⟨ColumnFamilies.Top.b9 D, ColumnFamilies.Top.b10 D, ColumnFamilies.Top.b11 D, ColumnFamilies.Top.b19 D⟩, ⟨h.tCartanDomain, h.tCartanOnto⟩,
    ⟨h.lWitt, h.tFlatTop, h.tFlatHH⟩, ⟨h.hyperLatticeBasis, h.hyperDualInclusion, h.tBePerfect, h.tHLSpans⟩, h.tTestSide,
    h.tLPOneEvery, ⟨h.windowClauseThree D, h.lWeylV⟩⟩

theorem first_theorem_admitted_closed (h70 : ExtremalProjectorTools) (h : Loc8All) (D : D7) : flipOneThree.AdmBE D := by
  obtain ⟨⟨⟨_, hT12, _, _, _⟩, _, _, _, _⟩, _, _⟩ := tool_statements_hold h70 D
  have hT := thresholds_and (h.p13A D) (thresholds_and (h.thresholdClauseOne D) (h.thresholdClauseThree D))
  intro Cc hCc
  obtain ⟨A0, hA0, h15⟩ := extended_windows_theorem h70 h D Cc hCc
  obtain ⟨B0, _, hT⟩ := hT Cc hCc
  refine ⟨max A0 B0, lt_max_of_lt_left hA0, fun C₀ hC0 => ?_⟩
  obtain ⟨A1, hA1, h15⟩ := h15 C₀ (le_trans (le_max_left _ _) hC0)
  obtain ⟨B1, _, hT⟩ := hT C₀ (le_trans (le_max_right _ _) hC0)
  refine ⟨max A1 B1, lt_max_of_lt_left hA1, fun CE1 CE2 Cm h1 h2 h3 => ?_⟩
  obtain ⟨A2, hA2, h15⟩ := h15 CE1 CE2 Cm (le_trans (le_max_left _ _) h1) (le_trans (le_max_left _ _) h2)
    (le_trans (le_max_left _ _) h3)
  obtain ⟨B2, _, hT⟩ := hT CE1 CE2 (le_trans (le_max_right _ _) h1) (le_trans (le_max_right _ _) h2)
  have hCm : 0 ≤ Cm := le_trans hA1.le (le_trans (le_max_left _ _) h3)
  refine ⟨max A2 B2, lt_max_of_lt_left hA2, fun CH hCH => ?_⟩
  have ha := le_trans (le_max_left A2 B2) hCH
  have hb := le_trans (le_max_right A2 B2) hCH
  obtain ⟨Ckap, Ct, Cs, k1, k2, k3, hExt, h2Ext, _, _, _, hAlt2, hAlt3, h4Ext, hR2, _⟩ := h15 CH CH CH CH CH ha ha ha ha ha
  obtain ⟨hS1, ha1, ha3⟩ := hT CH CH CH CH CH hb hb hb hb hb
  obtain ⟨CA, hCA, hSt⟩ := hS1 Ckap (Cs + Ckap)
  have hconds1 : ∀ X : flipOneThree.Inst, flipOneThree.Conclusion1 D C₀ CH CH CH CH CH CE1 CE2 Cc CA X := fun X =>
    hSt X ⟨ha1 X, Joints.weight_condition_of_integral_form D X hT12, ha3 X, h.tKP1 D, h.tKP2 D, h.tKP3 D, h.tRES D, h.instanceClauseEight D X,
      Joints.extension_gives_ratio_bound D C₀ CH CH CH CH CH CE1 CE2 Cm Ckap Cc Cs X k1.le hCm hAlt2 h2Ext,
      Joints.fourth_extension_gives_ratio_bound D C₀ CH CH CH CH CH CE1 CE2 Cc X h4Ext,
      Joints.residue_bound_of_extension D C₀ CH CH CH CH CH CE1 CE2 Cc X hR2⟩
  exact ⟨CA, Ckap, Ct, Cs + Ckap, hCA, k1, k2, by linarith,
    Joints.bad_share_bound_of_extension D C₀ CH CA CE1 CE2 Cc hconds1,
    Joints.bad_share_of_extension_proposition D C₀ CH CA CE1 CE2 Cm Ckap Ct Cc hCA.le hExt,
    Joints.kappa_share_bound_of_extension D C₀ CH CE1 CE2 Cm Ckap Cc Cs k1.le hCm hAlt2 h2Ext,
    Joints.alternative_extension_gives_bound D C₀ CH CE1 CE2 Ct Cc hAlt3, first_theorem_tools_admitted h70 h D⟩

theorem first_theorem_with_constants (h70 : ExtremalProjectorTools) (h : Loc8All) : ∀ D : D7, flipOneThree.projection_lemma_base_level D := fun D => h.p13B D (first_theorem_admitted_closed h70 h D)

theorem first_theorem_uniform_thresholds (h70 : ExtremalProjectorTools) (h : Loc8All) :
    ∃ T0 : ℝ, 0 < T0 ∧ ∀ C₀ : ℝ, T0 ≤ C₀ → ∃ T2 C : ℝ, 0 < T2 ∧ 0 < C ∧ ∀ CH : ℝ, T2 ≤ CH →
      ∀ D : D7, flipOneThree.Conclusion2 D C₀ CH C := by
  by_cases hne : Nonempty D7
  · obtain ⟨D0⟩ := hne
    obtain ⟨T0, hT0, hp⟩ := first_theorem_with_constants h70 h D0
    refine ⟨T0, hT0, fun C₀ hC0 => ?_⟩
    obtain ⟨T2, C, hT2, hC, hp⟩ := hp C₀ hC0
    exact ⟨T2, C, hT2, hC, fun CH hCH _ => hp CH hCH⟩
  · exact ⟨1, one_pos, fun _ _ => ⟨1, 1, one_pos, one_pos, fun _ _ D => absurd ⟨D⟩ hne⟩⟩

theorem first_theorem_threshold_functions (h70 : ExtremalProjectorTools) (h : Loc8All) :
    ∃ (T0 : ℝ) (T2 C : ℝ → ℝ), 0 < T0 ∧ ∀ C₀ : ℝ, T0 ≤ C₀ → 0 < T2 C₀ ∧ 0 < C C₀ ∧ ∀ CH : ℝ, T2 C₀ ≤ CH →
      ∀ D : D7, flipOneThree.Conclusion2 D C₀ CH (C C₀) := by
  classical
  obtain ⟨T0, hT0, hp⟩ := first_theorem_uniform_thresholds h70 h
  choose! T2 C hTC using hp
  exact ⟨T0, T2, C, hT0, fun C₀ hC0 => hTC C₀ hC0⟩

structure Loc8 : Prop where

  p13B : ∀ D : D7, flipOneThree.SecondPartClosed D

  p13A : ∀ D : D7, flipOneThree.IntegralityFromMetricForLargeConstants D

  p15 : ∀ D : D7, ColumnSystems.ExtendedClosedForm D

  windowClauseTwo : ∀ D : D7, ColumnSystems.adm2 D

  windowClauseThree : ∀ D : D7, ColumnSystems.adm3 D

  lWeylV : flipOneThree.WeylV

  tFlatHH : ColumnSystems.FlatHH

  tCartanDomain : flipOneThree.CartanDomain

  tCartanOnto : flipOneThree.CartanOnto

  tKP2 : ∀ D : D7, flipOneThree.adm5 D

  tKP3 : ∀ D : D7, flipOneThree.adm6 D

  tRES : ∀ D : D7, flipOneThree.adm7 D

theorem loc8All_of (h70 : ExtremalProjectorTools) (h6 : Loc6) (h : Loc8) : Loc8All where
  p13B := h.p13B
  p13A := h.p13A
  p15 := h.p15
  windowClauseTwo := h.windowClauseTwo
  windowClauseThree := h.windowClauseThree
  lWeylV := h.lWeylV
  lWitt := h6.wittIdent
  tFlatTop := h6.flatTop
  tFlatHH := h.tFlatHH
  hyperLatticeBasis := h6.dualHeightBasis
  hyperDualInclusion := h6.dualInclusionLattices
  tBePerfect := h6.bePerfect
  tHLSpans := h6.hlSpans
  tTestSide := h6.testSide
  tLPOneEvery := h6.lpOneEvery
  tCartanDomain := h.tCartanDomain
  tCartanOnto := h.tCartanOnto
  tKP1 := CountingStatementReduction.key_positivity_condition
  tKP2 := h.tKP2
  tKP3 := h.tKP3
  tRES := h.tRES
  thresholdClauseOne := CountingStatementReduction.positivity_condition_eventually
  thresholdClauseThree := CountingStatementReduction.exponent_bound_eventually
  instanceClauseEight := fun D X => PolBridge.combined_weight_of_nested_sets D X (GLWeightTheory.weight_condition_from_integral_form D) (ColumnFamilies.Top.b15 D)

end TheoremI

section Sizes

open Formalism.BasicNotions

theorem log_cube_le (M δ : ℝ) (hδ : 0 < δ) : ∃ x0 : ℝ, ∀ x ≥ x0, M * Real.log x ^ 3 ≤ x ^ δ := by
  have h := (isLittleO_log_rpow_rpow_atTop (3 : ℝ) hδ).def (c := 1 / (|M| + 1)) (by positivity)
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 h
  refine ⟨max x0 1, fun x hx => ?_⟩
  have h1 := hx0 x (le_trans (le_max_left _ _) hx)
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hp : 0 ≤ x ^ δ := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hl _), Real.norm_of_nonneg hp,
    show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h1
  have hM : 0 < |M| + 1 := by positivity
  have h2 : (|M| + 1) * Real.log x ^ 3 ≤ x ^ δ := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hM] at h1
    linarith
  have h3 : M * Real.log x ^ 3 ≤ (|M| + 1) * Real.log x ^ 3 :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self M]) (by positivity)
  linarith

theorem sizes_bound_of_log_estimates (K : Consts) (δ Ce : ℝ) (hLa : 0 < K.La) (hCe : 0 < Ce) (hx3 : 3 ≤ L.sc.x)
    (hG : (Gp L.sc : ℝ) ≤ Ce * Real.log L.sc.x / L.sc.delta1) (hN : (N1 L.sc : ℝ) ≤ Ce * Real.log L.sc.x)
    (hk : (D.R.k : ℝ) ≤ L.sc.x ^ (6 : ℝ))
    (hbig : (2 * K.La * Ce ^ 2 + 38 * Ce + 1 / K.La) * Real.log L.sc.x ^ 3 ≤ L.sc.x ^ δ) :
    AuxBlock8.adm5 D L K δ := by
  set x := L.sc.x with hx
  set e := L.sc.eps with he
  set l := Real.log x with hl
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hl1 : 1 ≤ l := TopChoiceBounds.one_le_log_of_three_le_bis hx3
  have he0 : 0 < e := L.sc.eps_pos
  set xe := x ^ e with hxe
  set xd := x ^ δ with hxd
  have hxe1 : 1 ≤ xe := Real.one_le_rpow hx1 he0.le
  have hxd0 : 0 < xd := Real.rpow_pos_of_pos hx0 _
  have hl2 : l ^ 2 ≤ l ^ 3 := pow_le_pow_right₀ hl1 (by norm_num)
  have hl13 : l ≤ l ^ 3 := by
    calc l = l ^ 1 := (pow_one l).symm
      _ ≤ l ^ 3 := pow_le_pow_right₀ hl1 (by norm_num)
  have hl3 : 1 ≤ l ^ 3 := one_le_pow₀ hl1
  have hinv : 0 < 1 / K.La := by positivity
  have hA : 2 * K.La * Ce ^ 2 * l ^ 3 ≤ xd := by
    have : 0 ≤ (38 * Ce + 1 / K.La) * l ^ 3 := by positivity
    nlinarith
  have hB : 38 * Ce * l ^ 3 ≤ xd := by
    have : 0 ≤ (2 * K.La * Ce ^ 2 + 1 / K.La) * l ^ 3 := by positivity
    nlinarith
  have hC : 1 / K.La ≤ xd := by
    have h1 : 0 ≤ (2 * K.La * Ce ^ 2 + 38 * Ce) * l ^ 3 := by positivity
    have h2 : 1 / K.La ≤ 1 / K.La * l ^ 3 := le_mul_of_one_le_right hinv.le hl3
    nlinarith
  have hloga : Real.log L.sc.a = l + xe := by
    unfold Scale.a Scale.b Scale.L
    rw [Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hN1 : (1 : ℝ) ≤ (N1 L.sc : ℝ) := by
    have : 1 ≤ N1 L.sc := by unfold N1 orbitWindowCount; omega
    exact_mod_cast this
  have hd1 : 1 / L.sc.delta1 = x ^ (e / 8) := by
    unfold Scale.delta1
    rw [Real.rpow_neg hx0.le, one_div, inv_inv]
  have hx8 : 0 < x ^ (e / 8) := Real.rpow_pos_of_pos hx0 _
  have hG' : (Gp L.sc : ℝ) ≤ Ce * l * x ^ (e / 8) := by
    rw [← hd1, mul_one_div]; exact hG
  refine ⟨?_, ?_, fun p hp => ⟨fun hp0 => ?_, fun hpX => ?_⟩⟩
  · rw [Real.rpow_sub hx0, div_le_iff₀ hxd0]
    unfold La
    rw [hloga]
    have h1 : 1 ≤ K.La * xd := by
      rw [div_le_iff₀ hLa] at hC
      linarith
    have h2 : (1 : ℝ) ≤ (N1 L.sc : ℝ) ^ 2 := one_le_pow₀ hN1
    have h3 : xe ≤ (N1 L.sc : ℝ) ^ 2 * (l + xe) := by nlinarith
    calc xe ≤ (N1 L.sc : ℝ) ^ 2 * (l + xe) := h3
      _ ≤ (K.La * xd) * ((N1 L.sc : ℝ) ^ 2 * (l + xe)) := le_mul_of_one_le_left (by positivity) h1
      _ = K.La * (N1 L.sc : ℝ) ^ 2 * (l + xe) * xd := by ring
  · rw [Real.rpow_add hx0]
    unfold La
    rw [hloga]
    have h1 : (N1 L.sc : ℝ) ^ 2 ≤ (Ce * l) ^ 2 := pow_le_pow_left₀ (by positivity) hN 2
    have h2 : l + xe ≤ 2 * l * xe := by nlinarith
    calc K.La * (N1 L.sc : ℝ) ^ 2 * (l + xe) ≤ K.La * (Ce * l) ^ 2 * (2 * l * xe) := by gcongr
      _ = xe * (2 * K.La * Ce ^ 2 * l ^ 3) := by ring
      _ ≤ xe * xd := mul_le_mul_of_nonneg_left hA (by positivity)
  · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hpp : (0 : ℝ) < p := by linarith
    have hlp0 : 0 ≤ Real.log p := Real.log_nonneg hp1
    have hlp : Real.log p ≤ 38 * l := by
      have h1 : (p : ℝ) ≤ x ^ (38 : ℝ) := by
        refine le_trans hp0.le ?_
        unfold Scale.p0 Scale.A
        have h2 : (D.R.k : ℝ) ^ 2 ≤ (x ^ (6 : ℝ)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hk 2
        have h3 : (x ^ (6 : ℝ)) ^ 2 * x ^ (26 : ℝ) = x ^ (38 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
          norm_num
        rw [← h3]
        exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hx0.le _)
      have h4 := Real.log_le_log hpp h1
      rwa [Real.log_rpow hx0] at h4
    unfold Qp
    rw [Real.log_pow, Real.rpow_add hx0]
    calc (Gp L.sc : ℝ) * Real.log p ≤ (Ce * l * x ^ (e / 8)) * (38 * l) := by gcongr
      _ = x ^ (e / 8) * (38 * Ce * l ^ 2) := by ring
      _ ≤ x ^ (e / 8) * (38 * Ce * l ^ 3) := by gcongr
      _ ≤ x ^ (e / 8) * xd := mul_le_mul_of_nonneg_left hB hx8.le
  · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hpp : (0 : ℝ) < p := by linarith
    have hlp0 : 0 ≤ Real.log p := Real.log_nonneg hp1
    have hlp : Real.log p ≤ x ^ (e / 3) := by
      have h4 := Real.log_le_log hpp hpX.le
      unfold Scale.X' at h4
      rwa [Real.log_exp] at h4
    have hx3' : 0 < x ^ (e / 3) := Real.rpow_pos_of_pos hx0 _
    have hsplit : x ^ (11 * e / 24 + δ) = x ^ (e / 8) * x ^ (e / 3) * xd := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
      congr 1
      ring
    unfold Qp
    rw [Real.log_pow, hsplit]
    have h5 : Ce * l ≤ xd := by
      have : Ce * l ≤ 38 * Ce * l ^ 3 := by nlinarith
      linarith
    calc (Gp L.sc : ℝ) * Real.log p ≤ (Ce * l * x ^ (e / 8)) * x ^ (e / 3) := by gcongr
      _ = x ^ (e / 8) * x ^ (e / 3) * (Ce * l) := by ring
      _ ≤ x ^ (e / 8) * x ^ (e / 3) * xd := mul_le_mul_of_nonneg_left h5 (by positivity)

theorem family_sizes_bound {eps : ℝ} (Fm : FamP eps) (hLa : 0 < Fm.GK.La) : Adm5F Fm := by
  intro δ hδ
  obtain ⟨i0⟩ := Fm.Ix_zero
  have heps : 0 < eps := by
    have := (Fm.L 0 i0).sc.eps_pos
    rwa [Fm.L_eps] at this
  obtain ⟨Ce, hCe, hC⟩ := (TopChoiceBounds.master_orbit_sizes_hold (Fm.D 0 i0)).1 (⌈8 * ((2 + 8 * eps) + 2) / eps⌉₊ + 1) (2 + 8 * eps)
    (by omega) (by linarith)
  obtain ⟨x0, hx0⟩ := log_cube_le (2 * Fm.GK.La * Ce ^ 2 + 38 * Ce + 1 / Fm.GK.La) δ hδ
  refine ⟨max (max (Fm.x1 + 1) 3) x0, fun x hx i => ?_⟩
  have hx1 : Fm.x1 < x := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
    linarith
  have hx3 : (3 : ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxx := Fm.L_x x i hx1
  have hee := Fm.L_eps x i
  have hd0 : 0 < (Fm.L x i).sc.delta1 := sc_delta1_pos _
  have hd1 : (Fm.L x i).sc.delta1 ≤ 1 := by
    unfold Scale.delta1
    apply Real.rpow_le_one_of_one_le_of_nonpos (Fm.L x i).sc.one_lt_alt.le
    have := (Fm.L x i).sc.eps_pos
    linarith
  have hr : rG (Fm.L x i).sc = ⌈8 * ((2 + 8 * eps) + 2) / eps⌉₊ + 1 := by
    unfold rG KG hG
    rw [hee]
  have hh : hG (Fm.L x i).sc = 2 + 8 * eps := by
    unfold hG
    rw [hee]
  obtain ⟨hGb, hNb, _⟩ := hC (Fm.L x i).sc.delta1 (Fm.L x i).sc.x hd0 hd1 (by rw [hxx]; exact hx3)
  rw [← hr, ← hh] at hGb hNb
  refine sizes_bound_of_log_estimates Fm.GK δ Ce hLa hCe (by rw [hxx]; exact hx3) hGb hNb ?_ (by rw [hxx]; exact hx0 x (le_trans (le_max_right _ _) hx))
  have hk := (Fm.sizes x hx1 i).2.2.1.2
  refine le_trans hk (Real.rpow_le_rpow_of_exponent_le (Fm.L x i).sc.one_lt_alt.le ?_)
  have := (Fm.L x i).sc.eps_lt
  have h0 := (Fm.L x i).sc.eps_pos
  unfold szTh
  linarith

end Sizes

section Rest

theorem family_first_lemma {eps : ℝ} (Fm : FamP eps) : Adm1F Fm := TopChoiceBounds.family_uniform_constant_holds Fm

theorem family_orders_first_part {eps : ℝ} (Fm : FamP eps) (C₄ : ℝ) (hS : CornerGLContinuity.FamilyOrdersSmallPrimeBound Fm C₄) (hO : CornerGLContinuity.FamilyGlobalOrderEstimate Fm C₄) :
    Adm3F Fm := by
  obtain ⟨x0, h⟩ := hS hO
  exact ⟨x0, fun x hx i => TopChoiceBounds.order_statement_of_odd_primes (h x hx i) (J.two_readings_of_Frobenius _)⟩

theorem family_orders_bound_of_lemma {eps : ℝ} (Fm : FamP eps) (hS : CornerGLContinuity.FamilyOrdersLargePrimeBound Fm) (hCN : CornerGLContinuity.FamilyWindowLogBound Fm) : Adm4F Fm := by
  obtain ⟨x0, h⟩ := hS (TopChoiceBounds.family_master_orbit_holds Fm) hCN
  exact ⟨x0, fun x hx i => TopChoiceBounds.band_ratio_statement_of _ (h x hx i)⟩

def TrivialStabiliserFiniteClasses (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    (D.gat u w hg).TrivStab ∧ (D.gat u w hg).FinClasses

def OperatorsPreserveLattices (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    FormalGroupSystem.adm12 D (D.gat u w hg)

theorem stability_of_trivial_stabilisers (hE : TrivialStabiliserFiniteClasses D) : CornerGLContinuity.MLatticeCond D :=
  fun u w hg => LatticeSystems.theta_kernel_expansion D _ ⟨(hE u w hg).1, (hE u w hg).2, LatticeSystems.exponent_condition_holds D _⟩

theorem service_statement_of_stability (X : Inst D L) (Y : LatInst D) (K : Consts) (hS : FormalGroupSystem.RamifiedSublatticeVolumeOfAdmissible D L X Y K) (hE : TrivialStabiliserFiniteClasses D)
    (hY : OperatorsPreserveLattices D) : CornerGLContinuity.ServiceLatticeCondition D L X Y K :=
  hS fun u w hg => ⟨stability_of_trivial_stabilisers hE u w hg, hY u w hg, (hE u w hg).2, LatticeSystems.exponent_condition_holds D _⟩

theorem saturated_ramified_lattice (Y : LatInst D) (c : LatCmp D) (hV : c.VramDef Y) : CornerGLContinuity.RamifiedPartSaturated D Y := by
  intro u w hg
  refine ⟨inf_le_left, fun a x hx ha hax => ⟨hx, ?_⟩⟩
  have hfr : IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf :=
    ((D.gat u w hg).P.setting (Y.vOf u w hg 0)).frac_O
  have ha' : algebraMap (D.gat u w hg).O (D.gat u w hg).Kf a ≠ 0 := by
    intro h0
    exact ha ((IsFractionRing.injective (D.gat u w hg).O (D.gat u w hg).Kf) (by rw [h0, map_zero]))
  have h1 : a • x ∈ (Y.Vram u w hg : Set (D.gat u w hg).Fn) := hax.2
  rw [hV u w hg] at h1
  have h2 : x ∈ (Y.Vram u w hg : Set (D.gat u w hg).Fn) := by
    rw [hV u w hg]
    have h3 := Submodule.smul_mem _ (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf a)⁻¹ h1
    rwa [← algebraMap_smul (D.gat u w hg).Kf a x, inv_smul_smul₀ ha'] at h3
  exact h2

theorem eventually_large_scale_bound {eps : ℝ} (Fm : FamP eps) : Ev Fm fun x i => CornerGLContinuity.LargeScaleSmallness (Fm.D x i) (Fm.L x i) := by
  obtain ⟨x0, h⟩ := Ev.x1 Fm
  refine ⟨max x0 ((2 : ℝ) ^ (1 / eps)), fun x hx i => ?_⟩
  have hx1 := h x (le_trans (le_max_left _ _) hx) i
  have he : 0 < eps := by rw [← Fm.L_eps x i]; exact (Fm.L x i).sc.eps_pos
  refine ⟨le_trans one_le_two (Fm.D x i).R.two_le_m, ?_⟩
  rw [Fm.L_x x i hx1, Fm.L_eps x i]
  have h3 : (2 : ℝ) ^ (1 / eps) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) h3
  have h4 : ((2 : ℝ) ^ (1 / eps)) ^ eps ≤ x ^ eps := Real.rpow_le_rpow (by positivity) h3 he.le
  rw [← Real.rpow_mul (by norm_num)] at h4
  have h5 : 1 / eps * eps = 1 := by field_simp
  rw [h5, Real.rpow_one] at h4
  rw [Real.rpow_neg hx0.le, one_div]
  exact inv_anti₀ (by norm_num) h4

structure Fam0 {eps : ℝ} (Fm : FamP eps) : Prop where

  p33i : ∀ C₄ : ℝ, CornerGLContinuity.FamilyOrdersSmallPrimeBound Fm C₄

  lemmaOrdersPartTwo : CornerGLContinuity.FamilyOrdersLargePrimeBound Fm

  p6G : Ev Fm fun x i => FormalGroupSystem.RamifiedSublatticeVolumeOfAdmissible (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK

  orders : ∃ C₄ : ℝ, CornerGLContinuity.FamilyGlobalOrderEstimate Fm C₄

  gatE : Ev Fm fun x i => TrivialStabiliserFiniteClasses (Fm.D x i)

  gatY : Ev Fm fun x i => OperatorsPreserveLattices (Fm.D x i)

  lpVV : Adm6F Fm → Adm7F Fm →
    Ev Fm fun x i => CornerGLContinuity.OrbitLatticeBounds (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK

  weyl : Ev Fm fun x i => Joints.WeylSandwichG (Fm.D x i)

  expB : Ev Fm fun x i => Joints.ExpBoundG (Fm.D x i) (Fm.Gx x i)

  unitBoundAtTwistedPlaces : AdmUF Fm

  svc1 : Ev Fm fun x i => CornerGLContinuity.ServiceLowerValuation (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK

theorem family_sixth_bound_of_nonneg {eps : ℝ} (Fm : FamP eps) (hCe : 0 ≤ Fm.cX.Ce) (hf : Fam0 Fm) : Adm9F Fm := by
  obtain ⟨x0, h⟩ := (hf.weyl.and hf.expB).and (Ev.x1 Fm)
  exact ⟨Fm.cX.Ce, hCe, x0, fun x hx i => Joints.weyl_sandwich_of_factors _ _ _ Fm.cX.Ce hCe (Fm.ex x (h x hx i).2 i).ep_def
    (h x hx i).1.1 (h x hx i).1.2⟩

theorem family_growth_bound_of_sizes {eps : ℝ} (Fm : FamP eps) (hCe : 0 ≤ Fm.cX.Ce) (hf : Fam0 Fm) (h6 : Adm6F Fm) (h7 : Adm7F Fm) :
    FamilyFirstGrowthBound Fm := by
  obtain ⟨Ce, _, h9⟩ := family_sixth_bound_of_nonneg Fm hCe hf
  obtain ⟨x0, h⟩ := ((((((((hf.unitBoundAtTwistedPlaces.and hf.gatE).and hf.p6G).and hf.gatY).and (hf.lpVV h6 h7)).and h9).and
    (eventually_large_scale_bound Fm)).and (Ev.x1 Fm)).and hf.svc1)
  refine ⟨x0, fun x hx i => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hU, hE⟩, hS⟩, hY⟩, hLP⟩, h9⟩, hB⟩, hx1⟩, hS1⟩ := h x hx i
  exact TopChoiceBounds.gluing_statement_of_proof _ _ _ (TopChoiceBounds.gluing_statement_holds Fm.GK (Fm.Gx x i) (Fm.Gy x i)
    ⟨hU, stability_of_trivial_stabilisers hE, service_statement_of_stability _ _ _ hS hE hY, hLP, TopChoiceBounds.sandwich_of_exponent_clause _ Ce (Fm.gatT x i) h9,
      saturated_ramified_lattice _ (Fm.ex x hx1 i).cmp (Fm.ex x hx1 i).lat.vram, hB, hS1⟩).1

theorem family_admitted_bounds {eps : ℝ} (Fm : FamP eps) (hCe : 0 ≤ Fm.cX.Ce) (hCN : CornerGLContinuity.FamilyWindowLogBound Fm) (hf : Fam0 Fm) (h6 : Adm6F Fm)
    (h7 : Adm7F Fm) :
    Adm1F Fm ∧ Adm3F Fm ∧ Adm4F Fm ∧ Adm9F Fm ∧ AdmUF Fm ∧ FamilyFirstGrowthBound Fm := by
  obtain ⟨C₄, hO⟩ := hf.orders
  exact ⟨family_first_lemma Fm, family_orders_first_part Fm C₄ (hf.p33i C₄) hO, family_orders_bound_of_lemma Fm hf.lemmaOrdersPartTwo hCN, family_sixth_bound_of_nonneg Fm hCe hf, hf.unitBoundAtTwistedPlaces,
    family_growth_bound_of_sizes Fm hCe hf h6 h7⟩

def LocalSystemCompletion (X : Inst D L) (Y : LatInst D) (low : D.what₂.Word → D.what₂.places.Pl → ℝ) : Prop :=
  ∀ hT : GatTies D, LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    ∃ (_ : Fact (D.what₂.places.resChar w).Prime) (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _)
      (dG_spec : _) (om : _) (Y5 : FormalGroupSystem.Pend (FormalGroupSystem.Sys.mk (D.gat u w hg) (Y.Fl u w hg) (Y.Lv u w hg)
        (Y.Ch u w hg) std vp unif eO eO_spec dG dG_spec om)),
      FormalGroupSystem.admitted D _ Y5 ∧
      ∃ Fn : Fin (D.gat u w hg).P.nV → ℕ → ℝ,
        (∀ v, v ∉ (reps X (D.what₂.places.resChar w)).image (Y.vOf u w hg) → ∀ j < D.R.m, Y5.LowAt j v (Fn v (j + 1))) ∧
        low u w ≤ (∑ j ∈ Finset.Icc 1 D.R.m,
          ∑ v ∈ Finset.univ \ (reps X (D.what₂.places.resChar w)).image (Y.vOf u w hg), Fn v j) -
            ∑ j ∈ Finset.range D.R.m, (dG j : ℝ)

def LargePrimeUnitNumbers (X : Inst D L) (K : Consts) : Prop :=
  ∀ w : D.what₂.places.Pl, Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) < 1 →
    ∀ t0 ∈ reps X (D.what₂.places.resChar w), ∀ j ∈ SizeData₂.lifts D,
      gU X K (aL L) (bL L) (D.what₂.places.resChar w) j t0 - Pr X K (bL L) (D.what₂.places.resChar w) j t0 ≤ 0 ∧
        g0 X K (aL L) (bL L) (D.what₂.places.resChar w) j t0 ≤ 0

open Classical in

theorem unit_bound_low_of_local_system (X : Inst D L) (Y : LatInst D) (K : Consts) (low : D.what₂.Word → D.what₂.places.Pl → ℝ)
    (hS : FormalGroupSystem.Stmt D) (h5 : LocalSystemCompletion X Y low)
    (hNum : FormalGroupSystem.SmallResidueCharComparison D L X Y K) (hBig : LargePrimeUnitNumbers X K) : AuxBlock8.UnitBoundLowTerm D L X Y K low := by
  refine Joints.lower_bound_of_large_residue D L X Y K low (fun hT hLT u w hg => ?_) hNum hBig
  obtain ⟨hF, std, vp, unif, eO, eO_spec, dG, dG_spec, om, Y5, hA, Fn, h1, h2⟩ := h5 hT hLT u w hg
  have hP := hS.1 _ _ Y5 hA
  have hfr : IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf :=
    ((D.gat u w hg).P.setting (Y.vOf u w hg 0)).frac_O
  exact ⟨hF, std, vp, unif, eO, eO_spec, dG, dG_spec, om, Y5, hP.2.2.2.2.2.1, hA.2.2.2.2.2.2.2.2.2.2.2.2,
    hP.2.2.2.2.2.2.2.2.2.2, IsFractionRing.injective _ _, Fn, h1, h2⟩

theorem windows_of (K : Consts) (P : ParameterChoice' D L) (hLa : La K L.sc = L.LaG) (p : ℕ) (t0 : HH D) :
    ∀ s ∈ topsPos D p t0, wPos D p t0 (aL L) s ∈ winA D L.sc ∧ wPos D p t0 (bL L) s ∈ winB D K L.sc := by
  intro s hs
  have hT : t0 + (s : ℕ) • hP D p ∈ D.host.TT := (Finset.mem_filter.1 hs).2
  have ha : wPos D p t0 (aL L) s = L.aT ⟨_, hT⟩ := by unfold wPos aL; rw [dif_pos hT]
  have hb : wPos D p t0 (bL L) s = L.bT ⟨_, hT⟩ := by unfold wPos bL; rw [dif_pos hT]
  rw [ha, hb]
  obtain ⟨a1, a2⟩ := L.aT_win ⟨_, hT⟩
  have b1 := L.bT_ge ⟨_, hT⟩
  have b2 := P.bT_le ⟨_, hT⟩
  refine ⟨Finset.mem_Icc.2 ⟨Int.ceil_le.2 a1, Int.le_floor.2 a2⟩, Finset.mem_Icc.2 ⟨Int.ceil_le.2 b1, Int.le_floor.2 ?_⟩⟩
  rw [hLa]
  exact b2

theorem La_nonneg {K : Consts} (h : 0 ≤ K.La) (s : Scale) : 0 ≤ La K s := by
  unfold La
  exact mul_nonneg (mul_nonneg h (by positivity)) (Real.log_nonneg (sc_one_lt_a s).le)

structure Fam1 {eps : ℝ} (Fm : FamP eps) : Prop where

  p6G : Ev Fm fun x i => FormalGroupSystem.RamifiedSublatticeVolumeOfAdmissible (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK

  p05 : FormalGroupSystem.KudlaFamilyStatement Fm

  gatE : Ev Fm fun x i => TrivialStabiliserFiniteClasses (Fm.D x i)

  gatY : Ev Fm fun x i => OperatorsPreserveLattices (Fm.D x i)

  stdSub : Ev Fm fun x i => Joints.StdSubAt (Fm.D x i)

  lpBC : LPBaseChange

  hypI : Ev Fm fun x i => Joints.HypIAt (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Fm.GK

  hypII : Ev Fm fun x i => Joints.HypIIAt (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Fm.GK

  model : Ev Fm fun x i => Joints.ModelSandwichG (Fm.D x i)

  localSystemLowTerm : Ev Fm fun x i => LocalSystemCompletion (Fm.Gx x i) (Fm.Gy x i) (AuxBlock8.lowU (Fm.D x i))

  localSystemSizeLowTerm : Ev Fm fun x i => LocalSystemCompletion (Fm.Gx x i) (Fm.Gy x i) (lowFE (Fm.L x i))

def NumCmpF {eps : ℝ} (Fm : FamP eps) : Prop :=
  Ev Fm fun x i => FormalGroupSystem.SmallResidueCharComparison (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK

theorem family_unit_bound_of_comparison {eps : ℝ} (Fm : FamP eps) (hf : Fam1 Fm) (hNum : NumCmpF Fm) (h1 : 1 ≤ Fm.GK.Pr1)
    (h2 : 1 ≤ Fm.GK.CN) : AdmUF Fm := by
  obtain ⟨x0, h⟩ := (hf.localSystemLowTerm.and hNum).and (Ev.x1 Fm)
  exact ⟨x0, fun x hx i => unit_bound_low_of_local_system _ _ _ _ (hf.p05 x i) (h x hx i).1.1 (h x hx i).1.2
    (TopChoiceBounds.hLarge_proved _ _ Fm.GK_nonneg h1 (Fm.params x (h x hx i).2 i))⟩

theorem family_lattice_bound_low_term {eps : ℝ} (Fm : FamP eps) (hf : Fam1 Fm) (hNum : NumCmpF Fm) (h1 : 1 ≤ Fm.GK.Pr1) :
    Ev Fm fun x i => CornerGLContinuity.ServiceLowerValuation (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK := by
  obtain ⟨x0, h⟩ := (hf.localSystemSizeLowTerm.and hNum).and (Ev.x1 Fm)
  exact ⟨x0, fun x hx i => TopChoiceBounds.bg_NP_of_Ulow _ _ _ _ (unit_bound_low_of_local_system _ _ _ _ (hf.p05 x i) (h x hx i).1.1 (h x hx i).1.2
    (TopChoiceBounds.hLarge_proved _ _ Fm.GK_nonneg h1 (Fm.params x (h x hx i).2 i)))⟩

theorem family_bounds_of_local_systems {eps : ℝ} (Fm : FamP eps) (hf : Fam1 Fm) (hNum : NumCmpF Fm) (h1 : 1 ≤ Fm.GK.Pr1)
    (h2 : 1 ≤ Fm.GK.CN) (hCe : 1 ≤ Fm.cX.Ce) (hLa : 0 < Fm.GK.La) (hCb : Ev Fm fun x i => CbLarge Fm.GK (Fm.L x i).sc) :
    Fam0 Fm := by
  obtain ⟨C₅, h59⟩ := UnusedSlot33.field_lemmas_except_seven
  obtain ⟨xm, hm⟩ := hf.model
  obtain ⟨x1, hx1⟩ := Ev.x1 Fm
  exact ⟨TopChoiceBounds.family_order_bound_holds Fm, TopChoiceBounds.family_band_ratio_holds Fm, hf.p6G,
    ⟨100, fun x i => (h59 (Fm.D x i) (Fm.L x i).sc).2.2.2.1⟩, hf.gatE, hf.gatY,
    fun h6 h7 => by
      obtain ⟨x0, h⟩ := ((((h6.and h7).and hf.stdSub).and hf.hypI).and hf.hypII).and hCb
      exact ⟨x0, fun x hx i => Joints.linear_programming_input_of_hypotheses _ _ _ _ _ (h x hx i).1.1.1.1.1 (h x hx i).1.1.1.1.2
        (h x hx i).1.1.1.2 hf.lpBC (h x hx i).1.1.2 (h x hx i).1.2
        (rho_le_rhoB _ _ _ Fm.GK_nonneg.2.1 (La_nonneg Fm.GK_nonneg.1 _) (h x hx i).2)⟩,
    ⟨xm, fun x hx i => Joints.weylSandwich_of_model _ (hm x hx i)⟩,
    ⟨x1, fun x hx i => Joints.expBound_of _ _ _ Fm.cX.Ce hCe (Fm.ex x (hx1 x hx i) i).ep_def (Fm.params x (hx1 x hx i) i)
      (Fm.gatT x i)⟩,
    family_unit_bound_of_comparison Fm hf hNum h1 h2, family_lattice_bound_low_term Fm hf hNum h1⟩

end Rest

theorem linkG_fam {eps : ℝ} (Fm : FamP eps) (hStmt : AuxBlock8.KudlaFamilyStatement Fm) (h14 : SecondTheoremAtFamily Fm) (h13 : FirstTheoremAtFamily Fm)
    (hLa : 0 < Fm.GK.La) (hCe : 0 ≤ Fm.cX.Ce) (hf : Fam0 Fm) (h2 : Adm2F Fm) (hd : NPDescF Fm) (hCN : CornerGLContinuity.FamilyWindowLogBound Fm) :
    LinkG Fm := by
  obtain ⟨C, hC0, a1, a2, a3, a4, a5, a6, hp14⟩ := h14
  obtain ⟨CH, C', b0, b1, b2, b3, b4, b5, b6, hp13⟩ := h13
  have h6 := family_second_bound_of_theorem Fm C hC0 a1 a2 a3 a4 a5 a6 hp14
  have h7 := family_kappa_bound Fm (kapIDefF Fm)
  have h8 := family_first_bound_of_theorem Fm CH C' (kapIDefF Fm) b0 b1 b2 b3 b4 b5 b6 hp13
  obtain ⟨h1, h3, h4, h9, hU, hG1⟩ := family_admitted_bounds Fm hCe hCN hf h6 h7
  exact linkG_of Fm (family_statement_of_general Fm hStmt) ⟨h1, h2, h3, h4, family_sizes_bound Fm hLa, h6, h7, h8, h9, hU, hG1, hd⟩

theorem second_theorem_closed_form (𝒞 : FamClass) (h14 : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ D : D7, tableLineDegreeFive.aux₃ D C₀) :
    Closed 𝒞 fun Fm _ => SecondTheoremAtFamily Fm := by
  obtain ⟨C₀, hC0, h⟩ := h14
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => C₀, fun _ => C₀⟩, fun Fm CH _ hL => ?_⟩⟩
  have hmid : ∀ c ∈ Fm.cMid CH, C₀ ≤ c := hL.2.2.1
  have hlast : ∀ c ∈ Fm.cLast, C₀ ≤ c := hL.2.2.2
  exact ⟨C₀, hC0, hlast _ (by simp [FamP.cLast]), hlast _ (by simp [FamP.cLast]),
    hmid _ (by simp [FamP.cMid]), hlast _ (by simp [FamP.cLast]), hlast _ (by simp [FamP.cLast]),
    hlast _ (by simp [FamP.cLast]), ⟨0, fun x _ i => h (Fm.D x i)⟩⟩

def lmax (f : ℝ → ℝ) (l : List ℝ) : ℝ := (l.map f).foldr max 0

theorem le_lmax (f : ℝ → ℝ) {l : List ℝ} {c : ℝ} (h : c ∈ l) : f c ≤ lmax f l := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    simp only [lmax, List.map_cons, List.foldr_cons] at *
    rcases List.mem_cons.1 h with rfl | h'
    · exact le_max_left _ _
    · exact le_trans (ih h') (le_max_right _ _)

theorem first_theorem_closed_form (𝒞 : FamClass)
    (h13 : ∃ (T0 : ℝ) (T2 C : ℝ → ℝ), 0 < T0 ∧ ∀ C₀ : ℝ, T0 ≤ C₀ → 0 < T2 C₀ ∧ 0 < C C₀ ∧ ∀ CH : ℝ, T2 C₀ ≤ CH →
      ∀ D : D7, flipOneThree.Conclusion2 D C₀ CH (C C₀)) :
    Closed 𝒞 fun Fm _ => FirstTheoremAtFamily Fm := by
  obtain ⟨T0, T2, C, _, h⟩ := h13
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => T0,
    fun l => lmax (fun c => max (2 * T2 c) (2 * C c)) l⟩, fun Fm CH _ hL => ?_⟩⟩
  have hLa : T0 ≤ Fm.GK.La := hL.2.2.1 _ (by simp [FamP.cMid])
  have hmem : Fm.GK.La ∈ Fm.cOut ++ Fm.cMid CH := List.mem_append_right _ (by simp [FamP.cMid])
  have hlast : ∀ c ∈ Fm.cLast, max (2 * T2 Fm.GK.La) (2 * C Fm.GK.La) ≤ c := fun c hc =>
    le_trans (le_lmax (fun c => max (2 * T2 c) (2 * C c)) hmem) (hL.2.2.2 c hc)
  obtain ⟨hT2, hC, hp⟩ := h _ hLa
  have hA : ∀ c ∈ Fm.cLast, 2 * T2 Fm.GK.La ≤ c := fun c hc => le_trans (le_max_left _ _) (hlast c hc)
  have hB : ∀ c ∈ Fm.cLast, 2 * C Fm.GK.La ≤ c := fun c hc => le_trans (le_max_right _ _) (hlast c hc)
  have hkI := hA Fm.GK.kI (by simp [FamP.cLast])
  have hDI := hA Fm.GK.DI (by simp [FamP.cLast])
  have hrho := hA Fm.GK.rho (by simp [FamP.cLast])
  have ht1 := hB Fm.GK.kappaThresholdOne (by simp [FamP.cLast])
  have ht2 := hB Fm.GK.kappaThresholdTwo (by simp [FamP.cLast])
  exact ⟨T2 Fm.GK.La, C Fm.GK.La, hT2.le, by linarith, by linarith, hrho, hC.le, ht1, by linarith,
    fun x i => hp _ le_rfl _⟩

theorem signs_closed (𝒞 : FamClass) : Closed 𝒞 fun Fm _ => 0 < Fm.GK.La ∧ 0 ≤ Fm.cX.Ce := by
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 1, fun _ => 0⟩, fun Fm CH _ hL => ?_⟩⟩
  have hmid : ∀ c ∈ Fm.cMid CH, (1 : ℝ) ≤ c := hL.2.2.1
  have h1 := hmid Fm.GK.La (by simp [FamP.cMid])
  have h2 : Fm.cX.Ce = 1 := Fm.fixed.2.2.2.1
  exact ⟨by linarith, by linarith⟩

theorem linkG_top (𝒞 : FamClass) (h70 : ExtremalProjectorTools) (h6 : Loc6) (h8 : Loc8)
    (h69 : Closed 𝒞 fun Fm _ => AuxBlock8.KudlaFamilyStatement Fm) (hf : Closed 𝒞 fun Fm _ => Fam0 Fm)
    (h2 : Closed 𝒞 fun Fm _ => Adm2F Fm) (hd : Closed 𝒞 fun Fm _ => NPDescF Fm) :
    Closed 𝒞 fun Fm _ => LinkG Fm :=
  (((((((h69.and (second_theorem_closed_form 𝒞 (second_theorem_absolute_constant h70 h6))).and (first_theorem_closed_form 𝒞 (first_theorem_threshold_functions h70 (loc8All_of h70 h6 h8)))).and (signs_closed 𝒞)).and
    hf).and h2).and hd).and (TopChoiceBounds.family_log_bound_closed 𝒞)).imp fun Fm _ _ h =>
    linkG_fam Fm h.1.1.1.1.1.1.1 h.1.1.1.1.1.1.2 h.1.1.1.1.1.2 h.1.1.1.1.2.1 h.1.1.1.1.2.2 h.1.1.1.2 h.1.1.2 h.1.2 h.2

theorem rG_lt_k {eps : ℝ} (Fm : FamP eps) : Ev Fm fun x i => rG (Fm.L x i).sc < (Fm.D x i).R.k := by
  obtain ⟨x1, hx1⟩ := Ev.x1 Fm
  refine ⟨max x1 (32 / eps + 66), fun x hx i => ?_⟩
  have hxx1 := hx1 x (le_trans (le_max_left _ _) hx) i
  have he : 0 < eps := by rw [← Fm.L_eps x i]; exact (Fm.L x i).sc.eps_pos
  have hxx := Fm.L_x x i hxx1
  have hee := Fm.L_eps x i
  have hge : 32 / eps + 66 ≤ x := le_trans (le_max_right _ _) hx
  have hr : (rG (Fm.L x i).sc : ℝ) < 32 / eps + 66 := by
    unfold rG KG hG
    rw [hee]
    have h0 : 0 ≤ 8 * ((2 + 8 * eps) + 2) / eps := by positivity
    have h1 := Nat.ceil_lt_add_one h0
    have h2 : 8 * ((2 + 8 * eps) + 2) / eps = 32 / eps + 64 := by field_simp; ring
    push_cast
    linarith
  have hk := (Fm.sizes x hxx1 i).2.2.1.1
  have hx1' : 1 ≤ (Fm.L x i).sc.x := (Fm.L x i).sc.one_lt_alt.le
  have hexp : (1 : ℝ) ≤ 9 / 2 + 10 * (Fm.L x i).sc.eps - szTh (Fm.L x i) := by
    unfold szTh
    have := (Fm.L x i).sc.eps_pos
    have := (Fm.L x i).sc.eps_lt
    linarith
  have h3 : (Fm.L x i).sc.x ≤ (Fm.L x i).sc.x ^ (9 / 2 + 10 * (Fm.L x i).sc.eps - szTh (Fm.L x i)) := by
    calc (Fm.L x i).sc.x = (Fm.L x i).sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1' hexp
  have hge' : 32 / eps + 66 ≤ (Fm.L x i).sc.x := by rw [hxx]; exact hge
  have h4 : (rG (Fm.L x i).sc : ℝ) < ((Fm.D x i).R.k : ℝ) := by linarith
  exact_mod_cast h4

theorem numCmpF_fixed {eps : ℝ} (Fm : FamP eps) : NumCmpF Fm := by
  obtain ⟨x0, hx0⟩ := ((Ev.x1 Fm).and (rG_lt_k Fm)).and ⟨2, fun x hx _ => hx⟩
  exact ⟨x0, fun x hx i => FormalGroupSystem.Pf.numeric_comparison_of_constants _ _ _ _ Fm.GK Fm.fixed.2.1.ge Fm.fixed.2.2.1.ge Fm.fixed.1.ge
    (hx0 x hx i).1.2 (by rw [Fm.L_x x i (hx0 x hx i).1.1]; exact (hx0 x hx i).2) (Fm.sizes x (hx0 x hx i).1.1 i)⟩

theorem num_closed (𝒞 : FamClass) (_hN : FormalGroupSystem.NumericalComparisonUniform) : Closed 𝒞 fun Fm _ => NumCmpF Fm :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => numCmpF_fixed Fm⟩⟩

theorem cb_closed (𝒞 : FamClass) : Closed 𝒞 fun Fm _ => Ev Fm fun x i => CbLarge Fm.GK (Fm.L x i).sc := by
  classical
  refine ⟨1 / 104, by norm_num, fun eps heps hle => ?_⟩
  by_cases hD : Nonempty D7
  · obtain ⟨D0⟩ := hD
    obtain ⟨Ce, hCe, hC⟩ := (TopChoiceBounds.master_orbit_sizes_hold D0).1 (⌈8 * ((2 + 8 * eps) + 2) / eps⌉₊ + 1) (2 + 8 * eps)
      (by omega) (by linarith)
    refine ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => Ce⟩, fun Fm CH _ hL => ?_⟩
    have hCN : Ce ≤ Fm.GK.CN := hL.2.2.2 _ (by simp [FamP.cLast])
    obtain ⟨x1, hx1⟩ := Ev.x1 Fm
    refine ⟨max x1 3, fun x hx i => ?_⟩
    have hxx1 := hx1 x (le_trans (le_max_left _ _) hx) i
    have hx3 : (3 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
    have hxx := Fm.L_x x i hxx1
    have hee := Fm.L_eps x i
    have hd0 : 0 < (Fm.L x i).sc.delta1 := sc_delta1_pos _
    have hd1 : (Fm.L x i).sc.delta1 ≤ 1 := by
      unfold Scale.delta1
      apply Real.rpow_le_one_of_one_le_of_nonpos (Fm.L x i).sc.one_lt_alt.le
      have := (Fm.L x i).sc.eps_pos
      linarith
    have hr : rG (Fm.L x i).sc = ⌈8 * ((2 + 8 * eps) + 2) / eps⌉₊ + 1 := by unfold rG KG hG; rw [hee]
    have hh : hG (Fm.L x i).sc = 2 + 8 * eps := by unfold hG; rw [hee]
    obtain ⟨_, hNb, _⟩ := hC (Fm.L x i).sc.delta1 (Fm.L x i).sc.x hd0 hd1 (by rw [hxx]; exact hx3)
    rw [← hr, ← hh] at hNb
    unfold CbLarge
    have hl : 0 ≤ Real.log (Fm.L x i).sc.x := Real.log_nonneg (Fm.L x i).sc.one_lt_alt.le
    exact le_trans hNb (mul_le_mul_of_nonneg_right hCN hl)
  · refine ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ?_⟩
    obtain ⟨i0⟩ := Fm.Ix_zero
    exact absurd ⟨Fm.D 0 i0⟩ hD

theorem ones_closed (𝒞 : FamClass) : Closed 𝒞 fun Fm _ => 1 ≤ Fm.GK.Pr1 ∧ 1 ≤ Fm.GK.CN ∧ 1 ≤ Fm.cX.Ce := by
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 1⟩, fun Fm CH _ hL => ?_⟩⟩
  exact ⟨Fm.fixed.1.ge, hL.2.2.2 _ (by simp [FamP.cLast]), Fm.fixed.2.2.2.1.ge⟩

theorem link_of_closed_families (𝒞 : FamClass) (h70 : ExtremalProjectorTools) (h6 : Loc6) (h8 : Loc8) (hN : FormalGroupSystem.NumericalComparisonUniform)
    (h69 : Closed 𝒞 fun Fm _ => AuxBlock8.KudlaFamilyStatement Fm) (hf : Closed 𝒞 fun Fm _ => Fam1 Fm)
    (h2 : Closed 𝒞 fun Fm _ => Adm2F Fm) (hd : Closed 𝒞 fun Fm _ => NPDescF Fm) :
    Closed 𝒞 fun Fm _ => LinkG Fm :=
  linkG_top 𝒞 h70 h6 h8 h69 (((((hf.and (num_closed 𝒞 hN)).and (ones_closed 𝒞)).and (signs_closed 𝒞)).and (cb_closed 𝒞)).imp
    fun Fm _ _ h => family_bounds_of_local_systems Fm h.1.1.1.1 h.1.1.1.2 h.1.1.2.1 h.1.1.2.2.1 h.1.1.2.2.2 h.1.2.1 h.2) h2 hd

end Formalism.MainNotions.G

end
