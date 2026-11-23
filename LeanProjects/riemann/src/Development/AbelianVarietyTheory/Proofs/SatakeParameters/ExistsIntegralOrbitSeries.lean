import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionHypothesesOfLevelOne
import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.OneLetterJetKernel

noncomputable section
open scoped BigOperators

namespace GlobalTheory.KerStd

namespace CofactorConverse

open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog ZV)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog mvExp_add)
open Formalism.L2.Th1.D
open Formalism.L2.Th1.D.Pair
open Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel (pXY zXY_eq dual2 subst_comb)
open MvPowerSeries

section Alg

variable {K0 K : Type} [Field K0] [Field K] {ι : Type} {d N0 N1 : ℕ} [NeZero d]

def rho (a : Fin N0) (b : Fin N1) (x : Bool × ι) : MvPowerSeries (Bool × ι × Fin N0 × Fin N1) K :=
  X (x.1, x.2, a, b)

theorem cc_rho (a : Fin N0) (b : Fin N1) (x : Bool × ι) :
    constantCoeff (rho (K := K) a b x) = 0 := constantCoeff_X _

theorem hasSubst_rho [Finite ι] (a : Fin N0) (b : Fin N1) : HasSubst (rho (K := K) (ι := ι) a b) :=
  hasSubst_of_constantCoeff_zero (cc_rho a b)

def linP (j : K0 →+* K) (σ : K0 →+* K0) (om oms : ι → K0) (a : Fin N0) (b : Fin N1) (x : Bool × ι) :
    MvPowerSeries (ZV d N0 N1) K :=
  ∑ s : ZMod d, C (j (pXY σ om oms x s)) * X (s, a, b)

theorem xOfZ_eq (l : ℕ) (j : K0 →+* K) (σ : K0 →+* K0) (om oms : ι → K0) (a : Fin N0) (b : Fin N1)
    (x : Bool × ι) :
    xOfZ (d := d) l j σ om oms (x.1, x.2, a, b) =
      PowerSeries.subst (linP (d := d) j σ om oms a b x) (expF K l) := by
  obtain ⟨c, r⟩ := x
  unfold xOfZ linP
  congr 1
  cases c
  · simp only [if_true]
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold pXY
    by_cases hs : s.val % 2 = 0 <;> simp [hs]
  · simp only [Bool.true_eq_false, if_false]
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold pXY
    by_cases hs : s.val % 2 = 0 <;> simp [hs]

theorem cc_linP (j : K0 →+* K) (σ : K0 →+* K0) (om oms : ι → K0) (a : Fin N0) (b : Fin N1)
    (x : Bool × ι) : constantCoeff (linP (d := d) j σ om oms a b x) = 0 := by
  unfold linP
  rw [map_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  simp

theorem cc_xOfZ {l : ℕ} (hl : 2 ≤ l) (j : K0 →+* K) (σ : K0 →+* K0) (om oms : ι → K0)
    (x : Bool × ι × Fin N0 × Fin N1) :
    constantCoeff (xOfZ (d := d) l j σ om oms x) = 0 := by
  obtain ⟨c, r, a, b⟩ := x
  rw [xOfZ_eq l j σ om oms a b (c, r)]
  exact cc_ps (cc_linP j σ om oms a b _) (expSpec K l hl).1

theorem log_xOfZ {l : ℕ} (hl : 2 ≤ l) (j : K0 →+* K) (σ : K0 →+* K0) (om oms : ι → K0) (a : Fin N0)
    (b : Fin N1) (x : Bool × ι) :
    PowerSeries.subst (xOfZ (d := d) l j σ om oms (x.1, x.2, a, b)) (lgF K l) =
      linP (d := d) j σ om oms a b x := by
  rw [xOfZ_eq l j σ om oms a b x, ps_comp (cc_linP j σ om oms a b x) (expSpec K l hl).1,
    (expSpec K l hl).2.1,
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero (cc_linP j σ om oms a b x))]

theorem map_inVar {τ : Type} (j : K0 →+* K) (x : τ) (f : PowerSeries K0) :
    map j (at1 x f) = at1 x (PowerSeries.map j f) := by
  unfold at1
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.X x), map_X]

theorem map_zXY [Fintype ι] (l : ℕ) (j : K0 →+* K) (σ : K0 →+* K0) (om oms : ι → K0) (s : ZMod d) :
    map j (zXY l σ om oms s) = ∑ x : Bool × ι, C (j (mXY σ om oms s x)) * at1 x (lgF K l) := by
  rw [zXY_eq, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, map_C, map_inVar, BiextensionSums.map_lgF']

theorem map_letLog (l : ℕ) (j : K0 →+* K) (s : ZMod d) :
    map j (letLog (K := K0) l s) = letLog (K := K) l s := by
  ext n
  rw [coeff_map]
  show j (letLog (K := K0) l s n) = letLog (K := K) l s n
  unfold letLog
  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp

def embAB (d : ℕ) (a : Fin N0) (b : Fin N1) : ZMod d ↪ ZV d N0 N1 :=
  ⟨fun s => (s, a, b), fun _ _ h => (Prod.ext_iff.1 h).1⟩

theorem entLog_eq_letLog (l : ℕ) (s : ZMod d) (a : Fin N0) (b : Fin N1) :
    entLog (K := K) l ((s, a, b) : ZV d N0 N1) =
      subst (fun s' : ZMod d => (X (s', a, b) : MvPowerSeries (ZV d N0 N1) K)) (letLog (K := K) l s) := by
  have e : subst (fun s' : ZMod d => (X (s', a, b) : MvPowerSeries (ZV d N0 N1) K)) (letLog (K := K) l s) =
      rename (embAB d a b) (letLog (K := K) l s) := by
    rw [rename_eq_subst]
    rfl
  rw [e]
  ext n
  by_cases hn : ∃ m, Finsupp.embDomain (embAB d a b) m = n
  · obtain ⟨m, rfl⟩ := hn
    rw [coeff_embDomain_rename]
    show entLog (K := K) l ((s, a, b) : ZV d N0 N1) _ = letLog (K := K) l s m
    have hdeg : (Finsupp.embDomain (embAB d a b) m).degree = m.degree := by
      show (Finsupp.embDomain (embAB d a b) m).sum (fun _ k => k) = m.sum (fun _ k => k)
      rw [Finsupp.sum_embDomain]
    unfold entLog letLog
    rw [hdeg]
    refine Finset.sum_congr rfl fun e _ => ?_
    have hs : (Finsupp.single ((s - 2 * (e : ZMod d), a, b) : ZV d N0 N1) ((l ^ 2) ^ e)) =
        Finsupp.embDomain (embAB d a b) (Finsupp.single (s - 2 * (e : ZMod d)) ((l ^ 2) ^ e)) := by
      rw [Finsupp.embDomain_single]
      rfl
    have hiff : (Finsupp.embDomain (embAB d a b) m =
          Finsupp.single ((s - 2 * (e : ZMod d), a, b) : ZV d N0 N1) ((l ^ 2) ^ e)) ↔
        m = Finsupp.single (s - 2 * (e : ZMod d)) ((l ^ 2) ^ e) := by
      rw [hs, Finsupp.embDomain_inj]
    simp only [hiff]
  · rw [coeff_rename_eq_zero]
    · show entLog (K := K) l ((s, a, b) : ZV d N0 N1) n = 0
      unfold entLog
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [if_neg]
      intro h
      refine hn ⟨Finsupp.single (s - 2 * (e : ZMod d)) ((l ^ 2) ^ e), ?_⟩
      rw [h, Finsupp.embDomain_single]
      rfl
    · rintro ⟨m, rfl⟩
      exact hn ⟨m, Finsupp.embDomain_eq_mapDomain _ _⟩

theorem subst_xOfZ_zXY [Fintype ι] [DecidableEq ι] {l : ℕ} (hl : 2 ≤ l) (hd : Even d) (j : K0 →+* K)
    (σ : K0 →+* K0) {om oms : ι → K0} (hfix : ∀ r, σ^[d] (om r) = om r ∧ σ^[d] (oms r) = oms r)
    (hT : TrDual d σ om oms) (s : ZMod d) (a : Fin N0) (b : Fin N1) :
    subst (xOfZ (d := d) (N0 := N0) (N1 := N1) l j σ om oms) (subst (rho (K := K) a b) (map j (zXY l σ om oms s))) =
      X (s, a, b) := by
  have hx : HasSubst (xOfZ (d := d) (N0 := N0) (N1 := N1) l j σ om oms) :=
    hasSubst_of_constantCoeff_zero (cc_xOfZ hl j σ om oms)
  have hρ := hasSubst_rho (K := K) (ι := ι) a b
  rw [subst_comp_subst_apply hρ hx]
  have hψ : (fun x => subst (xOfZ (d := d) (N0 := N0) (N1 := N1) l j σ om oms) (rho (K := K) a b x)) =
      fun x : Bool × ι => xOfZ (d := d) (N0 := N0) (N1 := N1) l j σ om oms (x.1, x.2, a, b) :=
    funext fun x => subst_X hx _
  rw [hψ]
  have hs : HasSubst fun x : Bool × ι => xOfZ (d := d) (N0 := N0) (N1 := N1) l j σ om oms (x.1, x.2, a, b) :=
    hasSubst_of_constantCoeff_zero fun x => cc_xOfZ hl j σ om oms _
  rw [map_zXY, subst_comb hs]
  simp only [subst_single_var hs, log_xOfZ hl j σ om oms a b]
  unfold linP
  have e : (∑ x : Bool × ι, C (j (mXY σ om oms s x)) *
        ∑ s' : ZMod d, C (j (pXY σ om oms x s')) * (X (s', a, b) : MvPowerSeries (ZV d N0 N1) K)) =
      ∑ s' : ZMod d, C (j (∑ x : Bool × ι, mXY σ om oms s x * pXY σ om oms x s')) *
        (X (s', a, b) : MvPowerSeries (ZV d N0 N1) K) := by
    simp only [Finset.mul_sum, map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun s' _ => ?_
    rw [map_mul, map_mul, mul_assoc]
  rw [e]
  simp only [dual2 hd σ hfix hT]
  rw [Finset.sum_eq_single s]
  · simp
  · intro y _ hy
    rw [if_neg (fun h => hy h.symm), map_zero, map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ s) h

theorem sum_subst_rho_beXY [Fintype ι] (j : K0 →+* K) (be0 : MvPowerSeries (Fin 2) K0) :
    (∑ ab : Fin N0 × Fin N1, subst (rho ab.1 ab.2) (map j (beXY (ι := ι) be0))) =
      sumE (ι := ι) (N0 := N0) (N1 := N1) (map j be0) := by
  have h1 : ∀ ab : Fin N0 × Fin N1, subst (rho (K := K) (ι := ι) ab.1 ab.2) (map j (beXY (ι := ι) be0)) =
      ∑ r : ι, subst (fun c : Fin 2 => (X (if c = 0 then (false, r, ab) else (true, r, ab)) :
        MvPowerSeries (Bool × ι × Fin N0 × Fin N1) K)) (map j be0) := by
    intro ab
    have hρ := hasSubst_rho (K := K) (ι := ι) ab.1 ab.2
    unfold beXY
    rw [map_sum, subst_sum hρ]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_subst (hs2 (constantCoeff_X _) (constantCoeff_X _)),
      subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (by
        intro c; fin_cases c <;> simp)) hρ]
    congr 1
    funext c
    fin_cases c
    · simp [subst_X hρ, rho]
    · simp [subst_X hρ, rho]
  simp only [h1]
  unfold sumE
  rw [Fintype.sum_prod_type (f := fun e : ι × Fin N0 × Fin N1 => _), Finset.sum_comm]

end Alg

section Main

variable {K0 K : Type} [NormedField K0] [IsUltrametricDist K0] [CharZero K0] [NormedField K]
  [IsUltrametricDist K] [CharZero K]

theorem exists_cofactor (l d N0 N1 : ℕ) [NeZero d] (σ : K0 →+* K0) (j : K0 →+* K) (hU : UnrOK K0 l σ)
    (hj : ∀ a, ‖j a‖ = ‖a‖) (h2 : 2 ≤ d) (hd : Even d) (F : MvPowerSeries (Fin 2) K0) (hF : IsLawOfLog l F)
    (be0 : MvPowerSeries (Fin 2) K0) (hF1 : F1 F be0) (hF2 : F2 l σ be0)
    (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K0) (hOw : OwOK d σ om oms)
    (hTr : TrDual d σ om oms) (ζ : K0) (hζ : IsPrimitiveRoot ζ (l ^ d - 1))
    (Φ U : MvPowerSeries (ZV d N0 N1) K) (hUi : Integral U)
    (hΦ : subst (entLog (K := K) (d := d) (N0 := N0) (N1 := N1) l) Φ =
      U * subst (entLog (K := K) (d := d) (N0 := N0) (N1 := N1) l)
        (mvExp (-∑ ab : Fin N0 × Fin N1, subst (fun s : ZMod d =>
          (X (s, ab.1, ab.2) : MvPowerSeries (ZV d N0 N1) K)) (map j (beMean (d := d) l σ be0 om oms ζ))))) :
    ∃ U0 : MvPowerSeries (Bool × ι × Fin N0 × Fin N1) K, Integral U0 ∧
      Φ = thetaInZ (d := d) l j σ om oms (mvExp (-(sumE (map j be0))) * U0) := by
  have hl : 2 ≤ l := hU.1.two_le
  obtain ⟨T, -, hT, -, hlog, -, -, -, -⟩ := bMinus1 K0 l d σ hU h2 hd ι om oms hOw hTr
  have hS := (meanSimeq K0 l d σ hU h2 hd F hF be0 hF1 hF2 ι om oms hOw hTr ζ hζ).2
  have hTs : HasSubst T := hasSubst_of_constantCoeff_zero fun s => (hT s).1
  have hx : HasSubst (xOfZ (d := d) (N0 := N0) (N1 := N1) l j σ om oms) :=
    hasSubst_of_constantCoeff_zero (cc_xOfZ hl j σ om oms)
  have hfix := hOw.2

  obtain ⟨T', hT'⟩ : ∃ T' : ZV d N0 N1 → MvPowerSeries (Bool × ι × Fin N0 × Fin N1) K,
      ∀ v, T' v = subst (rho v.2.1 v.2.2) (map j (T v.1)) := ⟨_, fun _ => rfl⟩
  have hT0 : ∀ a b s, constantCoeff (subst (rho (K := K) (ι := ι) (N0 := N0) (N1 := N1) a b) (map j (T s))) = 0 :=
    fun a b s => constantCoeff_subst_eq_zero (hasSubst_rho a b) (cc_rho a b)
      (by rw [constantCoeff_map, (hT s).1, map_zero])
  have hT'0 : ∀ v, constantCoeff (T' v) = 0 := fun v => by rw [hT']; exact hT0 _ _ _
  have hT'i : ∀ v, Integral (T' v) := fun v => by
    rw [hT']
    exact Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' (cc_rho _ _) (fun x => KernelCokernelKilling.integral_X' _)
      (Formalism.DworkPowerSeriesWeights.Transfer.integral_map j hj (hT v.1).2)
  have hT's : HasSubst T' := hasSubst_of_constantCoeff_zero hT'0

  obtain ⟨g, hgdef⟩ : ∃ g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K,
      ∀ v, g v = subst (xOfZ (d := d) (N0 := N0) (N1 := N1) l j σ om oms) (T' v) := ⟨_, fun _ => rfl⟩
  have hg0 : ∀ v, constantCoeff (g v) = 0 := fun v => by
    rw [hgdef]
    exact constantCoeff_subst_eq_zero hx (cc_xOfZ hl j σ om oms) (hT'0 v)
  have hgs : HasSubst g := hasSubst_of_constantCoeff_zero hg0
  have hgE : ∀ v, subst g (entLog (K := K) l v) = X v := by
    rintro ⟨s, a, b⟩
    have hY : HasSubst (fun s' : ZMod d => (X (s', a, b) : MvPowerSeries (ZV d N0 N1) K)) :=
      hasSubst_of_constantCoeff_zero fun s' => constantCoeff_X _
    have hρ := hasSubst_rho (K := K) (ι := ι) a b
    have hmT : HasSubst fun s' => (map j (T s') : MvPowerSeries (Bool × ι) K) := hasSubst_of_constantCoeff_zero fun s' => by
      rw [constantCoeff_map, (hT s').1, map_zero]
    have hρT : HasSubst fun s' => subst (rho (K := K) (ι := ι) (N0 := N0) (N1 := N1) a b) (map j (T s')) :=
      hasSubst_of_constantCoeff_zero (hT0 a b)
    rw [entLog_eq_letLog, subst_comp_subst_apply hY hgs]
    have e : (fun s' : ZMod d => subst g (X (s', a, b) : MvPowerSeries (ZV d N0 N1) K)) =
        fun s' => subst (xOfZ (d := d) (N0 := N0) (N1 := N1) l j σ om oms)
          (subst (rho (K := K) a b) (map j (T s'))) := by
      funext s'
      rw [subst_X hgs, hgdef, hT']
    rw [e, ← subst_comp_subst_apply hρT hx, ← subst_comp_subst_apply hmT hρ, ← map_letLog l j,
      ← map_subst hTs, hlog]
    exact subst_xOfZ_zXY hl hd j σ hfix hTr s a b
  have hlg : HasSubst (entLog (K := K) (d := d) (N0 := N0) (N1 := N1) l) :=
    hasSubst_of_constantCoeff_zero fun v =>
      ((Formalism.L2.Th1.D.letterShift K l d (RingHom.id K) hU.1).2.2 N0 N1 v.2.1 v.2.2 v.1).1
  have hinv : ∀ f : MvPowerSeries (ZV d N0 N1) K, subst g (subst (entLog (K := K) l) f) = f := by
    intro f
    rw [subst_comp_subst_apply hlg hgs]
    simp only [hgE]
    rw [subst_self]
    rfl

  obtain ⟨B, hB⟩ : ∃ B : MvPowerSeries (Bool × ι × Fin N0 × Fin N1) K, B = ∑ ab : Fin N0 × Fin N1,
      subst (rho ab.1 ab.2) (map j (subst (zXY l σ om oms) (beMean (d := d) l σ be0 om oms ζ))) := ⟨_, rfl⟩
  have hSm := (Formalism.InvariantFactorPaths.G7.Top.mapSimeq K0 K _ j hj).1 _ _ hS
  have hR := Formalism.InvariantFactorPaths.G7.Top.simeqRules K (Bool × ι × Fin N0 × Fin N1)
  have hBS : Simeq B (sumE (ι := ι) (N0 := N0) (N1 := N1) (map j be0)) := by
    rw [hB, ← sum_subst_rho_beXY]
    refine BiextensionSums.simeq_sum (K := K) _ _ _ fun ab _ => ?_
    exact (Formalism.InvariantFactorPaths.G7.Top.simeqRules K (Bool × ι)).2.2.2.2 _ _ _ _ (cc_rho _ _)
      (fun x => KernelCokernelKilling.integral_X' _) hSm
  have hE0 : constantCoeff (sumE (ι := ι) (N0 := N0) (N1 := N1) (map j be0)) = 0 := by
    have h0 : constantCoeff (map j be0) = 0 := by
      rw [constantCoeff_map, ← coeff_zero_eq_constantCoeff_apply, hF1.1 0 (Or.inl rfl), map_zero]
    unfold sumE
    rw [map_sum]
    refine Finset.sum_eq_zero fun e _ => ?_
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun c => constantCoeff_X _)
      (fun c => constantCoeff_X _) h0
  have hSB := hR.2.1 _ _ hBS
  have hB0 : constantCoeff B = 0 := by
    have := hBS.1
    rwa [map_sub, hE0, sub_zero] at this
  have hnE : constantCoeff (-(sumE (ι := ι) (N0 := N0) (N1 := N1) (map j be0))) = 0 := by
    rw [map_neg, hE0, neg_zero]
  have hnB : constantCoeff (-B) = 0 := by rw [map_neg, hB0, neg_zero]
  have hxB : subst (xOfZ (d := d) (N0 := N0) (N1 := N1) l j σ om oms) B =
      ∑ ab : Fin N0 × Fin N1, subst (fun s : ZMod d =>
        (X (s, ab.1, ab.2) : MvPowerSeries (ZV d N0 N1) K)) (map j (beMean (d := d) l σ be0 om oms ζ)) := by
    rw [hB, subst_sum hx]
    refine Finset.sum_congr rfl fun ab _ => ?_
    have hz : HasSubst (zXY (d := d) l σ om oms) :=
      hasSubst_of_constantCoeff_zero (TranslateJetMomentLawAnyIdempotentLevel.cc_zXY hl σ om oms)
    have hmz : HasSubst fun s : ZMod d => map j (zXY (d := d) l σ om oms s) :=
      hasSubst_of_constantCoeff_zero fun s => by
        rw [constantCoeff_map, TranslateJetMomentLawAnyIdempotentLevel.cc_zXY hl σ om oms, map_zero]
    have hρ := hasSubst_rho (K := K) (ι := ι) ab.1 ab.2
    have hρz : HasSubst fun s : ZMod d => subst (rho (K := K) ab.1 ab.2) (map j (zXY (d := d) l σ om oms s)) :=
      hasSubst_of_constantCoeff_zero fun s => constantCoeff_subst_eq_zero hρ (cc_rho _ _)
        (by rw [constantCoeff_map, TranslateJetMomentLawAnyIdempotentLevel.cc_zXY hl σ om oms, map_zero])
    rw [map_subst hz, subst_comp_subst_apply hmz hρ, subst_comp_subst_apply hρz hx]
    congr 1
    funext s
    exact subst_xOfZ_zXY hl hd j σ hfix hTr s ab.1 ab.2
  refine ⟨subst T' U * mvExp (sumE (map j be0) - B),
    Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' (Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' hT'0 hT'i hUi) hSB.2, ?_⟩
  have hmain : mvExp (-(sumE (ι := ι) (N0 := N0) (N1 := N1) (map j be0))) *
      (subst T' U * mvExp (sumE (map j be0) - B)) = subst T' U * mvExp (-B) := by
    rw [mul_left_comm, ← mvExp_add hnE hSB.1]
    congr 2
    ring
  have hgx : subst (xOfZ (d := d) (N0 := N0) (N1 := N1) l j σ om oms) (subst T' U) = subst g U := by
    rw [subst_comp_subst_apply hT's hx]
    congr 1
    funext v
    exact (hgdef v).symm
  have hΦ2 := congrArg (subst g) hΦ
  rw [hinv, subst_mul hgs, hinv] at hΦ2
  rw [hΦ2]
  unfold thetaInZ
  rw [hmain, subst_mul hx, hgx, Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' hx hnB, BiextensionSums.subst_neg' hx, hxB]

end Main

end CofactorConverse

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem integral_cofactor_converse : ∀ (Lc : product_zeroth_first_parts.Loc) (ep : ℂ_[Lc.l]) (σ : MaximalUnramifiedExtension Lc.l →+* MaximalUnramifiedExtension Lc.l) (F be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension Lc.l)) (om oms : Fin (Lc.d / 2) → MaximalUnramifiedExtension Lc.l) (ζ : MaximalUnramifiedExtension Lc.l), BeData Lc.l Lc.d σ F be0 om oms ζ → OrbitPlaces.OrbitThetaExpansion Lc ep (-1) (beOf Lc.l Lc.d σ be0 om oms ζ) → ∃ U0 : MvPowerSeries (Bool × Fin (Lc.d / 2) × Fin Lc.N0 × Fin Lc.N1) ℂ_[Lc.l], Formalism.DworkPowerSeriesWeights.Integral U0 ∧ (MvPowerSeries.subst (fun v : ZMod Lc.d × Fin Lc.N0 × Fin Lc.N1 => (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (ZMod Lc.d × Fin Lc.N0 × Fin Lc.N1) ℂ_[Lc.l])) Lc.Th : MvPowerSeries (ZMod Lc.d × Fin Lc.N0 × Fin Lc.N1) ℂ_[Lc.l]) = thetaInZ (d := Lc.d) Lc.l (MaximalUnramifiedExtension Lc.l).subtype σ om oms (Formalism.DworkPowerSeriesWeights.mvExp (-(sumE (MvPowerSeries.map (MaximalUnramifiedExtension Lc.l).subtype be0))) * U0) := by
  intro Lc ep σ F be0 om oms ζ hD hB0
  obtain ⟨hUn, hF, hF1, hF2, hOw, hTr, hζ⟩ := hD
  obtain ⟨U, hU, hTh⟩ := hB0
  have hlg := Formalism.MainNotions.DIV.Bridge.OneLetterJetKernel.hasSubst_jetLogG Lc.l Lc.d (β := Fin Lc.N0 × Fin Lc.N1)
  have hfun : Formalism.BasicNotions.jetLogG Lc.l Lc.d (β := Fin Lc.N0 × Fin Lc.N1) =
      Formalism.DworkPowerSeriesWeights.entLog (K := ℂ_[Lc.l]) (d := Lc.d) (N0 := Lc.N0) (N1 := Lc.N1) Lc.l :=
    funext fun v => Formalism.MainNotions.DIV.Bridge.OneLetterJetKernel.jetLogG_eq_entLog Lc.l Lc.d Lc.N0 Lc.N1 v
  refine CofactorConverse.exists_cofactor Lc.l Lc.d Lc.N0 Lc.N1 σ (MaximalUnramifiedExtension Lc.l).subtype hUn (fun a => rfl)
    Lc.J.two_le_d Lc.J.d_even F hF be0 hF1 hF2 (Fin (Lc.d / 2)) om oms hOw hTr ζ hζ _ U hU ?_
  have h1 : Lc.Tht ep = MvPowerSeries.subst (Formalism.BasicNotions.jetLogG Lc.l Lc.d (β := Fin Lc.N0 × Fin Lc.N1))
      (MvPowerSeries.subst (fun v : ZMod Lc.d × Fin Lc.N0 × Fin Lc.N1 =>
        (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (ZMod Lc.d × Fin Lc.N0 × Fin Lc.N1) ℂ_[Lc.l])) Lc.Th) := by
    unfold product_zeroth_first_parts.Loc.Tht
    rw [MvPowerSeries.subst_comp_subst_apply (Formalism.MainNotions.DIV.Bridge.OneLetterJetKernel.hasSubst_CX ep) hlg]
    congr 1
    funext v
    rw [MvPowerSeries.subst_mul hlg, MvPowerSeries.subst_C, MvPowerSeries.subst_X hlg]
  rw [← hfun, ← h1, hTh]
  have e : (-1 : ℂ_[Lc.l]) • Lc.beSum (beOf Lc.l Lc.d σ be0 om oms ζ) =
      -∑ ab : Fin Lc.N0 × Fin Lc.N1, MvPowerSeries.subst (fun s : ZMod Lc.d =>
        (MvPowerSeries.X (s, ab.1, ab.2) : MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV Lc.d Lc.N0 Lc.N1) ℂ_[Lc.l]))
        (MvPowerSeries.map (MaximalUnramifiedExtension Lc.l).subtype (Formalism.L2.Th1.D.beMean (d := Lc.d) Lc.l σ be0 om oms ζ)) := by
    rw [neg_smul, one_smul]
    congr 1
    unfold product_zeroth_first_parts.Loc.beSum
    rw [Fintype.sum_prod_type]
    rfl
  rw [e]
  rfl

end GlobalTheory.KerStd
