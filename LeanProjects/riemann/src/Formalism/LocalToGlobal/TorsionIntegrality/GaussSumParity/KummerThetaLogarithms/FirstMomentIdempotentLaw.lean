import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionPointsIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SubstFirstCoboundaryThree
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.IpNormPowSubPowLe
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.EqZeroOfPowEqOne
import Formalism.FormalGroupWitt.WeightInvariance
import Formalism.FormalGroupWitt.FormalGroupWittProofs.EqSingleOfDegreeEqOne

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp torus)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog frobVar frobVar_eq_expand)
open MvPowerSeries

namespace TranslateJetMomentLawAnyIdempotentLevel

open Pair KernelCokernelKilling

lemma val_sub_one {d : ℕ} [NeZero d] (t : ZMod d) :
    ∃ k : ℕ, (t - 1).val + 1 = t.val + d * k := by
  have hmod : ((t - 1).val + 1) % d = t.val := by
    have h := (ZMod.natCast_eq_natCast_iff' ((t - 1).val + 1) t.val d).1 (by simp)
    rwa [Nat.mod_eq_of_lt (ZMod.val_lt t)] at h
  refine ⟨((t - 1).val + 1) / d, ?_⟩
  have h2 := Nat.div_add_mod ((t - 1).val + 1) d
  rw [hmod] at h2
  omega

lemma parity_sub_one {d : ℕ} [NeZero d] (hd : Even d) (t : ZMod d) :
    (t - 1).val % 2 = 0 ↔ ¬ t.val % 2 = 0 := by
  obtain ⟨k, hk⟩ := val_sub_one t
  obtain ⟨m, hm⟩ := hd
  have h2 : d * k = 2 * (m * k) := by rw [hm]; ring
  rw [h2] at hk
  omega

lemma iter_sub_one {α : Type} {d : ℕ} [NeZero d] (f : α → α) {c : α} (hc : f^[d] c = c)
    (t : ZMod d) : f (f^[(t - 1).val] c) = f^[t.val] c := by
  obtain ⟨k, hk⟩ := val_sub_one t
  have h1 : f (f^[(t - 1).val] c) = f^[(t - 1).val + 1] c := (Function.iterate_succ_apply' f _ c).symm
  rw [h1, hk, Function.iterate_add_apply, Function.iterate_mul, Function.iterate_fixed hc]

lemma parity_sub_two_mul {d : ℕ} [NeZero d] (hd : Even d) (t : ZMod d) (e : ℕ) :
    (t - 2 * (e : ZMod d)).val % 2 = t.val % 2 := by
  induction e with
  | zero => simp
  | succ e ih =>
    have h : t - 2 * ((e + 1 : ℕ) : ZMod d) = t - 2 * (e : ZMod d) - 1 - 1 := by push_cast; ring
    rw [h]
    have h1 := parity_sub_one hd (t - 2 * (e : ZMod d) - 1)
    have h2 := parity_sub_one hd (t - 2 * (e : ZMod d))
    omega

section Alg

variable {K : Type} [Field K] {d : ℕ} [NeZero d]

lemma sum_odd (hd : Even d) (σ : K →+* K) {c : K} (hc : σ^[d] c = c) :
    (∑ s : ZMod d, if s.val % 2 = 0 then 0 else σ^[s.val] c) =
      σ (∑ s : ZMod d, if s.val % 2 = 0 then σ^[s.val] c else 0) := by
  rw [map_sum]
  refine Fintype.sum_equiv (Equiv.subRight (1 : ZMod d)) _ _ ?_
  intro s
  simp only [Equiv.subRight_apply]
  have hp := parity_sub_one hd s
  have hi := iter_sub_one (⇑σ) hc s
  by_cases h : s.val % 2 = 0
  · have h' : ¬ (s - 1).val % 2 = 0 := fun h'' => (hp.1 h'') h
    rw [if_pos h, if_neg h', map_zero]
  · rw [if_neg h, if_pos (hp.2 h)]
    exact hi.symm

variable {ι : Type}

def pXY (σ : K →+* K) (om oms : ι → K) (x : Bool × ι) (s : ZMod d) : K :=
  if s.val % 2 = 0 then (if x.1 = false then σ^[s.val] (oms x.2) else 0)
  else (if x.1 = true then σ^[s.val] (om x.2) else 0)

lemma dual1 [Fintype ι] [DecidableEq ι] (hd : Even d) (σ : K →+* K) {om oms : ι → K}
    (hfix : ∀ r, σ^[d] (om r) = om r ∧ σ^[d] (oms r) = oms r) (hT : TrDual d σ om oms)
    (x y : Bool × ι) :
    (∑ s : ZMod d, pXY σ om oms x s * mXY σ om oms s y) = if x = y then 1 else 0 := by
  have hit : ∀ (n : ℕ) (a b : K), σ^[n] (a * b) = σ^[n] a * σ^[n] b := by
    intro n
    induction n with
    | zero => intro a b; rfl
    | succ n ih =>
      intro a b
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        map_mul]
  obtain ⟨-, hT⟩ := hT
  obtain ⟨bx, r⟩ := x
  obtain ⟨bY, r'⟩ := y
  cases bx <;> cases bY
  · calc (∑ s : ZMod d, pXY σ om oms (false, r) s * mXY σ om oms s (false, r'))
          = ∑ s : ZMod d, if s.val % 2 = 0 then σ^[s.val] (om r' * oms r) else 0 := by
            refine Finset.sum_congr rfl fun s _ => ?_
            by_cases h : s.val % 2 = 0 <;> simp [pXY, mXY, h, hit, mul_comm]
      _ = _ := by
            rw [hT r' r]
            by_cases hr : r = r'
            · subst hr; simp
            · simp [hr, Ne.symm hr]
  · have h0 : ∀ s : ZMod d, pXY σ om oms (false, r) s * mXY σ om oms s (true, r') = 0 := by
      intro s
      by_cases h : s.val % 2 = 0 <;> simp [pXY, mXY, h]
    simp [h0]
  · have h0 : ∀ s : ZMod d, pXY σ om oms (true, r) s * mXY σ om oms s (false, r') = 0 := by
      intro s
      by_cases h : s.val % 2 = 0 <;> simp [pXY, mXY, h]
    simp [h0]
  · calc (∑ s : ZMod d, pXY σ om oms (true, r) s * mXY σ om oms s (true, r'))
          = ∑ s : ZMod d, if s.val % 2 = 0 then 0 else σ^[s.val] (om r * oms r') := by
            refine Finset.sum_congr rfl fun s _ => ?_
            by_cases h : s.val % 2 = 0 <;> simp [pXY, mXY, h, hit]
      _ = _ := by
            rw [sum_odd hd σ (c := om r * oms r') (by rw [hit, (hfix r).1, (hfix r').2]), hT r r']
            by_cases hr : r = r'
            · subst hr; simp
            · simp [hr]

lemma dual2 [Fintype ι] [DecidableEq ι] (hd : Even d) (σ : K →+* K) {om oms : ι → K}
    (hfix : ∀ r, σ^[d] (om r) = om r ∧ σ^[d] (oms r) = oms r) (hT : TrDual d σ om oms)
    (s s' : ZMod d) :
    (∑ x : Bool × ι, mXY σ om oms s x * pXY σ om oms x s') = if s = s' then 1 else 0 := by
  have hcard : Fintype.card (Bool × ι) = Fintype.card (ZMod d) := by
    rw [Fintype.card_prod, Fintype.card_bool, ZMod.card, hT.1]
  obtain ⟨e⟩ : Nonempty (Bool × ι ≃ ZMod d) := ⟨Fintype.equivOfCardEq hcard⟩
  have hAB : (Matrix.of fun (i s : ZMod d) => pXY σ om oms (e.symm i) s) *
      (Matrix.of fun (s j : ZMod d) => mXY σ om oms s (e.symm j)) = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    rw [dual1 hd σ hfix hT]
    simp only [e.symm.injective.eq_iff]
  have h2 := congrArg (fun M => M s s') (mul_eq_one_comm.1 hAB)
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply] at h2
  rw [← h2]
  exact Fintype.sum_equiv e _ _ (fun x => by simp)

lemma zXY_eq [Fintype ι] (l : ℕ) (σ : K →+* K) (om oms : ι → K) (s : ZMod d) :
    zXY l σ om oms s = ∑ x : Bool × ι, C (mXY σ om oms s x) * at1 x (lgF K l) := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  unfold zXY mXY
  by_cases h : s.val % 2 = 0 <;> simp [h]

lemma cc_zXY [Fintype ι] {l : ℕ} (hl : 2 ≤ l) (σ : K →+* K) (om oms : ι → K) (s : ZMod d) :
    constantCoeff (zXY l σ om oms s) = 0 := by
  have h0 : ∀ x : Bool × ι, MvPowerSeries.constantCoeff (at1 x (lgF K l)) = 0 := fun x =>
    Formalism.InvariantFactorPaths.G7.FormalGroupLaws.constantCoeff_inVar x _ (Formalism.InvariantFactorPaths.G7.FormalGroupLaws.constantCoeff_lgF l hl)
  unfold zXY
  split_ifs <;> simp [h0]

lemma sumE_eq {τ : Type} (σ : K →+* K) (om oms : ι → K) (r : ι) (L : ZMod d → MvPowerSeries τ K) :
    (∑ s : ZMod d, if s.val % 2 = 0 then C (σ^[s.val] (oms r)) * L s else 0) =
      ∑ s : ZMod d, C (pXY σ om oms (false, r) s) * L s := by
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : s.val % 2 = 0 <;> simp [pXY, h]

lemma sumO_eq {τ : Type} (σ : K →+* K) (om oms : ι → K) (r : ι) (L : ZMod d → MvPowerSeries τ K) :
    (∑ s : ZMod d, if s.val % 2 = 0 then 0 else C (σ^[s.val] (om r)) * L s) =
      ∑ s : ZMod d, C (pXY σ om oms (true, r) s) * L s := by
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : s.val % 2 = 0 <;> simp [pXY, h]

lemma comb_zXY [Fintype ι] [DecidableEq ι] (hd : Even d) (l : ℕ) (σ : K →+* K) {om oms : ι → K}
    (hfix : ∀ r, σ^[d] (om r) = om r ∧ σ^[d] (oms r) = oms r) (hT : TrDual d σ om oms)
    (x : Bool × ι) :
    (∑ s : ZMod d, C (pXY σ om oms x s) * zXY l σ om oms s) = at1 x (lgF K l) := by
  simp only [zXY_eq, Finset.mul_sum, ← mul_assoc, ← map_mul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, ← map_sum, dual1 hd σ hfix hT]
  simp

lemma comb_back [Fintype ι] [DecidableEq ι] (hd : Even d) (σ : K →+* K) {om oms : ι → K}
    (hfix : ∀ r, σ^[d] (om r) = om r ∧ σ^[d] (oms r) = oms r) (hT : TrDual d σ om oms)
    {τ : Type} (L : ZMod d → MvPowerSeries τ K) (j : ZMod d) :
    (∑ x : Bool × ι, C (mXY σ om oms j x) * ∑ s : ZMod d, C (pXY σ om oms x s) * L s) = L j := by
  simp only [Finset.mul_sum, ← mul_assoc, ← map_mul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, ← map_sum, dual2 hd σ hfix hT]
  simp

lemma subst_comb {α τ κ : Type} [Fintype α] {φ : τ → MvPowerSeries κ K} (hφ : HasSubst φ)
    (c : α → K) (L : α → MvPowerSeries τ K) :
    subst φ (∑ s, C (c s) * L s) = ∑ s, C (c s) * subst φ (L s) := by
  simp only [← MvPowerSeries.smul_eq_C_mul]
  rw [← MvPowerSeries.coe_substAlgHom hφ, map_sum]
  simp only [map_smul]

lemma subst_linE' {τ : Type} (σ : K →+* K) (om oms : ι → K) (r : ι)
    {L : ZMod d → MvPowerSeries τ K} (hL : HasSubst L) :
    subst L (linE σ (oms r)) = ∑ s : ZMod d, C (pXY σ om oms (false, r) s) * L s := by
  unfold linE
  rw [sumE_eq σ om oms r MvPowerSeries.X, subst_comb hL]
  simp only [MvPowerSeries.subst_X hL]

lemma subst_linO' {τ : Type} (σ : K →+* K) (om oms : ι → K) (r : ι)
    {L : ZMod d → MvPowerSeries τ K} (hL : HasSubst L) :
    subst L (linO σ (om r)) = ∑ s : ZMod d, C (pXY σ om oms (true, r) s) * L s := by
  unfold linO
  rw [sumO_eq σ om oms r MvPowerSeries.X, subst_comb hL]
  simp only [MvPowerSeries.subst_X hL]

end Alg

end TranslateJetMomentLawAnyIdempotentLevel

open Pair TranslateJetMomentLawAnyIdempotentLevel

theorem BeTilXY_of (hE : ExpSpec) : BeTilXY := by
  intro K _ _ l d _ σ hl hd be0 ι _ _ om oms hfix hT
  have hz : HasSubst (zXY (d := d) l σ om oms) :=
    hasSubst_of_constantCoeff_zero (cc_zXY hl σ om oms)
  unfold beTil beXY
  rw [subst_sum hz]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [subst2_comp hz (cc_linE σ _) (cc_linO σ _), subst_linE' σ om oms r hz,
    subst_linO' σ om oms r hz, comb_zXY hd l σ hfix hT, comb_zXY hd l σ hfix hT]
  exact addC_log hE hl (by simp) (by simp) be0

namespace TranslateJetMomentLawAnyIdempotentLevel

open Pair KernelCokernelKilling

section Gen

variable {K : Type} [Field K]

lemma letLog_eq {d : ℕ} [NeZero d] (l : ℕ) (s : ZMod d) :
    letLog (K := K) l s = gLog K l (fun s : ZMod d => s) s := by
  rfl

lemma artin_hasse_log_eq_generic_log {τ : Type} [DecidableEq τ] {d : ℕ} (l : ℕ) (x : τ) (s : ZMod d) :
    at1 x (lgF K l) = gLog K l (fun _ : ZMod d => x) s := by
  ext n
  rw [Formalism.InvariantFactorPaths.G7.coeff_single_variable_series]
  show _ = ∑ e ∈ Finset.range (n.degree + 1),
    if n = Finsupp.single x ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0
  split_ifs with h
  · obtain ⟨m, rfl⟩ : ∃ m, n = Finsupp.single x m := ⟨_, h⟩
    simp only [Finsupp.single_eq_same, Finsupp.degree_single, (Finsupp.single_injective x).eq_iff]
    rw [lgF, PowerSeries.coeff_mk]
  · symm
    refine Finset.sum_eq_zero fun e _ => if_neg ?_
    intro he
    apply h
    rw [he]
    simp

lemma coeff_one_gLog [CharZero K] {τ : Type} [DecidableEq τ] {l d : ℕ} (hl : l.Prime)
    (φ : ZMod d → τ) (s : ZMod d) (i : τ) :
    coeff (Finsupp.single i 1) (gLog K l φ s) = if i = φ s then 1 else 0 := by
  show (∑ e ∈ Finset.range ((Finsupp.single i 1).degree + 1),
      if Finsupp.single i 1 = Finsupp.single (φ (s - 2 * (e : ZMod d))) ((l ^ 2) ^ e) then
        ((l : K) ^ e)⁻¹ else 0) = _
  have hl1 : l ^ 2 ≠ 1 := by
    have := hl.two_le
    nlinarith
  rw [Finsupp.degree_single, Finset.sum_range_succ, Finset.sum_range_one]
  simp [Finsupp.single_eq_single_iff, hl1, Ne.symm hl1, hl.one_lt.ne']

lemma isIdMod2_letLog [CharZero K] {l d : ℕ} [NeZero d] (hl : l.Prime) :
    Formalism.FG.IsIdMod2 (letLog (K := K) (d := d) l) := by
  refine ⟨fun j => ?_, fun j i => ?_⟩
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    show (∑ e ∈ Finset.range ((0 : ZMod d →₀ ℕ).degree + 1),
      if (0 : ZMod d →₀ ℕ) = Finsupp.single (j - 2 * (e : ZMod d)) ((l ^ 2) ^ e) then
        ((l : K) ^ e)⁻¹ else 0) = 0
    exact Finset.sum_eq_zero fun e _ =>
      if_neg (Finsupp.single_ne_zero.2 (pow_ne_zero _ (pow_ne_zero _ hl.ne_zero))).symm
  · rw [letLog_eq, coeff_one_gLog hl]

lemma artin_hasse_log_frobenius_shift [CharZero K] {τ : Type} {l : ℕ} (hl : l.Prime) (ρ : K →+* K) (x : τ) :
    at1 x (lgF K l) - C ((l : K)⁻¹) * frobVar (l ^ 2) (map ρ (at1 x (lgF K l))) = X x := by
  classical
  have h := gLog_shift (K := K) (d := 1) hl ρ (fun _ => x) 0
  rw [← artin_hasse_log_eq_generic_log, ← artin_hasse_log_eq_generic_log] at h
  exact h

lemma coeff_one_subst {R : Type} [CommRing R] {α τ : Type} [Fintype α] [DecidableEq α]
    {f : α → MvPowerSeries α R} (hf : Formalism.FG.IsIdMod2 f) {a : α → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (j : α) (x : τ) :
    coeff (Finsupp.single x 1) (subst a (f j)) = coeff (Finsupp.single x 1) (a j) := by
  have haS : HasSubst a := hasSubst_of_constantCoeff_zero ha
  rw [coeff_subst haS, finsum_eq_single _ (Finsupp.single j 1)]
  · rw [Finsupp.prod_single_index (by simp), hf.2 j j, if_pos rfl, one_smul, pow_one]
  · intro e he
    rcases Nat.lt_or_ge e.degree 2 with hlt | hge
    · rcases Nat.lt_or_ge e.degree 1 with h0 | h1
      · have : e = 0 := (Finsupp.degree_eq_zero_iff e).1 (by omega)
        subst this
        rw [coeff_zero_eq_constantCoeff_apply, hf.1 j, zero_smul]
      · obtain ⟨i, rfl⟩ := Formalism.FG.InjVAux.eq_single_of_degree_eq_one e (by omega)
        have hij : i ≠ j := fun hij => he (by rw [hij])
        rw [hf.2 j i, if_neg hij, zero_smul]
    · rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      have hgood : ∀ i, Formalism.FG.InjVAux.Good 0 1 (a i) (a i) := fun i =>
        ⟨Formalism.FG.InjVAux.hasOrd_one_of_cc (ha i), Formalism.FG.InjVAux.hasOrd_one_of_cc (ha i), by
          rw [sub_self]; exact Formalism.FG.InjVAux.hasOrd_zero _⟩
      have hg := Formalism.FG.InjVAux.good_prod Finset.univ (fun i => 1 * e i) (fun i => a i ^ e i)
        (fun i => a i ^ e i) (fun i _ => (hgood i).pow (e i))
      have hsum : ∑ i ∈ Finset.univ, 1 * e i = e.degree := by
        rw [Finsupp.degree_eq_sum]; simp
      rw [hsum] at hg
      rw [hg.1 _ (by rw [Finsupp.degree_single]; omega), smul_zero]

open Classical in

def keep {τ : Type} (P : τ → Prop) (f : MvPowerSeries τ K) : MvPowerSeries τ K :=
  rescale (fun x => if P x then (1 : K) else 0) f

open Classical in
lemma coeff_keep {τ : Type} (P : τ → Prop) (f : MvPowerSeries τ K)
    (n : τ →₀ ℕ) :
    coeff n (keep P f) = if ∀ x, n x ≠ 0 → P x then coeff n f else 0 := by
  unfold keep
  rw [MvPowerSeries.coeff_rescale]
  split_ifs with h
  · rw [Finsupp.prod, Finset.prod_eq_one, one_mul]
    intro x hx
    rw [if_pos (h x (Finsupp.mem_support_iff.1 hx)), one_pow]
  · push_neg at h
    obtain ⟨x, hx, hPx⟩ := h
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hx), zero_mul]
    rw [if_neg hPx, zero_pow hx]

open Classical in

def keepX {τ : Type} (P : τ → Prop) : τ → MvPowerSeries τ K :=
  (fun x => if P x then (1 : K) else 0) • X

lemma keep_eq_subst {τ : Type} (P : τ → Prop) (f : MvPowerSeries τ K) :
    keep P f = subst (keepX (K := K) P) f := by
  unfold keep keepX
  exact MvPowerSeries.rescale_eq_subst _ _

lemma hasSubst_keepX {τ : Type} (P : τ → Prop) : HasSubst (keepX (K := K) P) := by
  unfold keepX
  exact MvPowerSeries.HasSubst.smul_X _

lemma keepX_pos {τ : Type} {P : τ → Prop} {x : τ} (h : P x) :
    keepX (K := K) P x = X x := by
  simp [keepX, h]

lemma keepX_neg {τ : Type} {P : τ → Prop} {x : τ} (h : ¬ P x) :
    keepX (K := K) P x = 0 := by
  simp [keepX, h]

lemma keep_letLog {l d : ℕ} [NeZero d] (hd : Even d) (j : ZMod d) :
    keep (fun s : ZMod d => (s.val % 2 = 0 ↔ j.val % 2 = 0)) (letLog (K := K) l j) =
      letLog l j := by
  ext n
  rw [coeff_keep]
  split_ifs with h
  · rfl
  · symm
    push_neg at h
    obtain ⟨x, hx, hPx⟩ := h
    show (∑ e ∈ Finset.range (n.degree + 1),
      if n = Finsupp.single (j - 2 * (e : ZMod d)) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0) = 0
    refine Finset.sum_eq_zero fun e _ => if_neg ?_
    rintro rfl
    have hx' : j - 2 * (e : ZMod d) = x := by
      by_contra hne
      rw [Finsupp.single_apply, if_neg hne] at hx
      exact hx rfl
    have hp := parity_sub_two_mul hd j e
    rw [hx'] at hp
    omega

lemma keep_zXY {l d : ℕ} [NeZero d] {ι : Type} [Fintype ι] (σ : K →+* K) (om oms : ι → K)
    (j : ZMod d) :
    keep (fun x : Bool × ι => (x.1 = false ↔ j.val % 2 = 0)) (zXY l σ om oms j) =
      zXY l σ om oms j := by
  classical
  ext n
  rw [coeff_keep]
  split_ifs with h
  · rfl
  · symm
    simp only [not_forall] at h
    obtain ⟨x, hx, hPx⟩ := h
    unfold zXY
    split_ifs with hj
    · rw [map_sum]
      refine Finset.sum_eq_zero fun r _ => ?_
      rw [MvPowerSeries.coeff_C_mul, Formalism.InvariantFactorPaths.G7.coeff_single_variable_series, if_neg, mul_zero]
      intro hn
      apply hPx
      have hxr : x = (false, r) := by
        by_contra hne
        rw [hn, Finsupp.single_apply, if_neg (Ne.symm hne)] at hx
        exact hx rfl
      subst hxr
      simp [hj]
    · rw [map_sum]
      refine Finset.sum_eq_zero fun r _ => ?_
      rw [MvPowerSeries.coeff_C_mul, Formalism.InvariantFactorPaths.G7.coeff_single_variable_series, if_neg, mul_zero]
      intro hn
      apply hPx
      have hxr : x = (true, r) := by
        by_contra hne
        rw [hn, Finsupp.single_apply, if_neg (Ne.symm hne)] at hx
        exact hx rfl
      subst hxr
      simp [hj]

end Gen

end TranslateJetMomentLawAnyIdempotentLevel

namespace TranslateJetMomentLawAnyIdempotentLevel

open Pair KernelCokernelKilling

section Shift

variable {K : Type} [Field K] {d : ℕ} [NeZero d] {ι : Type}

lemma mXY_shift (hd : Even d) (σ : K →+* K) {om oms : ι → K}
    (hfix : ∀ r, σ^[d] (om r) = om r ∧ σ^[d] (oms r) = oms r) (s : ZMod d) (x : Bool × ι) :
    σ (σ (mXY σ om oms (s - 2) x)) = mXY σ om oms s x := by
  have h2 : s - 2 = s - 1 - 1 := by ring
  have hp : (s - 2).val % 2 = s.val % 2 := by
    have := parity_sub_two_mul hd s 1
    simpa using this
  have key : ∀ c : K, σ^[d] c = c → σ (σ (σ^[(s - 2).val] c)) = σ^[s.val] c := by
    intro c hc
    rw [h2, iter_sub_one (⇑σ) hc (s - 1), iter_sub_one (⇑σ) hc s]
  obtain ⟨b, r⟩ := x
  unfold mXY
  by_cases h : s.val % 2 = 0
  · have h' : (s - 2).val % 2 = 0 := by omega
    cases b <;> simp [h, h', key _ (hfix r).1, key _ (hfix r).2]
  · have h' : ¬ (s - 2).val % 2 = 0 := by omega
    cases b <;> simp [h, h', key _ (hfix r).1, key _ (hfix r).2]

lemma zXY_shift [CharZero K] [Fintype ι] {l : ℕ} (hl : l.Prime) (hd : Even d) (σ : K →+* K)
    {om oms : ι → K} (hfix : ∀ r, σ^[d] (om r) = om r ∧ σ^[d] (oms r) = oms r) (s : ZMod d) :
    zXY l σ om oms s -
        C ((l : K)⁻¹) * frobVar (l ^ 2) (map (σ.comp σ) (zXY l σ om oms (s - 2))) =
      ∑ x : Bool × ι, C (mXY σ om oms s x) * X x := by
  have hq : l ^ 2 ≠ 0 := pow_ne_zero _ hl.ne_zero
  have hA : ∀ x : Bool × ι, at1 x (lgF K l) -
      C ((l : K)⁻¹) * frobVar (l ^ 2) (map (σ.comp σ) (at1 x (lgF K l))) = X x :=
    fun x => artin_hasse_log_frobenius_shift hl (σ.comp σ) x
  simp only [frobVar_eq_expand hq] at hA ⊢
  rw [zXY_eq l σ om oms s, zXY_eq l σ om oms (s - 2)]
  simp only [map_sum, map_mul, MvPowerSeries.map_C, RingHom.coe_comp, Function.comp_apply,
    mXY_shift hd σ hfix, MvPowerSeries.expand_C]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← hA x]
  ring

def sM (K : Type) [Field K] (d : ℕ) (s k : ZMod d) : K := if k = s - 2 then 1 else 0

end Shift

section Normed

variable {K : Type} [NormedField K] {d : ℕ} [NeZero d] {ι : Type}

lemma norm_mXY {σ : K →+* K} (hσ : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1) {om oms : ι → K}
    (hn : ∀ r, ‖om r‖ ≤ 1 ∧ ‖oms r‖ ≤ 1) (s : ZMod d) (x : Bool × ι) :
    ‖mXY σ om oms s x‖ ≤ 1 := by
  have hit : ∀ (n : ℕ) (a : K), ‖a‖ ≤ 1 → ‖σ^[n] a‖ ≤ 1 := by
    intro n
    induction n with
    | zero => intro a ha; simpa using ha
    | succ n ih =>
      intro a ha
      rw [Function.iterate_succ_apply']
      exact hσ _ (ih a ha)
  unfold mXY
  split_ifs <;> first | exact hit _ _ (hn _).1 | exact hit _ _ (hn _).2 | simp

lemma shiftType_zXY [IsUltrametricDist K] [CharZero K] [Fintype ι] {l : ℕ} (hl : l.Prime)
    (hd : Even d) {σ : K →+* K} (hσ : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1) {om oms : ι → K}
    (hO : OwOK d σ om oms) : ShiftType l σ (zXY (d := d) l σ om oms) := by
  classical
  intro s
  refine ⟨cc_zXY hl.two_le σ om oms s, ?_⟩
  rw [zXY_shift hl hd σ hO.2 s]
  intro n
  rw [map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, norm_mul]
  split_ifs <;> simp [norm_mXY hσ hO.1 s x]

lemma funEq_of_shift {l : ℕ} (hq : l ^ 2 ≠ 0) (σ : K →+* K) {τ : Type}
    {L : ZMod d → MvPowerSeries τ K} (hL : ShiftType l σ L) :
    Formalism.FG.IsFunEqTypeV l (l ^ 2) hq (σ.comp σ) (sM K d) L := by
  intro j
  have h := (hL j).2
  rw [frobVar_eq_expand hq, ← MvPowerSeries.smul_eq_C_mul] at h
  have hsum : (∑ k, sM K d j k • MvPowerSeries.expand (l ^ 2) hq (MvPowerSeries.map (σ.comp σ) (L k))) =
      MvPowerSeries.expand (l ^ 2) hq (MvPowerSeries.map (σ.comp σ) (L (j - 2))) := by
    simp [sM, ite_smul, Finset.sum_ite_eq']
  rw [hsum]
  exact h

end Normed

end TranslateJetMomentLawAnyIdempotentLevel

theorem BMinus1_of' (hE : ExpSpec) : BMinus1 := by
  intro K _ _ _ l d _ σ hU _ hd ι _ _ om oms hO hT
  have hl : l.Prime := hU.1
  have hl2 : 2 ≤ l := hl.two_le
  have hq : l ^ 2 ≠ 0 := pow_ne_zero 2 hl.ne_zero
  obtain ⟨hset, hball⟩ := frobenius_square K l σ hU
  have hfix := hO.2
  have hLS : ShiftType l σ (fun s : ZMod d => letLog (K := K) l s) :=
    (letter_shift K l d σ hl).2.1
  have hZS := shiftType_zXY hl hd hball hO
  have hid := isIdMod2_letLog (K := K) (d := d) hl
  obtain ⟨T0, hT00, hT0I, hT0s⟩ := Formalism.FG.funEqHomV K l (l ^ 2) hq (σ.comp σ) hset (ZMod d)
    (sM K d) (by intro j k; unfold sM; split_ifs <;> simp) (letLog l) hid
    (funEq_of_shift hq σ hLS) (Bool × ι) (zXY l σ om oms) (cc_zXY hl2 σ om oms)
    (funEq_of_shift hq σ hZS)
  have hT0S : HasSubst T0 := hasSubst_of_constantCoeff_zero hT00

  let PX : ZMod d → Bool × ι → Prop := fun s x => (x.1 = false ↔ s.val % 2 = 0)
  let T : ZMod d → MvPowerSeries (Bool × ι) K := fun s => keep (PX s) (T0 s)
  have hTc0 : ∀ s, constantCoeff (T s) = 0 := by
    intro s
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_keep]
    split_ifs
    · rw [coeff_zero_eq_constantCoeff_apply, hT00]
    · rfl
  have hTI : ∀ s, Integral (T s) := by
    intro s n
    rw [coeff_keep]
    split_ifs
    · exact hT0I s n
    · simp
  have hTS : HasSubst T := hasSubst_of_constantCoeff_zero hTc0
  have hTlog : ∀ j, subst T (letLog (K := K) l j) = zXY l σ om oms j := by
    intro j
    let PZ : ZMod d → Prop := fun s => (s.val % 2 = 0 ↔ j.val % 2 = 0)
    have hfam : (fun s => subst T (keepX (K := K) PZ s)) =
        fun s => subst (keepX (K := K) (PX j)) (subst T0 (keepX (K := K) PZ s)) := by
      funext s
      by_cases hs : PZ s
      · rw [keepX_pos hs, subst_X hTS, subst_X hT0S, ← keep_eq_subst]
        have hP : PX s = PX j := by
          funext x
          exact propext ⟨fun h => h.trans hs, fun h => h.trans hs.symm⟩
        change keep (PX s) (T0 s) = keep (PX j) (T0 s)
        rw [hP]
      · rw [keepX_neg hs, subst_zero' hTS, subst_zero' hT0S, subst_zero' (hasSubst_keepX _)]
    have hcomp : HasSubst (fun s => subst T0 (keepX (K := K) PZ s)) := by
      refine hasSubst_of_constantCoeff_zero fun s => ?_
      by_cases hs : PZ s
      · rw [keepX_pos hs, subst_X hT0S, hT00]
      · rw [keepX_neg hs, subst_zero' hT0S, map_zero]
    calc subst T (letLog (K := K) l j)
        = subst T (subst (keepX (K := K) PZ) (letLog (K := K) l j)) := by
          rw [← keep_eq_subst, keep_letLog hd]
      _ = subst (fun s => subst T (keepX (K := K) PZ s)) (letLog (K := K) l j) :=
          subst_comp_subst_apply (hasSubst_keepX _) hTS _
      _ = subst (fun s => subst (keepX (K := K) (PX j)) (subst T0 (keepX (K := K) PZ s)))
            (letLog (K := K) l j) := by rw [hfam]
      _ = subst (keepX (K := K) (PX j))
            (subst (fun s => subst T0 (keepX (K := K) PZ s)) (letLog (K := K) l j)) :=
          (subst_comp_subst_apply hcomp (hasSubst_keepX _) _).symm
      _ = subst (keepX (K := K) (PX j))
            (subst T0 (subst (keepX (K := K) PZ) (letLog (K := K) l j))) := by
          rw [subst_comp_subst_apply (hasSubst_keepX _) hT0S]
      _ = zXY l σ om oms j := by
          rw [← keep_eq_subst PZ, keep_letLog hd, hT0s, ← keep_eq_subst, keep_zXY]

  let G : Bool × ι → MvPowerSeries (ZMod d) K :=
    fun x => ∑ s : ZMod d, C (pXY σ om oms x s) * letLog l s
  have hG : ∀ x, IP l σ (G x) := by
    rintro ⟨b, r⟩
    have h := ShiftIP_of_frobSq frobenius_square K l d σ hU hd (ZMod d) (fun s => letLog l s) hLS
    cases b
    · have h1 := (h (oms r) (hO.1 r).2 (hfix r).2).1
      unfold linEL at h1
      rw [sumE_eq σ om oms r] at h1
      exact h1
    · have h1 := (h (om r) (hO.1 r).1 (hfix r).1).2
      unfold linOL at h1
      rw [sumO_eq σ om oms r] at h1
      exact h1
  choose Xi hXi0 hXiI hXil using fun x => integral_part_lemma K l σ hU (ZMod d) (G x) (hG x)
  have hXiS : HasSubst Xi := hasSubst_of_constantCoeff_zero hXi0
  refine ⟨T, Xi, fun s => ⟨hTc0 s, hTI s⟩, fun x => ⟨hXi0 x, hXiI x⟩, hTlog, ?_, ?_, ?_, ?_⟩
  · intro s x
    rw [← coeff_one_subst hid hTc0 s x, hTlog, zXY_eq, map_sum, Finset.sum_eq_single x]
    · rw [coeff_C_mul, artin_hasse_log_eq_generic_log (d := 1) l x 0, coeff_one_gLog hl, if_pos rfl, mul_one]
    · intro y _ hy
      rw [coeff_C_mul, artin_hasse_log_eq_generic_log (d := 1) l y 0, coeff_one_gLog hl, if_neg (Ne.symm hy),
        mul_zero]
    · intro h
      exact absurd (Finset.mem_univ x) h
  · intro s
    have hj : ∀ j, subst (fun s => subst Xi (T s)) (letLog (K := K) l j) =
        subst (X : ZMod d → MvPowerSeries (ZMod d) K) (letLog (K := K) l j) := by
      intro j
      rw [← subst_comp_subst_apply hTS hXiS, hTlog, zXY_eq, subst_comb hXiS, subst_self]
      simp only [subst_single_var hXiS, hXil]
      exact comb_back hd σ hfix hT _ j
    have key := Formalism.FG.subst_injective_vector K (ZMod d) (ZMod d) (letLog l)
      (fun s => subst Xi (T s)) X hid
      (fun s => constantCoeff_subst_eq_zero hXiS hXi0 (hTc0 s)) (fun s => constantCoeff_X s) hj
    exact congrFun key s
  · intro x
    have h1 : PowerSeries.subst (subst T (Xi x)) (lgF K l) =
        PowerSeries.subst (X x : MvPowerSeries (Bool × ι) K) (lgF K l) := by
      rw [← subst_subst1 hTS (PowerSeries.HasSubst.of_constantCoeff_zero (hXi0 x)), hXil,
        subst_comb hTS]
      simp only [hTlog]
      exact comb_zXY hd l σ hfix hT x
    have h2 := exp_log hE hl2 (constantCoeff_subst_eq_zero hTS hTc0 (hXi0 x))
    rw [h1, exp_log hE hl2 (constantCoeff_X x)] at h2
    exact h2.symm
  · intro s n hn x hx
    rw [coeff_keep] at hn
    split_ifs at hn with h
    · exact h x hx
    · exact absurd rfl hn

theorem MeanSimeq_of' (hM : MeanSimeqL) (hB : BeTilXY) (hLS : LetterShift) : MeanSimeq := by
  intro K _ _ _ l d _ σ hU hd2 hd F hF be0 hF1 hF2 ι _ _ om oms hO hT ζ hζ
  have hball := (frobenius_square K l σ hU).2
  refine ⟨hM K l d σ hU hd2 hd F hF be0 hF1 hF2 ι om oms hO hT ζ hζ (ZMod d) _
    (hLS K l d σ hU.1).2.1, ?_⟩
  have h := hM K l d σ hU hd2 hd F hF be0 hF1 hF2 ι om oms hO hT ζ hζ (Bool × ι) _
    (shiftType_zXY hU.1 hd hball hO)
  rw [hB K l d σ hU.1.two_le hd be0 ι om oms hO.2 hT] at h
  exact h

end Formalism.L2.Th1.D
