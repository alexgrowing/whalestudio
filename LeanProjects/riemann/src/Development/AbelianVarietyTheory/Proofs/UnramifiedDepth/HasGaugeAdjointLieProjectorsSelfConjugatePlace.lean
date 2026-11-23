import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextCoeffSecondLinear
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawSelfConjugateSquarStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralEndOfLadicActionLimitStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsGaugeAdjointIntegralEndPairAddStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeAdjointEndPairElementaryBlockStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LimitIdempotentRangeLeSumEigenspacesStatement

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.ProjSelf

variable {C : Type} [Field C] {V : VF C}

theorem eq_zero_of_ge {x : C} (h : ∀ N : ℕ, V.Ge N x) : x = 0 := by
  by_contra hx
  have hne : V.v x ≠ ⊤ := fun e => hx ((AddValuation.top_iff _).1 e)
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hne
  obtain ⟨N, hN⟩ := exists_nat_gt t
  have := h N
  unfold VF.Ge at this
  rw [← ht] at this
  have h2 : (N : ℝ) ≤ t := by exact_mod_cast this
  linarith

theorem exists_lower {κ : Type} [Fintype κ] (v : κ → C) : ∃ m : ℕ, ∀ i, V.Ge (-(m : ℝ)) (v i) := by
  have h1 : ∀ x : C, ∃ m : ℕ, V.Ge (-(m : ℝ)) x := by
    intro x
    unfold VF.Ge
    induction V.v x using WithTop.recTopCoe with
    | top => exact ⟨0, le_top⟩
    | coe t =>
      obtain ⟨N, hN⟩ := exists_nat_gt (-t)
      refine ⟨N, ?_⟩
      have : -(N : ℝ) ≤ t := by linarith
      exact_mod_cast this
  choose f hf using fun i => h1 (v i)
  refine ⟨∑ i, f i, fun i => (hf i).mono ?_⟩
  have : f i ≤ ∑ i, f i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have : (f i : ℝ) ≤ ((∑ i, f i : ℕ) : ℝ) := by exact_mod_cast this
  linarith

theorem ge_mulVec {κ : Type} [Fintype κ] {A : Matrix κ κ C} (hA : ∀ i j, V.Ge 0 (A i j)) {m : ℝ} {v : κ → C}
    (hv : ∀ i, V.Ge m (v i)) (i : κ) : V.Ge m (A.mulVec v i) :=
  VF.Ge.sum fun j _ => (hA i j).mul_int (hv j)

theorem ge_l_pow (n : ℕ) : V.Ge n ((V.l : C) ^ n) := by
  induction n with
  | zero => simpa using VF.Ge.one (V := V)
  | succ n ih =>
    rw [pow_succ]
    have := ih.mul (VF.ge_l (V := V))
    push_cast
    exact this

theorem ge_of_unit_mul {u x : C} {m : ℝ} (hu : V.v u = 0) (h : V.Ge m (u * x)) : V.Ge m x := by
  unfold VF.Ge at h ⊢
  rwa [V.v.map_mul, hu, zero_add] at h

theorem v_eq_zero_of_mm {t : C} (h : V.MM (t - 1)) : V.v t = 0 := by
  have e : t = 1 + (t - 1) := by ring
  rw [e, AddValuation.map_add_eq_of_lt_left _ (by rw [V.v.map_one]; exact h), V.v.map_one]

section Lim

variable {O : Type} [CommRing O] {κ : Type} [Fintype κ] [DecidableEq κ] (L : O →+* Matrix κ κ C)

def IsLim (V : VF C) (L : O →+* Matrix κ κ C) (M : Matrix κ κ C) (a : ℕ → O) : Prop :=
  ∀ (N : ℕ) (v : κ → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M.mulVec v i - (L (a n)).mulVec v i)

theorem IsLim.eig {M : Matrix κ κ C} {a : ℕ → O} (h : IsLim V L M a) (ψ : O →+* C) (c : C)
    (hc : ∀ N : ℕ, ∃ n0, ∀ n ≥ n0, V.Ge N (c - ψ (a n))) {w : κ → C} (hw0 : ∀ i, V.Ge 0 (w i))
    (hw : ∀ x, (L x).mulVec w = ψ x • w) : M.mulVec w = c • w := by
  funext i
  rw [← sub_eq_zero]
  apply eq_zero_of_ge (V := V)
  intro N
  obtain ⟨n0, h0⟩ := h N w i
  obtain ⟨n1, h1⟩ := hc N
  have a1 := h0 (n0 + n1) (by omega)
  have a2 := (hw0 i).mul_int (h1 (n0 + n1) (by omega))
  rw [hw] at a1
  have := a1.sub a2
  convert this using 1
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem IsLim.absorb (hL : ∀ x i j, V.Ge 0 (L x i j)) {M E : Matrix κ κ C} {a e : ℕ → O} (h : IsLim V L M a)
    (hE : IsLim V L E e) (hae : ∀ n, ∃ y, e n * a n - a n = (V.l : O) ^ n * y) (v : κ → C) :
    M.mulVec v = M.mulVec (E.mulVec v) := by
  funext i
  rw [← sub_eq_zero]
  apply eq_zero_of_ge (V := V)
  intro N
  obtain ⟨m, hm⟩ := exists_lower (V := V) v
  obtain ⟨n0, h0⟩ := h N v i
  obtain ⟨n1, h1⟩ := h N (E.mulVec v) i
  choose n2 h2 using hE N v
  set n := n0 + n1 + (∑ j, n2 j) + N + m with hn
  have a0 := h0 n (by omega)
  have a1 := h1 n (by omega)
  have a2 : ∀ j, V.Ge N ((E.mulVec v - (L (e n)).mulVec v) j) := fun j => h2 j n (by
    have : n2 j ≤ ∑ j, n2 j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    omega)
  have a3 := ge_mulVec (hL (a n)) a2 i
  obtain ⟨y, hy⟩ := hae n
  have a4 : V.Ge N ((V.l : C) ^ n * (L y).mulVec v i) := by
    refine ((ge_l_pow n).mul (ge_mulVec (hL y) hm i)).mono ?_
    have : N + m ≤ n := by omega
    have : (N : ℝ) + m ≤ n := by exact_mod_cast this
    linarith
  have e1 : (V.l : C) ^ n * (L y).mulVec v i = (L (a n)).mulVec ((L (e n)).mulVec v) i - (L (a n)).mulVec v i := by
    have h3 := congrArg (fun z => (L z).mulVec v i) hy
    simp only [map_sub, map_mul, map_pow, map_natCast, Matrix.sub_mulVec, Pi.sub_apply] at h3
    have h4 : (V.l : Matrix κ κ C) ^ n * L y = ((V.l : C) ^ n) • L y := by
      rw [← Nat.cast_pow, ← Nat.cast_pow, ← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]
    rw [Matrix.mulVec_mulVec, ← map_mul, mul_comm (a n), map_mul, h3, h4, Matrix.smul_mulVec, Pi.smul_apply,
      smul_eq_mul]
  rw [e1] at a4
  rw [Matrix.mulVec_sub, Pi.sub_apply] at a3
  have := ((a0.sub a1).sub a3).sub a4
  convert this using 1
  ring

end Lim

section Seq

variable {O : Type} [CommRing O]

theorem idem_pow {l : ℕ} {ε : O} (h : ∃ y, ε * ε - ε = (l : O) * y) (k : ℕ) : (l : O) ∣ ε ^ (k + 1) - ε := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨y, hy⟩ := h
    have e : ε ^ (k + 1 + 1) - ε = ε * (ε ^ (k + 1) - ε) + (ε * ε - ε) := by ring
    rw [e, hy]
    exact (ih.mul_left _).add (dvd_mul_right _ _)

theorem pow_kill {ι : Type} (em : ι → (O →+* C)) (hint : ∀ a x, V.Ge 0 (em a x)) {ε : O}
    (hP : ∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y) (n : ℕ) :
    ∀ x : O, (∀ a, V.Ge n (em a x)) → (V.l : O) ^ n ∣ ε ^ n * x := by
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    obtain ⟨y, hy⟩ := hP x fun a => lt_of_lt_of_le (by
      have : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      exact_mod_cast this) (hx a)
    have hy' : ∀ a, V.Ge n (em a y) := by
      intro a
      have h1 := (hint a ε).mul_int (hx a)
      rw [← map_mul, hy, map_mul, map_natCast] at h1
      refine h1.of_l_mul.mono ?_
      push_cast
      linarith
    obtain ⟨z, hz⟩ := ih y hy'
    refine ⟨z, ?_⟩
    calc ε ^ (n + 1) * x = ε ^ n * (ε * x) := by ring
      _ = (V.l : O) * (ε ^ n * y) := by rw [hy]; ring
      _ = _ := by rw [hz]; ring

end Seq

section Seq2

variable {O : Type} [CommRing O] {ι : Type} (em : ι → (O →+* C))

theorem idem_lift {l : ℕ} {ε : O} (h : ∃ y, ε * ε - ε = (l : O) * y) (n : ℕ) :
    (l : O) ^ n ∣ ε ^ (l ^ n) * ε ^ (l ^ n) - ε ^ (l ^ n) := by
  obtain ⟨y, hy⟩ := h
  have h1 := dvd_sub_pow_of_dvd_sub (p := l) (a := ε * ε) (b := ε) ⟨y, hy⟩ n
  rw [mul_pow] at h1
  exact (pow_dvd_pow _ (Nat.le_succ n)).trans h1

theorem idem_cauchy {ε : O} (h : ∃ y, ε * ε - ε = (V.l : O) * y) (n : ℕ) :
    (V.l : O) ^ n ∣ ε ^ (V.l ^ (n + 1)) - ε ^ (V.l ^ n) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero V.l_prime.ne_zero
  have h0 := idem_pow h k
  rw [← Nat.succ_eq_add_one, ← hk] at h0
  have h1 := dvd_sub_pow_of_dvd_sub h0 n
  rw [← pow_mul, ← pow_succ'] at h1
  exact (pow_dvd_pow _ (Nat.le_succ n)).trans h1

theorem em_idem (ψ : O →+* C) (hint : ∀ x, V.Ge 0 (ψ x)) {ε : O} (h : ∃ y, ε * ε - ε = (V.l : O) * y)
    (h1 : V.MM (ψ ε - 1)) (n : ℕ) : V.Ge n (ψ (ε ^ (V.l ^ n)) - 1) := by
  obtain ⟨y, hy⟩ := idem_lift h n
  have h2 := congrArg ψ hy
  have hu : V.v (ψ (ε ^ (V.l ^ n))) = 0 := by
    rw [map_pow, V.v.map_pow, v_eq_zero_of_mm h1, smul_zero]
  apply ge_of_unit_mul hu
  rw [map_sub, map_mul, map_mul, map_pow ψ (V.l : O), map_natCast] at h2
  rw [mul_sub, mul_one, h2]
  simpa using (ge_l_pow n).mul (hint y)

theorem exists_seq (hint : ∀ a x, V.Ge 0 (em a x)) {ε : O} (h : ∃ y, ε * ε - ε = (V.l : O) * y)
    (h1 : ∀ a, V.MM (em a ε - 1)) (hP : ∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y)
    (φ : ι → C) (hφ : ∀ N : ℕ, ∃ x : O, ∀ a, V.Ge N (φ a - em a x)) :
    ∃ s : ℕ → O, (∀ n, ∃ y, s (n + 1) - s n = (V.l : O) ^ n * y) ∧ (∀ n, ε ^ (V.l ^ n) ∣ s n) ∧
      ∀ a (N : ℕ), ∃ n0, ∀ n ≥ n0, V.Ge N (φ a - em a (s n)) := by
  choose x hx using hφ
  refine ⟨fun n => ε ^ (V.l ^ n) * x n, fun n => ?_, fun n => dvd_mul_right _ _, fun a N => ⟨N, fun n hn => ?_⟩⟩
  · have h2 : (V.l : O) ^ n ∣ ε ^ n * (x (n + 1) - x n) := by
      refine pow_kill em hint hP n _ fun a => ?_
      have := (hx n a).sub ((hx (n + 1) a).mono (by push_cast; linarith))
      convert this using 1
      rw [map_sub]
      ring
    have h3 : n ≤ V.l ^ n := (Nat.lt_pow_self V.l_prime.one_lt).le
    have h4 : (V.l : O) ^ n ∣ ε ^ (V.l ^ n) * (x (n + 1) - x n) :=
      h2.trans (mul_dvd_mul_right (pow_dvd_pow _ h3) _)
    have h5 := ((idem_cauchy h n).mul_right (x (n + 1))).add h4
    have e : ε ^ (V.l ^ (n + 1)) * x (n + 1) - ε ^ (V.l ^ n) * x n =
      (ε ^ V.l ^ (n + 1) - ε ^ V.l ^ n) * x (n + 1) + ε ^ V.l ^ n * (x (n + 1) - x n) := by ring
    show (V.l : O) ^ n ∣ ε ^ (V.l ^ (n + 1)) * x (n + 1) - ε ^ (V.l ^ n) * x n
    rw [e]
    exact h5
  · have h2 := (hx n a).sub ((hint a (x n)).mul_int (em_idem (em a) (hint a) h (h1 a) n))
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    refine VF.Ge.mono ?_ hn'
    convert h2 using 1
    rw [map_mul]
    ring

end Seq2

section Blocks

variable {κ : Type} [Fintype κ]

def blk (r s : Fin 2) (M : Matrix κ κ C) : Matrix (Fin 2 × κ) (Fin 2 × κ) C :=
  Matrix.of fun x y : Fin 2 × κ => if x.1 = r ∧ y.1 = s then M x.2 y.2 else 0

theorem blk_mulVec (r s : Fin 2) (M : Matrix κ κ C) (v : Fin 2 × κ → C) (x : Fin 2 × κ) :
    (blk r s M).mulVec v x = if x.1 = r then M.mulVec (fun j => v (s, j)) x.2 else 0 := by
  simp only [Matrix.mulVec, dotProduct, blk, Matrix.of_apply, Fintype.sum_prod_type]
  by_cases h : x.1 = r
  · simp only [h, true_and, if_true]
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  · simp [h]

def blks (M : Fin 2 → Fin 2 → Matrix κ κ C) : Matrix (Fin 2 × κ) (Fin 2 × κ) C :=
  (blk 0 0 (M 0 0) + blk 0 1 (M 0 1)) + (blk 1 0 (M 1 0) + blk 1 1 (M 1 1))

theorem blks_mulVec (M : Fin 2 → Fin 2 → Matrix κ κ C) (v : Fin 2 × κ → C) (x : Fin 2 × κ) :
    (blks M).mulVec v x = ∑ s, (M x.1 s).mulVec (fun j => v (s, j)) x.2 := by
  obtain ⟨r, i⟩ := x
  simp only [blks, Matrix.add_mulVec, Pi.add_apply, blk_mulVec, Fin.sum_univ_two]
  fin_cases r <;> simp

end Blocks

section Main

variable [CharZero C] {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd)

theorem exists_lin : ∃ L : O →+* Matrix (Fin dd) (Fin dd) C,
    (∀ x v, (L x).mulVec v = linAct (Y.B.A.act x) v) ∧ ∀ x i j, V.Ge 0 (L x i j) := by
  have e : ∀ x i j, ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dActH C Y.B x i j =
      MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (Y.B.A.act x i) := by
    intro x i j
    show MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1)
      (MvPowerSeries.map (algebraMap C C) (Y.B.A.act x i)) = _
    rw [MvPowerSeries.coeff_map]
    rfl
  refine ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dActH C Y.B, fun x v => ?_, fun x i j => ?_⟩
  · funext i
    simp only [Matrix.mulVec, dotProduct, e, linAct]
  · rw [e]
    exact Y.intAct x i _

variable {d : ℕ} [NeZero d] {I0 : Type} [Fintype I0] (p : SelfData Y d I0)

noncomputable def rawOne : RawChart C 0 (fun _ => Empty) (Fin dd) where
  lg := fun i => un1 (Y.lg i)
  ex := fun i => un1 (Y.ex i)
  h := Y.h
  k := 0
  u := fun _ c => c.elim
  ty := fun _ c => c.elim
  n := 0
  j := 0
  j' := 0
  big := fun _ _ => True

theorem isEnd_blks (M M' : Fin 2 → Fin 2 → Matrix (Fin dd) (Fin dd) C)
    (h : ∀ r s, IsEnd (rawOne Y) V (M r s) (M' s r)) : IsEnd (Y.rawSelf p) V (blks M) (blks M') := by
  have hR := GlobalTheory.T.isIntegralGaugedFormalGroupLaw_selfConjugateSquare C V O dd Y d I0 p
  have hb : ∀ r s, IsEnd (Y.rawSelf p) V (blk r s (M r s)) (blk s r (M' s r)) := fun r s =>
    GlobalTheory.T.gaugeAdjointEndPair_elementaryBlock C V O dd Y d I0 p 0 _ (rawOne Y) rfl rfl rfl r s _ _ (h r s)
  have ha := GlobalTheory.T.isGaugeAdjointIntegralEndPair_add C V d _ _ (Y.rawSelf p) hR
  have := ha _ _ _ _ (ha _ _ _ _ (hb 0 0) (hb 0 1)) (ha _ _ _ _ (hb 1 0) (hb 1 1))
  have e : blks M' = blk 0 0 (M' 0 0) + blk 1 0 (M' 1 0) + (blk 0 1 (M' 0 1) + blk 1 1 (M' 1 1)) := by
    unfold blks
    abel
  rw [e]
  exact this

theorem exists_pair : ∃ b : (Fin dd → C) → I0 → C, ∀ φ : ZMod d → C,
    (∀ N : ℕ, ∃ x : O, ∀ a, V.Ge N (φ a - p.em a x)) →
    ∃ M M' : Matrix (Fin dd) (Fin dd) C, IsEnd (rawOne Y) V M M' ∧ IsEnd (rawOne Y) V M' M ∧
      (∀ c, M.mulVec (p.e c) = φ (p.ty0 c) • p.e c) ∧ (∀ c, M'.mulVec (p.e c) = φ (p.ty0 c + p.hd) • p.e c) ∧
      (∀ v, M.mulVec v = M.mulVec (∑ c, b v c • p.e c)) ∧ ∀ v, M'.mulVec v = M'.mulVec (∑ c, b v c • p.e c) := by
  have := Y.algClosed
  obtain ⟨L, hL, hLi⟩ := exists_lin Y
  obtain ⟨ε, h0, h1, hP⟩ := p.em_unr
  obtain ⟨E, -, -, -, hE, -⟩ := GlobalTheory.T.exists_integralEnd_of_ladic_action_limit C V O dd Y 0 _ (rawOne Y) rfl rfl rfl (fun n => ε ^ (V.l ^ n))
    (idem_cauchy h0)
  simp only [← hL] at hE
  have hb : ∀ v, ∃ b : I0 → C, E.mulVec v = ∑ c, b c • p.e c := by
    intro v
    obtain ⟨w, hw, hv⟩ := GlobalTheory.T.limitIdempotent_range_le_sum_eigenspaces C V O (Fin dd) L hLi d p.em p.em_int p.em_frob ε h0 hP E hE v
    choose b _ hb using fun a => p.e_full a (w a) fun x => by rw [← hL, hw]
    refine ⟨fun c => ∑ a, b a c, ?_⟩
    rw [hv]
    simp only [Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => hb a
  choose b hb using hb
  refine ⟨b, fun φ hφ => ?_⟩
  obtain ⟨s, hs, hsd, hsl⟩ := exists_seq p.em p.em_int h0 h1 hP φ hφ
  obtain ⟨M, M', e1, e2, hM, hM'⟩ := GlobalTheory.T.exists_integralEnd_of_ladic_action_limit C V O dd Y 0 _ (rawOne Y) rfl rfl rfl s hs
  simp only [← hL] at hM hM'
  have hst : (V.l : O) ∣ ε * star ε - star ε := by
    obtain ⟨y, hy⟩ := hP (1 - star ε) fun a => by
      have := h1 (a + p.hd)
      unfold VF.MM at this ⊢
      rw [map_sub, map_one, p.em_conj, ← V.v.map_neg, neg_sub]
      exact this
    refine ⟨-star y, ?_⟩
    have h2 := congrArg star hy
    simp only [star_mul', star_sub, star_one, star_star, star_natCast] at h2
    linear_combination -h2
  refine ⟨M, M', e1, e2, fun c => ?_, fun c => ?_, fun v => ?_, fun v => ?_⟩
  · exact IsLim.eig L (a := s) hM (p.em (p.ty0 c)) _ (hsl _) (p.e_int c) fun x => by rw [hL, p.e_eig]
  · refine IsLim.eig L (a := fun n => star (s n)) hM' (p.em (p.ty0 c)) _ ?_ (p.e_int c) fun x => by
      rw [hL, p.e_eig]
    simp only [p.em_conj]
    exact hsl _
  · rw [← hb]
    refine IsLim.absorb L hLi (a := s) (e := fun n => ε ^ (V.l ^ n)) hM hE (fun n => ?_) v
    obtain ⟨z, hz⟩ := hsd n
    show (V.l : O) ^ n ∣ ε ^ (V.l ^ n) * s n - s n
    rw [hz, ← mul_assoc, ← sub_mul]
    exact (idem_lift h0 n).mul_right _
  · rw [← hb]
    refine IsLim.absorb L hLi (a := fun n => star (s n)) (e := fun n => ε ^ (V.l ^ n)) hM' hE (fun n => ?_) v
    obtain ⟨z, hz⟩ := hsd n
    show (V.l : O) ^ n ∣ ε ^ (V.l ^ n) * star (s n) - star (s n)
    rw [hz, star_mul', star_pow, ← mul_assoc, ← sub_mul, ← mul_pow]
    exact ((pow_dvd_pow _ (Nat.le_succ n)).trans (dvd_sub_pow_of_dvd_sub hst n)).mul_right _

end Main

theorem hasProj_of {d : ℕ} {I0 κ : Type} [Fintype I0] [Fintype κ] (X : RawChart C d (fun _ => I0) κ)
    (A B : Matrix κ κ C) (h1 : IsEnd X V A B) (h2 : IsEnd X V B A)
    (a0 : ∀ c, A.mulVec (X.u 0 c) = X.u 0 c) (b1 : ∀ c, B.mulVec (X.u 1 c) = X.u 1 c)
    (a1 : ∀ c, A.mulVec (X.u 1 c) = 0) (b0 : ∀ c, B.mulVec (X.u 0 c) = 0)
    (ra : ∀ v, ∃ b : I0 → C, A.mulVec v = ∑ c, b c • X.u 0 c)
    (rb : ∀ v, ∃ b : I0 → C, B.mulVec v = ∑ c, b c • X.u 1 c) : HasProj X V :=
  ⟨![A, B], h1, h2, Fin.forall_fin_two.2 ⟨a0, b1⟩, Fin.forall_fin_two.2 ⟨a1, b0⟩, Fin.forall_fin_two.2 ⟨ra, rb⟩⟩

theorem hasProj_self : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0), HasProj (Y.rawSelf p) V := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p
  obtain ⟨b, hb⟩ := exists_pair Y p
  have hgi : ∀ a r s, V.Ge 0 (p.gm a r s) := by
    intro a r s
    obtain ⟨G, hG⟩ := p.gm_lim 0
    have := (hG a r s).add (by simpa using p.em_int a (G r s))
    simpa using this
  have hφ : ∀ r s : Fin 2, ∀ N : ℕ, ∃ x : O, ∀ a, V.Ge N (p.gm a r 0 * p.gm (a + p.hd) s 1 - p.em a x) := by
    intro r s N
    obtain ⟨G, hG⟩ := p.gm_lim N
    refine ⟨G r 0 * star (G s 1), fun a => ?_⟩
    have := ((hgi a r 0).mul_int (hG (a + p.hd) s 1)).add
      ((p.em_int (a + p.hd) (G s 1)).mul_int (hG a r 0))
    convert this using 1
    rw [map_mul, p.em_conj]
    ring
  choose M M' e1 e2 hM hM' hv hv' using fun r s : Fin 2 =>
    hb (fun a => p.gm a r 0 * p.gm (a + p.hd) s 1) (hφ r s)
  have hu : ∀ g c x, (Y.rawSelf p).u g c x = p.gm (p.ty0 c) x.1 g * p.e c x.2 := fun _ _ _ => rfl
  have hcol : ∀ g c s, (fun j => (Y.rawSelf p).u g c (s, j)) = p.gm (p.ty0 c) s g • p.e c := fun _ _ _ => rfl
  have k0 : ∀ g c, (blks M).mulVec ((Y.rawSelf p).u g c) = (if 1 = g then (0 : C) else 1) • (Y.rawSelf p).u 0 c := by
    intro g c
    funext x
    rw [blks_mulVec, ← p.gm_hyp (p.ty0 c) 1 g, Pi.smul_apply, hu, smul_eq_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hcol, Matrix.mulVec_smul, hM]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have k1 : ∀ g c, (blks fun s r => M' r s).mulVec ((Y.rawSelf p).u g c) =
      (if 0 = g then (0 : C) else 1) • (Y.rawSelf p).u 1 c := by
    intro g c
    funext x
    rw [blks_mulVec, ← p.gm_hyp (p.ty0 c) 0 g, Pi.smul_apply, hu, smul_eq_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hcol, Matrix.mulVec_smul, hM', add_assoc, p.hd_two, add_zero]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have i1 : IsEnd (Y.rawSelf p) V (blks M) (blks fun s r => M' r s) :=
    isEnd_blks Y p M (fun s r => M' r s) e1
  have i2 : IsEnd (Y.rawSelf p) V (blks fun s r => M' r s) (blks M) :=
    isEnd_blks Y p (fun s r => M' r s) M fun r s => e2 s r
  refine hasProj_of _ _ _ i1 i2 (fun c => ?_) (fun c => ?_) (fun c => ?_) (fun c => ?_) ?_ ?_
  · rw [k0, if_neg (by decide), one_smul]
  · rw [k1, if_neg (by decide), one_smul]
  · rw [k0, if_pos rfl, zero_smul]
  · rw [k1, if_pos rfl, zero_smul]
  · intro v
    refine ⟨fun c => ∑ s, b (fun j => v (s, j)) c * p.gm (p.ty0 c + p.hd) s 1, ?_⟩
    funext x
    show (blks M).mulVec v x = (∑ c, (∑ s, b (fun j => v (s, j)) c * p.gm (p.ty0 c + p.hd) s 1) •
      (Y.rawSelf p).u 0 c) x
    rw [blks_mulVec, Finset.sum_apply]
    simp only [Pi.smul_apply, hu, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hv, Matrix.mulVec_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mulVec_smul, hM]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · intro v
    refine ⟨fun c => ∑ s, b (fun j => v (s, j)) c * p.gm (p.ty0 c + p.hd) s 0, ?_⟩
    funext x
    show (blks fun s r => M' r s).mulVec v x = (∑ c, (∑ s, b (fun j => v (s, j)) c * p.gm (p.ty0 c + p.hd) s 0) •
      (Y.rawSelf p).u 1 c) x
    rw [blks_mulVec, Finset.sum_apply]
    simp only [Pi.smul_apply, hu, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hv', Matrix.mulVec_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mulVec_smul, hM', add_assoc, p.hd_two, add_zero]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

end GlobalTheory.ProjSelf
