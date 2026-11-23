import Mathlib
import Formalism.FormalGroupWitt.FormalGroupWittProofs.SolveV
import Formalism.FormalGroupWitt.FormalGroupWittProofs.EqSingleOfDegreeEqOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Cobdry
import Formalism.LocalRingCardinality.DataJet

noncomputable section

namespace GlobalTheory.BiextInhab

open MvPowerSeries Formalism.FG.SolveVAux

def laK (K : Type) [Field K] (l d : ℕ) (s : ZMod d) : MvPowerSeries (ZMod d) K :=
  fun n => ∑ e ∈ Finset.range ((n.sum fun _ k => k) + 1),
    if n = Finsupp.single (s - ((2 * e : ℕ) : ZMod d)) (l ^ (2 * e)) then ((l : K) ^ e)⁻¹ else 0

section Field

variable {K : Type} [Field K] {l d : ℕ}

theorem pow_two_mul_inj (hl : l.Prime) {a b : ℕ} (h : l ^ (2 * a) = l ^ (2 * b)) : a = b := by
  have := Nat.pow_right_injective hl.two_le h
  omega

theorem coeff_laK_single (hl : l.Prime) (j : ZMod d) (e : ℕ) :
    coeff (Finsupp.single (j - ((2 * e : ℕ) : ZMod d)) (l ^ (2 * e))) (laK K l d j) = ((l : K) ^ e)⁻¹ := by
  rw [coeff_apply]
  unfold laK
  rw [Finset.sum_eq_single e]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    have h2 := congrArg Finsupp.degree h
    simp only [Finsupp.degree_single] at h2
    exact hb (pow_two_mul_inj hl h2).symm
  · intro h
    exfalso
    apply h
    rw [Finset.mem_range, Finsupp.sum_single_index rfl]
    have := Nat.lt_pow_self (n := 2 * e) hl.one_lt
    omega

theorem coeff_laK_of_ne (j : ZMod d) (n : ZMod d →₀ ℕ)
    (h : ∀ e : ℕ, n ≠ Finsupp.single (j - ((2 * e : ℕ) : ZMod d)) (l ^ (2 * e))) :
    coeff n (laK K l d j) = 0 := by
  rw [coeff_apply]
  unfold laK
  exact Finset.sum_eq_zero fun e _ => if_neg (h e)

theorem map_laK {K' : Type} [Field K'] (σ : K →+* K') (j : ZMod d) :
    map σ (laK K l d j) = laK K' l d j := by
  ext n
  rw [coeff_map, coeff_apply, coeff_apply]
  unfold laK
  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp

theorem smul_single_shift (j : ZMod d) (e : ℕ) :
    (l ^ 2) • (Finsupp.single (j - 2 - ((2 * e : ℕ) : ZMod d)) (l ^ (2 * e)) : ZMod d →₀ ℕ)
      = Finsupp.single (j - ((2 * (e + 1) : ℕ) : ZMod d)) (l ^ (2 * (e + 1))) := by
  rw [Finsupp.smul_single, smul_eq_mul, ← pow_add]
  congr 1
  · push_cast
    ring
  · congr 1
    ring

open MvPowerSeries in
variable {K : Type} [Field K] {l d : ℕ} in
theorem _root_.GlobalTheory.BiextInhab.laK_idMod2 (hl : l.Prime) :
    _root_.Formalism.FG.IsIdMod2 (_root_.GlobalTheory.BiextInhab.laK K l d) := by
  refine ⟨fun j => ?_, fun j i => ?_⟩
  · show _root_.GlobalTheory.BiextInhab.laK K l d j 0 = 0
    unfold _root_.GlobalTheory.BiextInhab.laK
    refine Finset.sum_eq_zero fun e _ => if_neg fun h => ?_
    exact pow_ne_zero _ hl.ne_zero (Finsupp.single_eq_zero.mp h.symm)
  · show _root_.GlobalTheory.BiextInhab.laK K l d j (Finsupp.single i 1) = _
    unfold _root_.GlobalTheory.BiextInhab.laK
    rw [Finset.sum_eq_single 0]
    · simp [Finsupp.single_left_inj one_ne_zero]
    · intro e _ he
      refine if_neg fun h => he ?_
      have h1 := congrArg (fun f : ZMod d →₀ ℕ => f.sum fun _ k => k) h
      simp only [Finsupp.sum_single_index] at h1
      rcases Nat.pow_eq_one.mp h1.symm with h2 | h2
      · exact absurd h2 hl.ne_one
      · omega
    · intro h
      simp at h

theorem laK_funEq (hl : l.Prime) (j : ZMod d) :
    laK K l d j = X j + (l : K)⁻¹ • expand (l ^ 2) (pow_ne_zero 2 hl.ne_zero) (laK K l d (j - 2)) := by
  classical
  have hq : 1 < l ^ 2 := Nat.one_lt_pow two_ne_zero hl.one_lt
  ext n
  rw [map_add, map_smul, smul_eq_mul, coeff_X]
  by_cases h : ∃ e : ℕ, n = Finsupp.single (j - ((2 * e : ℕ) : ZMod d)) (l ^ (2 * e))
  · obtain ⟨e, rfl⟩ := h
    rw [coeff_laK_single hl]
    cases e with
    | zero =>
      rw [coeff_expand_of_not_dvd (i := j)]
      · simp
      · simp only [mul_zero, Nat.cast_zero, sub_zero, pow_zero, Finsupp.single_eq_same, Nat.dvd_one]
        omega
    | succ e =>
      rw [if_neg, ← smul_single_shift, coeff_expand_smul, coeff_laK_single hl, pow_succ', mul_inv, zero_add]
      intro h
      have h2 := congrArg Finsupp.degree h
      simp only [Finsupp.degree_single] at h2
      have := pow_two_mul_inj hl (b := 0) (h2.trans (by simp))
      omega
  · push Not at h
    rw [coeff_laK_of_ne j n h, if_neg (by simpa using h 0)]
    by_cases hd : ∀ i, l ^ 2 ∣ n i
    · have hn : n = (l ^ 2) • n.mapRange (· / l ^ 2) (Nat.zero_div _) := by
        ext i
        simp [Nat.mul_div_cancel' (hd i)]
      rw [hn, coeff_expand_smul, coeff_laK_of_ne]
      · simp
      · intro e he
        apply h (e + 1)
        rw [hn, he, smul_single_shift]
    · push Not at hd
      obtain ⟨i, hi⟩ := hd
      rw [coeff_expand_of_not_dvd _ _ _ hi]
      simp

theorem rescale_laK (hl : l.Prime) (w : ZMod d → K) (hw : ∀ s, w (s - 2) ^ (l ^ 2) = w s) (j : ZMod d) :
    rescale w (laK K l d j) = w j • laK K l d j := by
  have hw' : ∀ (e : ℕ) (s : ZMod d), w (s - ((2 * e : ℕ) : ZMod d)) ^ (l ^ (2 * e)) = w s := by
    intro e
    induction e with
    | zero => simp
    | succ e ih =>
      intro s
      rw [← hw s, ← ih (s - 2), ← pow_mul, ← pow_add]
      congr 2
      push_cast
      ring
  ext n
  rw [coeff_rescale, map_smul, smul_eq_mul]
  by_cases h : ∃ e : ℕ, n = Finsupp.single (j - ((2 * e : ℕ) : ZMod d)) (l ^ (2 * e))
  · obtain ⟨e, rfl⟩ := h
    rw [Finsupp.prod_single_index (by simp), hw']
  · push Not at h
    rw [coeff_laK_of_ne j n h, mul_zero, mul_zero]

variable [NeZero d]

def IsInv (l : ℕ) (h : ZMod d → MvPowerSeries (ZMod d) K) : Prop :=
  (∀ i, constantCoeff (h i) = 0) ∧ ∀ j, subst h (laK K l d j) = X j

theorem IsInv.subst_eq (hl : l.Prime) {h : ZMod d → MvPowerSeries (ZMod d) K} (hh : IsInv l h)
    {τ : Type} [Finite τ] {T Z : ZMod d → MvPowerSeries τ K} (hT : ∀ i, constantCoeff (T i) = 0)
    (hTZ : ∀ j, subst T (laK K l d j) = Z j) (j : ZMod d) : subst Z (h j) = T j := by
  have hZ : ∀ j, constantCoeff (Z j) = 0 := fun j => by
    rw [← hTZ]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hT) hT ((laK_idMod2 hl).1 j)
  have hZs := hasSubst_of_constantCoeff_zero hZ
  have hs := hasSubst_of_constantCoeff_zero hh.1
  have := Formalism.FG.subst_injective_vector K (ZMod d) τ (laK K l d) (fun j => subst Z (h j)) T
    (laK_idMod2 hl) (fun i => constantCoeff_subst_eq_zero hZs hZ (hh.1 i)) hT (fun j => by
      rw [← subst_comp_subst_apply hs hZs, hh.2, subst_X hZs, hTZ])
  exact congrFun this j

theorem IsInv.ne_zero (hl : l.Prime) {h : ZMod d → MvPowerSeries (ZMod d) K} (hh : IsInv l h) (j : ZMod d) :
    h j ≠ 0 := by
  intro h0
  have h1 := hh.subst_eq hl (T := X) (Z := laK K l d) (by simp) (fun j => by rw [subst_self]; rfl) j
  rw [h0, ← substAlgHom_apply (hasSubst_of_constantCoeff_zero (laK_idMod2 hl).1), map_zero] at h1
  have := congrArg (coeff (Finsupp.single j 1)) h1
  simp at this

theorem IsInv.rescale_eq (hl : l.Prime) {h : ZMod d → MvPowerSeries (ZMod d) K} (hh : IsInv l h)
    (w : ZMod d → K) (hw : ∀ s, w (s - 2) ^ (l ^ 2) = w s) (j : ZMod d) :
    rescale w (h j) = w j • h j := by
  have hs := hasSubst_of_constantCoeff_zero hh.1
  rw [rescale_eq_subst]
  refine hh.subst_eq hl (T := fun j => w j • h j) (fun i => by simp [hh.1 i]) (fun j => ?_) j
  have e : (fun j => w j • h j) = fun j => subst h ((w • X : ZMod d → MvPowerSeries (ZMod d) K) j) := by
    funext j
    rw [Pi.smul_apply', subst_smul hs, subst_X hs]
  rw [e, ← subst_comp_subst_apply (HasSubst.smul_X w) hs, ← rescale_eq_subst, rescale_laK hl w hw,
    subst_smul hs, hh.2, Pi.smul_apply']

end Field

section Padic

open Formalism.G

variable {l : ℕ} [hl : Fact l.Prime] {d : ℕ} {τ : Type}

theorem exists_lift {F : MvPowerSeries τ ℚ_[l]} (hF : IntegralMv F) :
    ∃ G : MvPowerSeries τ ℤ_[l], map PadicInt.Coe.ringHom G = F :=
  ⟨fun n => ⟨coeff n F, hF n⟩, by ext n; rfl⟩

theorem integral_map (G : MvPowerSeries τ ℤ_[l]) : IntegralMv (map PadicInt.Coe.ringHom G) := fun n => by
  rw [coeff_map]; exact (coeff n G).2

theorem dvd_pow_sub_expand (B : MvPowerSeries τ ℤ_[l]) :
    (l : MvPowerSeries τ ℤ_[l]) ∣ B ^ (l ^ 2) - expand (l ^ 2) (pow_ne_zero 2 hl.out.ne_zero) B := by
  have h0 : map PadicInt.toZMod (B ^ (l ^ 2) - expand (l ^ 2) (pow_ne_zero 2 hl.out.ne_zero) B) = 0 := by
    have hid : iterateFrobenius (ZMod l) l 2 = RingHom.id _ := by
      refine RingHom.ext fun x => ?_
      rw [iterateFrobenius_def, ZMod.pow_card_pow, RingHom.id_apply]
    rw [map_sub, map_pow, map_expand, ← map_iterateFrobenius_expand l hl.out.ne_zero, hid, map_id]
    simp
  have h1 : ∀ n, ∃ c : ℤ_[l],
      coeff n (B ^ (l ^ 2) - expand (l ^ 2) (pow_ne_zero 2 hl.out.ne_zero) B) = l * c := by
    intro n
    have := congrArg (coeff n) h0
    rw [coeff_map, map_zero, ← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton] at this
    exact this
  choose c hc using h1
  refine ⟨c, ?_⟩
  ext n
  rw [hc]
  erw [← nsmul_eq_mul (α := MvPowerSeries τ ℤ_[l]), map_nsmul, nsmul_eq_mul]
  rfl

variable [NeZero d]

theorem norm_subst_sub_le {P Q : ZMod d → MvPowerSeries τ ℤ_[l]} (hP : ∀ i, constantCoeff (P i) = 0)
    (hQ : ∀ i, constantCoeff (Q i) = 0) (h : ∀ i, (l : MvPowerSeries τ ℤ_[l]) ∣ P i - Q i) (j : ZMod d) (n : τ →₀ ℕ) :
    ‖coeff n (subst (fun i => map PadicInt.Coe.ringHom (P i)) (laK ℚ_[l] l d j) -
      subst (fun i => map PadicInt.Coe.ringHom (Q i)) (laK ℚ_[l] l d j))‖ ≤ ‖(l : ℚ_[l])‖ := by
  have hPs : HasSubst (fun i => map PadicInt.Coe.ringHom (P i)) :=
    hasSubst_of_constantCoeff_zero fun i => by simp [hP i]
  have hQs : HasSubst (fun i => map PadicInt.Coe.ringHom (Q i)) :=
    hasSubst_of_constantCoeff_zero fun i => by simp [hQ i]
  rw [map_sub, coeff_subst hPs, coeff_subst hQs,
    ← finsum_sub_distrib (coeff_subst_finite hPs _ _) (coeff_subst_finite hQs _ _)]
  refine finsum_induction (fun x : ℚ_[l] => ‖x‖ ≤ ‖(l : ℚ_[l])‖) (by simp)
    (fun x y hx hy => (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)) fun m => ?_
  by_cases hm : ∃ e : ℕ, m = Finsupp.single (j - ((2 * e : ℕ) : ZMod d)) (l ^ (2 * e))
  · obtain ⟨e, rfl⟩ := hm
    obtain ⟨c, hc⟩ := dvd_sub_pow_of_dvd_sub (h (j - ((2 * e : ℕ) : ZMod d))) (2 * e)
    rw [coeff_laK_single hl.out, Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp),
      ← smul_sub, ← map_sub, ← map_pow, ← map_pow, ← map_sub, hc, coeff_map, ← Nat.cast_pow l (2 * e + 1),
      ← nsmul_eq_mul, map_nsmul, map_nsmul, nsmul_eq_mul, smul_eq_mul, Nat.cast_pow]
    have hl0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
    have e1 : ((l : ℚ_[l]) ^ e)⁻¹ * ((l : ℚ_[l]) ^ (2 * e + 1) * PadicInt.Coe.ringHom (coeff n c)) =
        (l : ℚ_[l]) * ((l : ℚ_[l]) ^ e * PadicInt.Coe.ringHom (coeff n c)) := by
      field_simp
      ring
    rw [e1, norm_mul, norm_mul, norm_pow]
    refine mul_le_of_le_one_right (norm_nonneg _) (mul_le_one₀ (pow_le_one₀ (norm_nonneg _) ?_) (norm_nonneg _) (coeff n c).2)
    exact Padic.norm_p_lt_one.le
  · push Not at hm
    simp [coeff_laK_of_ne j m hm]

theorem funEq_subst {P : ZMod d → MvPowerSeries τ ℚ_[l]} (hP0 : ∀ i, constantCoeff (P i) = 0)
    (hP : ∀ i, IntegralMv (P i)) (j : ZMod d) :
    IntegralMv (subst P (laK ℚ_[l] l d j) -
      (l : ℚ_[l])⁻¹ • expand (l ^ 2) (pow_ne_zero 2 hl.out.ne_zero) (subst P (laK ℚ_[l] l d (j - 2)))) := by
  have hq : l ^ 2 ≠ 0 := pow_ne_zero 2 hl.out.ne_zero
  have hs := hasSubst_of_constantCoeff_zero hP0
  choose G hG using fun i => exists_lift (hP i)
  have hG0 : ∀ i, constantCoeff (G i) = 0 := fun i => by
    have := hP0 i
    rw [← hG, constantCoeff_map] at this
    exact Subtype.ext this
  have key := norm_subst_sub_le (P := fun i => G i ^ (l ^ 2)) (Q := fun i => expand (l ^ 2) hq (G i))
    (fun i => by simp [hG0 i, hl.out.ne_zero]) (fun i => by simp [hG0 i]) (fun i => dvd_pow_sub_expand (G i)) (j - 2)
  simp only [map_pow, map_expand, hG] at key
  have e1 : subst P (expand (l ^ 2) hq (laK ℚ_[l] l d (j - 2))) =
      subst (fun i => P i ^ (l ^ 2)) (laK ℚ_[l] l d (j - 2)) := by
    rw [expand, substAlgHom_apply, subst_comp_subst_apply (HasSubst.X_pow hq) hs]
    simp only [subst_pow hs, subst_X hs]
  intro n
  rw [laK_funEq hl.out j, subst_add hs, subst_X hs, subst_smul hs, e1, expand_subst _ _ hs, add_sub_assoc,
    ← smul_sub, map_add, map_smul, smul_eq_mul]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hP j n) ?_)
  have hl0 : 0 < ‖(l : ℚ_[l])‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.out.ne_zero)
  rw [norm_mul, norm_inv, inv_mul_le_iff₀ hl0, mul_one]
  exact key n

theorem integral_of_funEq {T : ZMod d → MvPowerSeries τ ℚ_[l]} (hT0 : ∀ i, constantCoeff (T i) = 0)
    (hT : ∀ j, IntegralMv (subst T (laK ℚ_[l] l d j) -
      (l : ℚ_[l])⁻¹ • expand (l ^ 2) (pow_ne_zero 2 hl.out.ne_zero) (subst T (laK ℚ_[l] l d (j - 2))))) (j : ZMod d) :
    IntegralMv (T j) := by
  classical
  have hq : l ^ 2 ≠ 0 := pow_ne_zero 2 hl.out.ne_zero
  have hq1 : 1 < l ^ 2 := Nat.one_lt_pow two_ne_zero hl.out.one_lt
  have hf := laK_idMod2 (K := ℚ_[l]) (d := d) hl.out
  suffices H : ∀ (k : ℕ) (j : ZMod d) (n : τ →₀ ℕ), n.degree = k → ‖coeff n (T j)‖ ≤ 1 from fun n => H _ j n rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro j n hn
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [(Finsupp.degree_eq_zero_iff n).1 hn, coeff_zero_eq_constantCoeff_apply, hT0]
      simp
    let P : ZMod d → MvPowerSeries τ ℚ_[l] := fun i m => if m.degree < k then coeff m (T i) else 0
    have hPc : ∀ i m, coeff m (P i) = if m.degree < k then coeff m (T i) else 0 := fun _ _ => rfl
    have hP0 : ∀ i, constantCoeff (P i) = 0 := fun i => by
      rw [← coeff_zero_eq_constantCoeff_apply, hPc, coeff_zero_eq_constantCoeff_apply, hT0, ite_self]
    have hP : ∀ i, IntegralMv (P i) := fun i m => by
      rw [hPc]
      split_ifs with h
      · exact ih _ h i m rfl
      · simp
    have hlow : ∀ i, Low k (T i - P i) := fun i m hm => by rw [map_sub, hPc, if_pos hm, sub_self]
    have hTs := hasSubst_of_constantCoeff_zero hT0
    have hPs := hasSubst_of_constantCoeff_zero hP0
    have hg : ∀ i, Low 2 (laK ℚ_[l] l d i - X i) := by
      intro i m hm
      rw [map_sub]
      rcases Nat.eq_zero_or_pos m.degree with h0 | h0
      · rw [(Finsupp.degree_eq_zero_iff m).1 h0, coeff_zero_eq_constantCoeff_apply, hf.1]
        simp
      · obtain ⟨a, rfl⟩ := degree_eq_one m (by omega)
        rw [hf.2, coeff_X]
        simp [Finsupp.single_left_inj]
    have hD : ∀ i, Low (k + 1) (subst T (laK ℚ_[l] l d i) - subst P (laK ℚ_[l] l d i) - (T i - P i)) := by
      intro i
      have := low_subst_sub (fun i => (low_one_iff _).2 (hT0 i)) (fun i => (low_one_iff _).2 (hP0 i)) hlow (hg i)
      rw [subst_sub hTs, subst_sub hPs, subst_X hTs, subst_X hPs] at this
      convert this using 1
      ring
    have hD' : ∀ i, Low k (subst T (laK ℚ_[l] l d i) - subst P (laK ℚ_[l] l d i)) := fun i => by
      simpa using low_add (low_mono (Nat.le_succ k) (hD i)) (hlow i)
    have hE : coeff n (expand (l ^ 2) hq
        (subst T (laK ℚ_[l] l d (j - 2)) - subst P (laK ℚ_[l] l d (j - 2)))) = 0 := by
      by_cases hd : ∀ i, l ^ 2 ∣ n i
      · obtain ⟨m, rfl⟩ : ∃ m : τ →₀ ℕ, (l ^ 2) • m = n := ⟨n.mapRange (fun a => a / l ^ 2) (by simp),
          by ext i; simp [Nat.mul_div_cancel' (hd i)]⟩
        rw [coeff_expand_smul]
        refine hD' _ m ?_
        rw [map_nsmul, smul_eq_mul] at hn
        nlinarith
      · push Not at hd
        obtain ⟨i, hi⟩ := hd
        exact coeff_expand_of_not_dvd _ _ _ hi
    have h1 := hD j n (by omega)
    have h2 := hT j n
    have h3 := funEq_subst hP0 hP j n
    have h4 : coeff n (P j) = 0 := by rw [hPc, if_neg (by omega)]
    simp only [map_sub, map_smul, smul_eq_mul] at h1 h2 h3 hE
    rw [h4] at h1
    have h5 := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 ((norm_neg _).trans_le h3))
    refine le_of_eq_of_le (congrArg norm ?_) h5
    linear_combination (-1 : ℚ_[l]) * h1 + (l : ℚ_[l])⁻¹ * hE

end Padic

section Main

open GlobalTheory.ThStr Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

variable {l : ℕ} [hl : Fact l.Prime] {d : ℕ}

theorem algebraMap_mem_Wp {x : ℚ_[l]} (hx : ‖x‖ ≤ 1) : algebraMap ℚ_[l] ℂ_[l] x ∈ Wp l := by
  have hc : Continuous fun c : ℤ_[l] => algebraMap ℚ_[l] ℂ_[l] (c : ℚ_[l]) :=
    (continuous_algebraMap ℚ_[l] ℂ_[l]).comp continuous_subtype_val
  have hcl : IsClosed {c : ℤ_[l] | algebraMap ℚ_[l] ℂ_[l] (c : ℚ_[l]) ∈ Wp l} :=
    (Subring.isClosed_topologicalClosure _).preimage hc
  have := PadicInt.denseRange_natCast.induction_on (p := fun c : ℤ_[l] => algebraMap ℚ_[l] ℂ_[l] (c : ℚ_[l]) ∈ Wp l)
    ⟨x, hx⟩ hcl (fun n => by simp)
  exact this

theorem inWf_algebraMap (x : ℚ_[l]) : InWf (algebraMap ℚ_[l] ℂ_[l] x) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖(l : ℚ_[l]) ^ k * x‖ ≤ 1 := by
    have ht := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (Padic.norm_p_lt_one (p := l))).mul_const x
    rw [zero_mul] at ht
    have := (ht.norm.eventually (gt_mem_nhds (by simp : ‖(0 : ℚ_[l])‖ < 1))).exists
    exact this.imp fun k hk => hk.le
  exact ⟨k, by simpa using algebraMap_mem_Wp hk⟩

def serW (l : ℕ) [Fact l.Prime] (κ : Type) : Subring (MvPowerSeries κ ℂ_[l]) :=
  (MvPowerSeries.map (σ := κ) (Wp l).subtype).range

open MvPowerSeries in
variable {l : ℕ} [hl : Fact l.Prime] {d : ℕ} in
theorem _root_.GlobalTheory.BiextInhab.mem_serW {κ : Type} {F : MvPowerSeries κ ℂ_[l]} :
    F ∈ _root_.GlobalTheory.BiextInhab.serW l κ ↔ _root_.Formalism.MainNotions.GL3Theta.IntegralW F := by
  constructor
  · rintro ⟨G, rfl⟩ n
    exact (coeff n G).2
  · intro h
    exact ⟨fun n => ⟨coeff n F, h n⟩, by ext n; rfl⟩

theorem norm_pow_div_factorial_le (n : ℕ) : ‖((l : ℚ_[l]) ^ n / (n.factorial : ℚ_[l]))‖ ≤ 1 := by
  have hn : (n.factorial : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  have hl0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  rw [Padic.norm_le_one_iff_val_nonneg, div_eq_mul_inv, Padic.valuation_mul (pow_ne_zero _ hl0) (inv_ne_zero hn),
    Padic.valuation_inv, Padic.valuation_pow, Padic.valuation_p, Padic.valuation_natCast]
  have := padicValNat_factorial_le (p := l) n
  omega

theorem integralW_expMv {κ : Type} {G : MvPowerSeries κ ℂ_[l]} (hG : G ∈ serW l κ) :
    IntegralW (expMv ((l : MvPowerSeries κ ℂ_[l]) * G)) := by
  intro m
  rw [coeff_apply]
  unfold expMv
  refine Subring.sum_mem _ fun n _ => ?_
  rw [mul_pow, ← Nat.cast_pow, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, mul_div_right_comm]
  refine Subring.mul_mem _ ?_ (mem_serW.1 (Subring.pow_mem _ hG n) m)
  simpa using algebraMap_mem_Wp (norm_pow_div_factorial_le (l := l) n)

variable [NeZero d]

theorem exists_integral_point (a b : ZMod d → ℕ) (ha : ∀ s, a (s - 2) = a s) (hb : ∀ s, b (s - 2) = b s) :
    ∃ T : ZMod d → MvPowerSeries (Bool × ZMod d) ℂ_[l], (∀ s, constantCoeff (T s) = 0) ∧ (∀ s, T s ∈ serW l _) ∧
      ∀ s, subst T (laK ℂ_[l] l d s) = a s • laAt (fun r => (false, r)) s + b s • laAt (fun r => (true, r)) s := by
  have hq : l ^ 2 ≠ 0 := pow_ne_zero 2 hl.out.ne_zero
  have hf := laK_idMod2 (K := ℚ_[l]) (d := d) hl.out
  have hX : ∀ c : Bool, ∀ r : ZMod d, constantCoeff (X (c, r) : MvPowerSeries (Bool × ZMod d) ℚ_[l]) = 0 := by simp
  have hXs := fun c => hasSubst_of_constantCoeff_zero (hX c)
  let z : Bool → ZMod d → MvPowerSeries (Bool × ZMod d) ℚ_[l] := fun c s =>
    subst (fun r : ZMod d => (X (c, r) : MvPowerSeries (Bool × ZMod d) ℚ_[l])) (laK ℚ_[l] l d s)
  have hz0 : ∀ c s, constantCoeff (z c s) = 0 := fun c s =>
    constantCoeff_subst_eq_zero (hXs c) (hX c) (hf.1 s)
  have hz : ∀ c s, z c s = X (c, s) + (l : ℚ_[l])⁻¹ • expand (l ^ 2) hq (z c (s - 2)) := by
    intro c s
    simp only [z]
    rw [laK_funEq hl.out s, subst_add (hXs c), subst_X (hXs c), subst_smul (hXs c), expand_subst _ _ (hXs c),
      expand, substAlgHom_apply, subst_comp_subst_apply (HasSubst.X_pow hq) (hXs c)]
    simp only [subst_pow (hXs c), subst_X (hXs c), expand_X]
  obtain ⟨T, hT0, hT⟩ := Formalism.FG.solve_exists_vector ℚ_[l] (ZMod d) (Bool × ZMod d) (laK ℚ_[l] l d)
    (fun s => a s • z false s + b s • z true s) hf (fun s => by simp [hz0])
  have hint := integral_of_funEq hT0 (fun j => by
    have e : subst T (laK ℚ_[l] l d j) - (l : ℚ_[l])⁻¹ • expand (l ^ 2) hq (subst T (laK ℚ_[l] l d (j - 2))) =
        map PadicInt.Coe.ringHom (a j • X (false, j) + b j • X (true, j)) := by
      rw [hT, hT, ha, hb, hz false j, hz true j]
      simp only [map_add, map_nsmul, map_X]
      module
    rw [e]
    exact integral_map _)
  refine ⟨fun s => map (algebraMap ℚ_[l] ℂ_[l]) (T s), fun s => by simp [hT0], fun s => mem_serW.2 fun n => ?_, fun s => ?_⟩
  · rw [coeff_map]
    exact algebraMap_mem_Wp (hint s n)
  · rw [← map_laK (algebraMap ℚ_[l] ℂ_[l]), ← map_subst (hasSubst_of_constantCoeff_zero hT0), hT]
    simp only [map_add, map_nsmul, z, map_subst (hXs _), map_laK, map_X]
    rfl

theorem exists_isInv : ∃ h : ZMod d → MvPowerSeries (ZMod d) ℚ_[l],
    IsInv l fun s => map (algebraMap ℚ_[l] ℂ_[l]) (h s) := by
  obtain ⟨h, h0, hh⟩ := Formalism.FG.solve_exists_vector ℚ_[l] (ZMod d) (ZMod d) (laK ℚ_[l] l d) X
    (laK_idMod2 hl.out) (by simp)
  refine ⟨h, fun s => by simp [h0], fun s => ?_⟩
  rw [← map_laK (algebraMap ℚ_[l] ℂ_[l]), ← map_subst (hasSubst_of_constantCoeff_zero h0), hh, map_X]

omit hl in
theorem val_sub_two_mod (s : ZMod d) : (s - 2).val + 2 ≡ s.val [MOD d] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  simp

omit hl in
theorem even_val_sub_two (hd : Even d) (s : ZMod d) : Even (s - 2).val ↔ Even s.val := by
  have := (val_sub_two_mod s).of_dvd hd.two_dvd
  unfold Nat.ModEq at this
  rw [Nat.even_iff, Nat.even_iff]
  omega

theorem pow_pow_congr {u : ℂ_[l]} (hu : u ^ (l ^ d - 1) = 1) {a b : ℕ} (h : a ≡ b [MOD d]) :
    u ^ (l ^ a) = u ^ (l ^ b) := by
  have h1 : u ^ (l ^ d) = u := by
    rw [← Nat.sub_add_cancel (Nat.one_le_pow d l hl.out.pos), pow_succ, hu, one_mul]
  have h2 : ∀ k : ℕ, u ^ (l ^ (d * k)) = u := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h1]
  have h3 : ∀ a : ℕ, u ^ (l ^ a) = u ^ (l ^ (a % d)) := fun a => by
    conv_lhs => rw [← Nat.div_add_mod a d, pow_add, pow_mul, h2]
  rw [h3 a, h3 b, h]

def beOf (M : ℕ) (h : ZMod d → MvPowerSeries (ZMod d) ℂ_[l]) : MvPowerSeries (ZMod d) ℂ_[l] :=
  (l : MvPowerSeries (ZMod d) ℂ_[l]) * (h 0 * h 1) ^ M

theorem subst_beOf {h : ZMod d → MvPowerSeries (ZMod d) ℂ_[l]} (hh : IsInv l h) (M : ℕ) (a b : ZMod d → ℕ)
    (ha : ∀ s, a (s - 2) = a s) (hb : ∀ s, b (s - 2) = b s) {Z : ZMod d → MvPowerSeries (Bool × ZMod d) ℂ_[l]}
    (hZ : ∀ s, Z s = a s • laAt (fun r => (false, r)) s + b s • laAt (fun r => (true, r)) s) :
    ∃ G ∈ serW l (Bool × ZMod d), subst Z (beOf M h) = (l : MvPowerSeries (Bool × ZMod d) ℂ_[l]) * G := by
  obtain ⟨T, hT0, hTW, hT⟩ := exists_integral_point (l := l) a b ha hb
  have hTZ : ∀ s, subst T (laK ℂ_[l] l d s) = Z s := fun s => (hT s).trans (hZ s).symm
  have hZs : HasSubst Z := hasSubst_of_constantCoeff_zero fun j => by
    rw [← hTZ]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hT0) hT0 ((laK_idMod2 hl.out).1 j)
  refine ⟨(T 0 * T 1) ^ M, Subring.pow_mem _ (Subring.mul_mem _ (hTW 0) (hTW 1)) M, ?_⟩
  rw [beOf, ← substAlgHom_apply hZs, map_mul, map_pow, map_mul, map_natCast, substAlgHom_apply, substAlgHom_apply,
    hh.subst_eq hl.out hT0 hTZ, hh.subst_eq hl.out hT0 hTZ]

theorem rescale_beOf {h : ZMod d → MvPowerSeries (ZMod d) ℂ_[l]} (hh : IsInv l h) (M : ℕ) (w : ZMod d → ℂ_[l])
    (hw : ∀ s, w (s - 2) ^ (l ^ 2) = w s) : rescale w (beOf M h) = (w 0 ^ M * w 1 ^ M) • beOf M h := by
  rw [beOf, map_mul, map_pow, map_mul, map_natCast, hh.rescale_eq hl.out w hw, hh.rescale_eq hl.out w hw,
    smul_mul_smul_comm, smul_pow, mul_smul_comm, mul_pow]

theorem parDeg_ne_zero (hd : Even d) {h : ZMod d → MvPowerSeries (ZMod d) ℂ_[l]} (hh : IsInv l h) {M : ℕ} (hM : M ≠ 0)
    (par : Bool) {n : ZMod d →₀ ℕ} (hn : coeff n (beOf M h) ≠ 0) : parDeg par n ≠ 0 := by
  intro h0
  have hd1 : Fact (1 < d) := ⟨by
    obtain ⟨k, hk⟩ := hd
    have := NeZero.ne d
    omega⟩
  have h1 := rescale_beOf hh M (fun s => if decide (Even s.val) = par then 0 else 1) (fun s => by
    simp only [even_val_sub_two hd]
    split_ifs <;> simp [hl.out.ne_zero])
  have h2 := congrArg (coeff n) h1
  rw [coeff_rescale, map_smul, smul_eq_mul] at h2
  have h3 : (n.prod fun s m => (if decide (Even s.val) = par then (0 : ℂ_[l]) else 1) ^ m) = 1 := by
    refine Finset.prod_eq_one fun s hs => ?_
    have := (Finset.sum_eq_zero_iff.1 h0) s hs
    by_cases hp : decide (Even s.val) = par
    · simp only [hp, if_true] at this
      exact absurd this (Finsupp.mem_support_iff.1 hs)
    · simp [hp]
  rw [h3, one_mul] at h2
  apply hn
  rw [h2]
  cases par <;> simp [ZMod.val_one, hM]

omit hl [NeZero d] in
theorem parDeg_add (n : ZMod d →₀ ℕ) : parDeg true n + parDeg false n = n.degree := by
  rw [parDeg, parDeg, Finsupp.sum, Finsupp.sum, ← Finset.sum_add_distrib, Finsupp.degree_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : Even s.val <;> simp [h]

theorem exists_isBe : ∀ (l : ℕ) [Fact l.Prime] (d : ℕ) [NeZero d], 5 ≤ l → Even d →
    ∃ be : MvPowerSeries (ZMod d) ℂ_[l], be ≠ 0 ∧ IsBe d be := by
  intro l hl d _ h5 hd
  obtain ⟨h, hh⟩ := exists_isInv (l := l) (d := d)
  have hM : 2 ≤ l ^ d - 1 := by
    have := Nat.pow_le_pow_right hl.out.pos (Nat.one_le_iff_ne_zero.2 (NeZero.ne d))
    rw [pow_one] at this
    omega
  refine ⟨beOf (l ^ d - 1) fun s => map (algebraMap ℚ_[l] ℂ_[l]) (h s), ?_, ?_, ?_, ?_, ?_⟩
  · refine mul_ne_zero ?_ (pow_ne_zero _ (mul_ne_zero (hh.ne_zero hl.out 0) (hh.ne_zero hl.out 1)))
    intro h0
    have := congrArg constantCoeff h0
    rw [map_natCast, map_zero, Nat.cast_eq_zero] at this
    omega
  · intro n
    have e : (beOf (l ^ d - 1) fun s => map (algebraMap ℚ_[l] ℂ_[l]) (h s)) =
        map (algebraMap ℚ_[l] ℂ_[l]) ((l : MvPowerSeries (ZMod d) ℚ_[l]) * (h 0 * h 1) ^ (l ^ d - 1)) := by
      simp [beOf]
    rw [e, coeff_map]
    exact inWf_algebraMap _
  · intro u hu
    rw [rescale_beOf hh]
    · have : ∀ s : ZMod d, (if Even s.val then u ^ (l ^ s.val) else (u ^ (l ^ s.val))⁻¹) ^ (l ^ d - 1) = 1 := by
        intro s
        split_ifs
        · rw [pow_right_comm, hu, one_pow]
        · rw [inv_pow, pow_right_comm, hu, one_pow, inv_one]
      rw [this, this, one_mul, one_smul]
    · intro s
      have := pow_pow_congr hu (val_sub_two_mod s)
      rw [pow_add, pow_mul] at this
      simp only [even_val_sub_two hd]
      split_ifs
      · exact this
      · rw [inv_pow, this]
  · intro n hn
    refine ⟨parDeg_ne_zero hd hh (by omega) _ hn, parDeg_ne_zero hd hh (by omega) _ hn, ?_⟩
    rintro ⟨h1, h2⟩
    have h3 := parDeg_add n
    have h4 := low_mul (low_zero (l : MvPowerSeries (ZMod d) ℂ_[l]))
      (low_mul (low_pow ((low_one_iff _).2 (hh.1 0)) (l ^ d - 1)) (low_pow ((low_one_iff _).2 (hh.1 1)) (l ^ d - 1)))
    rw [← mul_pow] at h4
    exact hn (h4 n (by omega))
  · intro par
    have hp : ∀ (x y : ℕ) (s : ZMod d), (if decide (Even (s - 2).val) = par then x else y) =
        if decide (Even s.val) = par then x else y := fun x y s => by simp only [even_val_sub_two hd]
    obtain ⟨G₁, h1, e1⟩ := subst_beOf hh (l ^ d - 1) (fun _ => 1) (fun s => if decide (Even s.val) = par then 1 else 0)
      (fun _ => rfl) (hp 1 0) (Z := fun s : ZMod d => if decide (Even s.val) = par then
      (laAt (fun r => (false, r)) s + laAt (fun r => (true, r)) s : MvPowerSeries (Bool × ZMod d) ℂ_[l])
      else laAt (fun r => (false, r)) s) (fun s => by split_ifs <;> simp)
    obtain ⟨G₂, h2, e2⟩ := subst_beOf hh (l ^ d - 1) (fun _ => 1) (fun _ => 0)
      (fun _ => rfl) (fun _ => rfl)
      (Z := fun s : ZMod d => (laAt (fun r => (false, r)) s : MvPowerSeries (Bool × ZMod d) ℂ_[l])) (fun s => by simp)
    obtain ⟨G₃, h3, e3⟩ := subst_beOf hh (l ^ d - 1) (fun s => if decide (Even s.val) = par then 0 else 1)
      (fun s => if decide (Even s.val) = par then 1 else 0)
      (hp 0 1) (hp 1 0) (Z := fun s : ZMod d => if decide (Even s.val) = par then
      (laAt (fun r => (true, r)) s : MvPowerSeries (Bool × ZMod d) ℂ_[l]) else laAt (fun r => (false, r)) s)
      (fun s => by split_ifs <;> simp)
    rw [cobdry, e1, e2, e3, ← mul_sub, ← mul_sub]
    exact integralW_expMv (Subring.sub_mem _ (Subring.sub_mem _ h1 h2) h3)

open MvPowerSeries in
variable {l : ℕ} [hl : Fact l.Prime] {d : ℕ} in
variable [NeZero d] in
private theorem coeff_mapDomain_rename_of_injective {σ τ R : Type} [CommSemiring R] (f : σ → τ)
    [Filter.TendstoCofinite f] (hf : Function.Injective f) (p : MvPowerSeries σ R)
    (n : σ →₀ ℕ) : coeff (Finsupp.mapDomain f n) (rename f p) = coeff n p := by
  rw [coeff_rename, Finset.sum_eq_single n]
  · intro y hy hne
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hy
    exact absurd (Finsupp.mapDomain_injective hf hy) hne
  · intro hn
    exact absurd (by simp) hn

open MvPowerSeries in
variable {l : ℕ} [hl : Fact l.Prime] {d : ℕ} in
variable [NeZero d] in

theorem _root_.GlobalTheory.BiextInhab.bridge (l : ℕ) [Fact l.Prime] (d : ℕ) [NeZero d]
    {β : Type} (b : β) (s : ZMod d) :
    _root_.GlobalTheory.ThStr.laAt (l := l) (fun r : ZMod d => (r, b)) s =
      _root_.Formalism.BasicNotions.jetLogG l d (s, b) := by
  have hinj : Function.Injective (fun r : ZMod d => (r, b)) := fun x y h => (Prod.mk.inj h).1
  have hren : _root_.GlobalTheory.ThStr.laAt (l := l) (fun r : ZMod d => (r, b)) s =
      rename (fun r : ZMod d => (r, b)) (_root_.GlobalTheory.ThStr.laS l d s) := by
    rw [rename_eq_subst]
    rfl
  have hsingle : ∀ e : ℕ, (Finsupp.single (s - 2 * (e : ZMod d), b) ((l ^ 2) ^ e) :
      ZMod d × β →₀ ℕ) = Finsupp.mapDomain (fun r : ZMod d => (r, b))
        (Finsupp.single (s - ((2 * e : ℕ) : ZMod d)) (l ^ (2 * e))) := by
    intro e
    rw [Finsupp.mapDomain_single, pow_mul]
    push_cast
    rfl
  rw [hren]
  ext m
  by_cases hm : m ∈ Set.range (Finsupp.mapDomain (fun r : ZMod d => (r, b)))
  · obtain ⟨n, rfl⟩ := hm
    have hdeg : _root_.Formalism.BasicNotions.JetTdeg (Finsupp.mapDomain (fun r : ZMod d => (r, b)) n) =
        n.sum fun _ k => k := by
      unfold _root_.Formalism.BasicNotions.JetTdeg
      exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)
    rw [coeff_mapDomain_rename_of_injective _ hinj]
    show _root_.GlobalTheory.ThStr.laS l d s n =
      _root_.Formalism.BasicNotions.jetLogG l d (s, b) (Finsupp.mapDomain (fun r : ZMod d => (r, b)) n)
    unfold _root_.GlobalTheory.ThStr.laS _root_.Formalism.BasicNotions.jetLogG
    dsimp only
    rw [hdeg]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [hsingle e, (Finsupp.mapDomain_injective hinj).eq_iff]
  · rw [coeff_rename_eq_zero _ _ hm]
    show (0 : ℂ_[l]) = _root_.Formalism.BasicNotions.jetLogG l d (s, b) m
    unfold _root_.Formalism.BasicNotions.jetLogG
    dsimp only
    symm
    refine Finset.sum_eq_zero fun e _ => if_neg ?_
    rintro rfl
    exact hm ⟨_, (hsingle e).symm⟩

theorem exists_isBe_and_bridge :
    (∀ (l : ℕ) [Fact l.Prime] (d : ℕ) [NeZero d], 5 ≤ l → Even d →
      ∃ be : MvPowerSeries (ZMod d) ℂ_[l], be ≠ 0 ∧ IsBe d be) ∧
    ∀ (l : ℕ) [Fact l.Prime] (d : ℕ) [NeZero d] {β : Type} (b : β) (s : ZMod d),
      laAt (l := l) (fun r : ZMod d => (r, b)) s = jetLogG l d (s, b) :=
  ⟨exists_isBe, bridge⟩

end Main

end GlobalTheory.BiextInhab
