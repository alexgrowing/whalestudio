import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsPiola
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StMaDensLogPow
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMaDensChain
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology Matrix

noncomputable section

namespace MaDensLogPow

variable {D : ℕ}

theorem det_eq_zero_of_rows_smul (M : Matrix (Fin D) (Fin D) ℂ) (w : Fin D → ℂ) {i j : Fin D}
    (hij : i ≠ j) (a b : ℂ) (hi : M i = a • w) (hj : M j = b • w) : M.det = 0 := by
  by_cases ha : a = 0
  · exact Matrix.det_eq_zero_of_row_eq_zero i fun k => by simp [hi, ha]
  · rw [← Matrix.det_updateRow_add_smul_self M hij.symm (-(b / a))]
    refine Matrix.det_eq_zero_of_row_eq_zero j fun k => ?_
    rw [updateRow_self, hi, hj]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring

theorem mdisc_eq_zero_of_two_rankOne (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (w : Fin D → ℂ)
    {a b : Fin D} (hab : a ≠ b) (x x' : Fin D → ℂ) (ha : A a = vecMulVec x w)
    (hb : A b = vecMulVec x' w) : mdisc A = 0 := by
  rw [mdisc_eq_sum_polCoef]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun r _ => ?_)
  by_cases hr : Function.Surjective r
  · obtain ⟨i, hi⟩ := hr a
    obtain ⟨j, hj⟩ := hr b
    have hij : i ≠ j := fun h => hab (by rw [← hi, ← hj, h])
    refine mul_eq_zero_of_right _ (det_eq_zero_of_rows_smul _ w hij (x i) (x' j) ?_ ?_)
    · funext k; simp [hi, ha, vecMulVec_apply]
    · funext k; simp [hj, hb, vecMulVec_apply]
  · rw [polCoef_eq_zero r hr, zero_mul]

theorem mdisc_expand (α β : ℂ) (H G : Matrix (Fin D) (Fin D) ℂ)
    (hG : ∀ (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (i j : Fin D), i ≠ j → A i = G → A j = G →
      mdisc A = 0) :
    ∀ (s : Finset (Fin D)) (C : Fin D → Matrix (Fin D) (Fin D) ℂ), (∀ i ∈ s, C i = H) →
      mdisc (fun i => if i ∈ s then α • H + β • G else C i) =
        α ^ s.card * mdisc C + α ^ (s.card - 1) * β * ∑ i ∈ s, mdisc (Function.update C i G) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro C _; simp
  | insert j s hj ih =>
    intro C hC
    have hCj : C j = H := hC j (Finset.mem_insert_self j s)
    have hCs : ∀ i ∈ s, C i = H := fun i hi => hC i (Finset.mem_insert_of_mem hi)
    have e1 : (fun i => if i ∈ insert j s then α • H + β • G else C i) =
        Function.update (fun i => if i ∈ s then α • H + β • G else C i) j (α • H + β • G) := by
      funext i
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    have e2 : Function.update (fun i => if i ∈ s then α • H + β • G else C i) j H =
        (fun i => if i ∈ s then α • H + β • G else C i) := by
      funext i
      by_cases hij : i = j
      · subst hij; simp [hj, hCj]
      · simp [Function.update_of_ne hij]
    have e3 : Function.update (fun i => if i ∈ s then α • H + β • G else C i) j G =
        (fun i => if i ∈ s then α • H + β • G else Function.update C j G i) := by
      funext i
      by_cases hij : i = j
      · subst hij; simp [hj]
      · simp [Function.update_of_ne hij]
    have hCs' : ∀ i ∈ s, Function.update C j G i = H := fun i hi => by
      rw [Function.update_of_ne (by rintro rfl; exact hj hi)]; exact hCs i hi
    have hz : ∀ i ∈ s, mdisc (Function.update (Function.update C j G) i G) = 0 := fun i hi =>
      hG _ i j (by rintro rfl; exact hj hi) (by simp)
        (by rw [Function.update_of_ne (by rintro rfl; exact hj hi)]; simp)
    rw [e1, mdisc_update_add, mdisc_update_smul, mdisc_update_smul, e2, e3, ih C hCs,
      ih _ hCs', Finset.sum_eq_zero hz, Finset.card_insert_of_notMem hj, Finset.sum_insert hj]
    rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · rw [h0, Finset.card_eq_zero.mp h0]; simp
    · obtain ⟨m, hm⟩ : ∃ m, s.card = m + 1 := ⟨s.card - 1, by omega⟩
      rw [hm]
      simp only [Nat.add_sub_cancel]
      ring

theorem cons_const_apply {n : ℕ} (A₀ H : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ) (k : Fin (n + 1 + 1)) :
    (Fin.cons A₀ (fun _ : Fin (n + 1) => H) : Fin (n + 1 + 1) → _) k = if k = 0 then A₀ else H := by
  refine Fin.cases ?_ (fun i => ?_) k
  · simp
  · simp [Fin.succ_ne_zero]

theorem cons_cons_const_apply {n : ℕ} (G A₀ H : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ)
    (k : Fin (n + 1 + 1)) :
    (Fin.cons G (Fin.cons A₀ (fun _ : Fin n => H)) : Fin (n + 1 + 1) → _) k =
      if k = 0 then G else if k = 1 then A₀ else H := by
  refine Fin.cases ?_ (fun i => ?_) k
  · simp
  · refine Fin.cases ?_ (fun l => ?_) i
    · simp
    · have h1 : (l.succ.succ : Fin (n + 1 + 1)) ≠ 1 := by
        rw [← Fin.succ_zero_eq_one]; exact fun h => Fin.succ_ne_zero l (Fin.succ_injective _ h)
      simp [Fin.succ_ne_zero, h1]

theorem mdisc_update_eq {n : ℕ} (G A₀ H : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ) (i : Fin (n + 1 + 1))
    (hi : i ≠ 0) :
    mdisc (Function.update (Fin.cons A₀ (fun _ : Fin (n + 1) => H) : Fin (n + 1 + 1) → _) i G) =
      mdisc (Fin.cons G (Fin.cons A₀ (fun _ : Fin n => H)) : Fin (n + 1 + 1) → _) := by
  rw [← mdisc_comp_perm (Fin.cons G (Fin.cons A₀ (fun _ : Fin n => H)) : Fin (n + 1 + 1) → _)
    ((Equiv.swap 1 i).trans (Equiv.swap 0 1))]
  congr 1
  funext k
  simp only [Function.comp_apply, cons_cons_const_apply, Function.update_apply, cons_const_apply,
    Equiv.trans_apply, Equiv.swap_apply_def]
  have h01 : (0 : Fin (n + 1 + 1)) ≠ 1 := by
    rw [← Fin.succ_zero_eq_one]; exact (Fin.succ_ne_zero 0).symm
  by_cases hki : k = i
  · subst hki
    by_cases hk1 : k = 1
    · subst hk1; simp [Ne.symm h01]
    · simp [hk1]
  · by_cases hk0 : k = 0
    · subst hk0; simp [Ne.symm hi, h01]
    · by_cases hk1 : k = 1
      · subst hk1; simp [hki, Ne.symm hki, hi, Ne.symm h01]
      · simp [hki, hk0, hk1]

theorem hessC_log_comp {p : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (hp : ContDiffAt ℝ 2 p y) (hpos : 0 < p y) :
    hessC (Real.log ∘ p) y =
      (((p y)⁻¹ : ℝ) : ℂ) • hessC p y + ((-((p y) ^ 2)⁻¹ : ℝ) : ℂ) • gradMat p p y := by
  set c := p y / 2 with hc
  have hc0 : 0 < c := by positivity
  set h : ℝ → ℝ := fun t => c / 2 + Real.smoothTransition ((t - c / 2) / (c / 2)) * (t - c / 2) with hh
  have hhpos : ∀ t, 0 < h t := by
    intro t
    by_cases ht : t ≤ c / 2
    · have : (t - c / 2) / (c / 2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      simp only [hh, Real.smoothTransition.zero_of_nonpos this, zero_mul, add_zero]; positivity
    · have := Real.smoothTransition.nonneg ((t - c / 2) / (c / 2))
      have : 0 ≤ Real.smoothTransition ((t - c / 2) / (c / 2)) * (t - c / 2) :=
        mul_nonneg this (by linarith)
      simp only [hh]; linarith
  have hhc : ContDiff ℝ 2 h := by
    have hs : ContDiff ℝ 2 Real.smoothTransition := Real.smoothTransition.contDiff (n := 2)
    exact contDiff_const.add ((hs.comp ((contDiff_id.sub contDiff_const).div_const _)).mul
      (contDiff_id.sub contDiff_const))
  set F : ℝ → ℝ := Real.log ∘ h with hF
  have hFc : ContDiff ℝ 2 F := hhc.log fun t => (hhpos t).ne'
  have hFeq : F =ᶠ[𝓝 (p y)] Real.log := by
    filter_upwards [Ioi_mem_nhds (show c < p y by rw [hc]; linarith)] with t ht
    have h1 : 1 ≤ (t - c / 2) / (c / 2) := by
      rw [le_div_iff₀ (by positivity)]; simp only [Set.mem_Ioi] at ht; linarith
    simp only [hF, hh, Function.comp_apply, Real.smoothTransition.one_of_one_le h1, one_mul]
    ring_nf
  have hgerm : Real.log ∘ p =ᶠ[𝓝 y] F ∘ p :=
    ((hp.continuousAt.tendsto.eventually hFeq).mono fun x hx => hx.symm)
  have hgerm2 : hessC (Real.log ∘ p) y = hessC (F ∘ p) y := by
    unfold hessC
    rw [hgerm.fderiv.fderiv_eq]
  have hd1 : deriv F (p y) = (p y)⁻¹ := by rw [hFeq.deriv_eq, Real.deriv_log]
  have hd2 : deriv (deriv F) (p y) = -((p y) ^ 2)⁻¹ := by
    rw [hFeq.deriv.deriv_eq, Real.deriv_log', deriv_inv]
  rw [hgerm2, MaDensChain.hessC_comp_real F p y hFc hp, hd1, hd2]

theorem proof : MaDensLogPow.Statement := by
  intro e φ₀ p y hp hpos
  set H := hessC p y with hH
  set G := gradMat p p y with hGdef
  set A₀ := hessC φ₀ y with hA₀
  set a : ℝ := (p y)⁻¹ with ha
  set b : ℝ := -((p y) ^ 2)⁻¹ with hb
  have hlog : hessC (Real.log ∘ p) y = (a : ℂ) • H + (b : ℂ) • G := hessC_log_comp hp hpos
  have hG : ∀ (A : Fin (e + 1 + 1) → Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ) (i j : Fin (e + 1 + 1)),
      i ≠ j → A i = G → A j = G → mdisc A = 0 := fun A i j hij hi hj =>
    mdisc_eq_zero_of_two_rankOne A _ hij _ _ (hi.trans (gradMat_eq_vecMulVec p p y))
      (hj.trans (gradMat_eq_vecMulVec p p y))
  set s : Finset (Fin (e + 1 + 1)) := Finset.univ.erase 0 with hs
  have hscard : s.card = e + 1 := by simp [hs]
  set C : Fin (e + 1 + 1) → Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ :=
    Fin.cons A₀ (fun _ : Fin (e + 1) => H) with hC
  have hCs : ∀ i ∈ s, C i = H := fun i hi => by
    rw [hC, cons_const_apply, if_neg (Finset.ne_of_mem_erase hi)]
  have key := mdisc_expand (a : ℂ) (b : ℂ) H G hG s C hCs
  rw [Finset.sum_congr rfl fun i hi => mdisc_update_eq G A₀ H i (Finset.ne_of_mem_erase hi),
    Finset.sum_const, hscard, Nat.add_sub_cancel, nsmul_eq_mul] at key
  have hfam1 : (fun k => hessC ((Fin.cons φ₀ fun _ : Fin (e + 1) => Real.log ∘ p :
      Fin (e + 1 + 1) → (Fin (e + 1 + 1) → ℂ) → ℝ) k) y) =
      fun i => if i ∈ s then (a : ℂ) • H + (b : ℂ) • G else C i := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp [hs, hC, hA₀]
    · simp [hs, Fin.succ_ne_zero, hlog]
  have hfam2 : (fun k => hessC ((Fin.cons φ₀ fun _ : Fin (e + 1) => p :
      Fin (e + 1 + 1) → (Fin (e + 1 + 1) → ℂ) → ℝ) k) y) = C := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp [hC, hA₀]
    · simp [hC, hH]
  have hfam3 : (fun i => hessC ((Fin.cons φ₀ fun _ : Fin e => p :
      Fin (e + 1) → (Fin (e + 1 + 1) → ℂ) → ℝ) i) y) = Fin.cons A₀ (fun _ : Fin e => H) := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp [hA₀]
    · simp [hH]
  unfold maDens gradDens
  rw [hfam1, hfam2, hfam3, key]
  have hp0 : p y ≠ 0 := hpos.ne'
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.add_re,
    Complex.re_ofReal_mul]
  rw [← hGdef, ha, hb]
  simp only [inv_pow, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

end MaDensLogPow

end

end GroundTheory.Heights₂.Heights
