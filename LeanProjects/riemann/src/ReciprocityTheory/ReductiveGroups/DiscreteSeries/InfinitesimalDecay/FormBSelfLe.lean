import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundJ
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormula

set_option autoImplicit false

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}

theorem wAct_append {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) :
    ∀ (w : List (Fin n × Fin n)) (p : Fin n × Fin n), wAct E (w ++ [p]) = wAct E w * E p.1 p.2
  | [], p => by simp [wAct]
  | q :: w, p => by
    show E q.1 q.2 * wAct E (w ++ [p]) = E q.1 q.2 * wAct E w * E p.1 p.2
    rw [wAct_append E w p, mul_assoc]

theorem NE_nonneg (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (x : D) : 0 ≤ NE E j x :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _

theorem NE_add (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (x y : D) :
    NE E j (x + y) ≤ NE E j x + NE E j y := by
  simp only [NE, ← sum_add_distrib]
  refine sum_le_sum fun l _ => sum_le_sum fun w _ => ?_
  rw [map_add, Submodule.coe_add]
  exact norm_add_le _ _

theorem NE_smul (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (c : ℂ) (x : D) :
    NE E j (c • x) = ‖c‖ * NE E j x := by
  simp only [NE, mul_sum, map_smul, Submodule.coe_smul, norm_smul]

theorem NE_zero (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) : NE E j 0 = 0 := by
  simpa using NE_smul E j 0 0

theorem NE_neg (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (x : D) : NE E j (-x) = NE E j x := by
  rw [← neg_one_smul ℂ x, NE_smul]; simp

theorem NE_sum (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) {ι : Type*} (s : Finset ι) (x : ι → D) :
    NE E j (∑ i ∈ s, x i) ≤ ∑ i ∈ s, NE E j (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [NE_zero]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (NE_add E j _ _).trans (add_le_add le_rfl ih)

theorem NE_mono (E : Fin n → Fin n → Module.End ℂ D) {j j' : ℕ} (h : j ≤ j') (x : D) :
    NE E j x ≤ NE E j' x :=
  sum_le_sum_of_subset_of_nonneg (fun x hx => by simp only [mem_range] at hx ⊢; omega) fun _ _ _ =>
    sum_nonneg fun _ _ => norm_nonneg _

theorem NE_zero_eq (E : Fin n → Fin n → Module.End ℂ D) (x : D) : NE E 0 x = ‖((x : D) : H)‖ := by
  simp [NE, wAct]

theorem NT_nonneg (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (f : Fin n → D) : 0 ≤ NT E j f :=
  sum_nonneg fun _ _ => NE_nonneg E j _

theorem NT_add (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (f g : Fin n → D) :
    NT E j (f + g) ≤ NT E j f + NT E j g := by
  simp only [NT, ← sum_add_distrib]
  exact sum_le_sum fun c _ => NE_add E j _ _

theorem NT_smul (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (c : ℂ) (f : Fin n → D) :
    NT E j (c • f) = ‖c‖ * NT E j f := by
  simp only [NT, mul_sum, Pi.smul_apply, NE_smul]

theorem NT_mono (E : Fin n → Fin n → Module.End ℂ D) {j j' : ℕ} (h : j ≤ j') (f : Fin n → D) :
    NT E j f ≤ NT E j' f :=
  sum_le_sum fun _ _ => NE_mono E h _

theorem NE_apply_le (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (a b : Fin n) (x : D) :
    NE E j (E a b x) ≤ NE E (j + 1) x := by
  unfold NE
  have key : ∀ l, ∑ w : Fin l → Fin n × Fin n, ‖((wAct E (List.ofFn w) (E a b x) : D) : H)‖ ≤
      ∑ w : Fin (l + 1) → Fin n × Fin n, ‖((wAct E (List.ofFn w) x : D) : H)‖ := by
    intro l
    have e0 : ∀ w : Fin l → Fin n × Fin n,
        wAct E (List.ofFn (Fin.snoc w (a, b) : Fin (l + 1) → Fin n × Fin n)) = wAct E (List.ofFn w) * E a b := by
      intro w
      rw [List.ofFn_succ', List.concat_eq_append, wAct_append]
      simp [Fin.snoc_castSucc, Fin.snoc_last]
    have e : ∀ w : Fin l → Fin n × Fin n, ‖((wAct E (List.ofFn w) (E a b x) : D) : H)‖ =
        ‖((wAct E (List.ofFn (Fin.snoc w (a, b) : Fin (l + 1) → Fin n × Fin n)) x : D) : H)‖ := by
      intro w
      rw [e0, Module.End.mul_apply]
    simp_rw [e]
    have hinj : Function.Injective (fun w : Fin l → Fin n × Fin n => (Fin.snoc w (a, b) : Fin (l + 1) → Fin n × Fin n)) :=
      fun w w' h => funext fun i => by simpa using congrFun h i.castSucc
    rw [← sum_image (f := fun w : Fin (l + 1) → Fin n × Fin n => ‖((wAct E (List.ofFn w) x : D) : H)‖)
      (fun w _ w' _ h => hinj h)]
    exact sum_le_univ_sum_of_nonneg fun _ => norm_nonneg _
  calc ∑ l ∈ range (j + 1), ∑ w : Fin l → Fin n × Fin n, ‖((wAct E (List.ofFn w) (E a b x) : D) : H)‖
      ≤ ∑ l ∈ range (j + 1), ∑ w : Fin (l + 1) → Fin n × Fin n, ‖((wAct E (List.ofFn w) x : D) : H)‖ :=
        sum_le_sum fun l _ => key l
    _ ≤ _ := by
        rw [sum_range_succ' (fun l => ∑ w : Fin l → Fin n × Fin n, ‖((wAct E (List.ofFn w) x : D) : H)‖) (j + 1)]
        exact le_add_of_nonneg_right (sum_nonneg fun _ _ => norm_nonneg _)

theorem NT_tensV_le (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (a b : Fin n) (f : Fin n → D) :
    NT E j (tensV E a b f) ≤ NT E (j + 1) f + NT E j f := by
  unfold NT
  have e : ∀ c, tensV E a b f c = E a b (f c) + if c = a then f b else 0 := fun c => tensV_coord E a b f c
  calc ∑ c, NE E j (tensV E a b f c) ≤ ∑ c, (NE E (j + 1) (f c) + if c = a then NE E j (f b) else 0) := by
        refine sum_le_sum fun c _ => ?_
        rw [e]
        refine (NE_add E j _ _).trans (add_le_add (NE_apply_le E j a b _) ?_)
        split_ifs <;> simp [NE_zero]
    _ = ∑ c, NE E (j + 1) (f c) + NE E j (f b) := by rw [sum_add_distrib]; simp
    _ ≤ _ := add_le_add le_rfl (single_le_sum (f := fun c => NE E j (f c)) (fun _ _ => NE_nonneg E j _)
        (mem_univ b))

theorem NT_eeF_le (dual : Bool) (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (f : Fin n → D) :
    NT E j (eeF dual E f) ≤ (n : ℝ) ^ 2 * NT E (j + 1) f := by
  unfold NT
  have e1 : ∀ d, NE E j (eeF dual E f d) ≤ NT E (j + 1) f := fun d => by
    cases dual
    · show NE E j (eeV E f d) ≤ _
      rw [eeV_coord]
      exact (NE_sum E j _ _).trans (sum_le_sum fun c _ => NE_apply_le E j _ _ _)
    · show NE E j (eeVd E f d) ≤ _
      rw [eeVd_coord, NE_neg]
      exact (NE_sum E j _ _).trans (sum_le_sum fun c _ => NE_apply_le E j _ _ _)
  calc ∑ d, NE E j (eeF dual E f d) ≤ ∑ _d : Fin n, NT E (j + 1) f := sum_le_sum fun d _ => e1 d
    _ = (n : ℝ) * NT E (j + 1) f := by simp [NT]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ (NT_nonneg E _ f)
        rcases Nat.eq_zero_or_pos n with h | h
        · simp [h]
        · exact_mod_cast Nat.le_self_pow two_ne_zero n

theorem NT_poly_le (dual : Bool) (E : Fin n → Fin n → Module.End ℂ D) (p : Polynomial ℂ) (j : ℕ) :
    ∃ C : ℝ, ∀ f : Fin n → D, NT E j (Polynomial.aeval (eeF dual E) p f) ≤ C * NT E (j + p.natDegree) f := by
  have hpow : ∀ i j, ∀ f : Fin n → D, NT E j (((eeF dual E) ^ i) f) ≤ ((n : ℝ) ^ 2) ^ i * NT E (j + i) f := by
    intro i
    induction i with
    | zero => intro j f; simp
    | succ i ih =>
      intro j f
      rw [pow_succ', Module.End.mul_apply]
      refine (NT_eeF_le dual E j _).trans ?_
      calc (n : ℝ) ^ 2 * NT E (j + 1) (((eeF dual E) ^ i) f) ≤ (n : ℝ) ^ 2 * (((n : ℝ) ^ 2) ^ i * NT E (j + 1 + i) f) :=
            mul_le_mul_of_nonneg_left (ih _ f) (by positivity)
        _ = _ := by rw [show j + 1 + i = j + (i + 1) by omega]; ring
  refine ⟨∑ i ∈ range (p.natDegree + 1), ‖p.coeff i‖ * ((n : ℝ) ^ 2) ^ i, fun f => ?_⟩
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, sum_mul]
  simp only [NT]
  calc ∑ c, NE E j ((∑ i ∈ range (p.natDegree + 1), (p.coeff i • (eeF dual E) ^ i) f) c)
      ≤ ∑ c, ∑ i ∈ range (p.natDegree + 1), NE E j (((p.coeff i • (eeF dual E) ^ i) f) c) :=
        sum_le_sum fun c _ => by rw [Finset.sum_apply]; exact NE_sum E j _ _
    _ = ∑ i ∈ range (p.natDegree + 1), NT E j ((p.coeff i • (eeF dual E) ^ i) f) := by
        rw [sum_comm]; rfl
    _ ≤ ∑ i ∈ range (p.natDegree + 1), ‖p.coeff i‖ * ((n : ℝ) ^ 2) ^ i * NT E (j + p.natDegree) f := by
        refine sum_le_sum fun i hi => ?_
        rw [LinearMap.smul_apply, NT_smul, mul_assoc]
        refine mul_le_mul_of_nonneg_left ((hpow i j f).trans ?_) (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (NT_mono E (by have := mem_range.mp hi; omega) f) (by positivity)

theorem NT_single (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (b : Fin n) (x : D) :
    NT E j (Pi.single b x) = NE E j x := by
  unfold NT
  rw [sum_eq_single b (fun c _ hc => by rw [Pi.single_eq_of_ne hc, NE_zero]) (by simp)]
  simp

theorem formB_self_le (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (f : Fin n → D) :
    ‖formB ε f f‖ ≤ NT E 0 f ^ 2 := by
  unfold formB NT
  calc ‖∑ c, (if ε c then (1 : ℂ) else -1) * inner ℂ ((f c : D) : H) ((f c : D) : H)‖
      ≤ ∑ c, ‖((f c : D) : H)‖ ^ 2 := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun c _ => ?_)
        rw [norm_mul, inner_self_eq_norm_sq_to_K]
        split_ifs <;> simp
    _ ≤ (∑ c, ‖((f c : D) : H)‖) ^ 2 := by
        rw [sq, sum_mul]
        refine sum_le_sum fun c _ => ?_
        rw [sq]
        exact mul_le_mul_of_nonneg_left (single_le_sum (f := fun c => ‖((f c : D) : H)‖) (fun _ _ => norm_nonneg _)
          (mem_univ c)) (norm_nonneg _)
    _ = _ := by simp [NE_zero_eq]

theorem NE_q_le {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {D' : Submodule ℂ H'}
    (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (E' : Fin n → Fin n → Module.End ℂ D')
    (S : Submodule ℂ (Fin n → D)) (hS : ∀ a b, ∀ f ∈ S, tensV E a b f ∈ S)
    (q : (Fin n → D) → D') (P : Module.End ℂ (Fin n → D)) (d : ℕ)
    (hP : ∀ j, ∃ C : ℝ, ∀ f ∈ S, NT E j (P f) ≤ C * NT E (j + d) f)
    (ka : ℝ) (hka : ka ≠ 0)
    (hT2 : ∀ a b, ∀ f ∈ S, q (tensV E a b f) = E' a b (q f))
    (hT3 : ∀ f ∈ S, ((ka * ‖((q f : D') : H')‖ ^ 2 : ℝ) : ℂ) = formB ε (P f) (P f)) (j : ℕ) :
    ∃ C : ℝ, ∀ f ∈ S, NE E' j (q f) ≤ C * NT E (j + d) f := by
  obtain ⟨C0, hC0⟩ := hP 0
  set C1 := max C0 0 with hC1
  have hk : 0 < |ka| := abs_pos.mpr hka
  set C' := C1 / Real.sqrt |ka| with hC'
  have hC'0 : 0 ≤ C' := div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)
  have hq0 : ∀ g ∈ S, ‖((q g : D') : H')‖ ≤ C' * NT E d g := by
    intro g hg
    have h1 := congrArg norm (hT3 g hg)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖((q g : D') : H')‖)] at h1
    have h2 : |ka| * ‖((q g : D') : H')‖ ^ 2 ≤ (C1 * NT E d g) ^ 2 := by
      rw [h1]
      refine (formB_self_le ε E _).trans (pow_le_pow_left₀ (NT_nonneg E 0 _) ?_ 2)
      have h4 : C0 * NT E (0 + d) g ≤ C1 * NT E d g := by
        rw [zero_add]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (NT_nonneg E d g)
      exact (hC0 g hg).trans h4
    have hx : ‖((q g : D') : H')‖ ^ 2 ≤ (C1 * NT E d g) ^ 2 / |ka| := by
      rw [le_div_iff₀ hk, mul_comm]; exact h2
    have hy : 0 ≤ C1 * NT E d g := mul_nonneg (le_max_right _ _) (NT_nonneg E d g)
    calc ‖((q g : D') : H')‖ = Real.sqrt (‖((q g : D') : H')‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((C1 * NT E d g) ^ 2 / |ka|) := Real.sqrt_le_sqrt hx
      _ = C' * NT E d g := by
          rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hy, hC']; ring
  let T : List (Fin n × Fin n) → Module.End ℂ (Fin n → D) := fun w => (w.map fun p => tensV E p.1 p.2).prod
  have hTS : ∀ w f, f ∈ S → T w f ∈ S := by
    intro w
    induction w with
    | nil => intro f hf; exact hf
    | cons p w ih => intro f hf; exact hS _ _ _ (ih f hf)
  have hTq : ∀ w f, f ∈ S → wAct E' w (q f) = q (T w f) := by
    intro w
    induction w with
    | nil => intro f hf; rfl
    | cons p w ih =>
      intro f hf
      show E' p.1 p.2 (wAct E' w (q f)) = q (tensV E p.1 p.2 (T w f))
      rw [ih f hf, hT2 _ _ _ (hTS w f hf)]
  have hTN : ∀ w j f, NT E j (T w f) ≤ 2 ^ w.length * NT E (j + w.length) f := by
    intro w
    induction w with
    | nil => intro j f; simp [T]
    | cons p w ih =>
      intro j f
      show NT E j (tensV E p.1 p.2 (T w f)) ≤ _
      refine (NT_tensV_le E j _ _ _).trans ?_
      have e1 := ih (j + 1) f
      have e2 := ih j f
      have e3 : NT E (j + w.length) f ≤ NT E (j + 1 + w.length) f := NT_mono E (by omega) f
      rw [List.length_cons, pow_succ, show j + (w.length + 1) = j + 1 + w.length by omega]
      nlinarith [NT_nonneg E (j + 1 + w.length) f, pow_pos (two_pos (α := ℝ)) w.length]
  refine ⟨∑ l ∈ range (j + 1), ((n : ℝ) ^ 2) ^ l * (C' * 2 ^ l), fun f hf => ?_⟩
  unfold NE
  rw [sum_mul]
  refine sum_le_sum fun l hl => ?_
  have hl' : l ≤ j := by have := mem_range.mp hl; omega
  calc ∑ w : Fin l → Fin n × Fin n, ‖((wAct E' (List.ofFn w) (q f) : D') : H')‖
      ≤ ∑ _w : Fin l → Fin n × Fin n, C' * (2 ^ l * NT E (d + j) f) := by
        refine sum_le_sum fun w _ => ?_
        rw [hTq _ f hf]
        refine (hq0 _ (hTS _ f hf)).trans (mul_le_mul_of_nonneg_left ?_ hC'0)
        refine (hTN _ d f).trans ?_
        rw [List.length_ofFn]
        exact mul_le_mul_of_nonneg_left (NT_mono E (by omega) f) (by positivity)
    _ = _ := by
        rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
        simp only [Fintype.card_fin]; push_cast; ring

end ReciprocityTheory.ChartRestriction.DS.DecInf
