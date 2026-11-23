import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace

open ValuativeRel Matrix UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.ConvolutionTheory.Loc

variable {E : Type} [Field E] [ValuativeRel E]

theorem vecMul_bound {n : ℕ} (M : Matrix (Fin n) (Fin n) E) (h1 : ∀ j l, valuation E (M j l) ≤ 1)
    (hd : ∀ j, valuation E (M j j) = 1) (hl : ∀ j l, l < j → valuation E (M j l) < 1) (i : ℕ) (e : Fin n → E)
    (γ : ValueGroupWithZero E) (h0 : ∀ l : Fin n, i ≤ l → e l = 0)
    (hb : ∀ j : Fin n, (j : ℕ) < i → valuation E (∑ l, e l * M l j) ≤ γ) (l₀ : Fin n) : valuation E (e l₀) ≤ γ := by
  classical
  by_contra hc
  rw [not_le] at hc
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun l => valuation E (e l)) ⟨l₀, Finset.mem_univ _⟩
  obtain ⟨j, hj, hj'⟩ := Finset.exists_min_image (Finset.univ.filter fun l => valuation E (e l) = valuation E (e m))
    id ⟨m, by simp⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, id, forall_true_left] at hj hj' hm
  have hγ : γ < valuation E (e j) := hj ▸ hc.trans_le (hm l₀)
  have hpos : 0 < valuation E (e j) := zero_le.trans_lt hγ
  have hji : (j : ℕ) < i := by
    by_contra h
    rw [h0 j (not_lt.1 h)] at hpos
    simp at hpos
  have hs : valuation E (∑ l ∈ Finset.univ.erase j, e l * M l j) < valuation E (e j) := by
    refine Valuation.map_sum_lt _ hpos.ne' fun l hlj => ?_
    rw [map_mul]
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hlj) with h | h
    · refine (mul_le_of_le_one_right' (h1 l j)).trans_lt (lt_of_le_of_ne (hj ▸ hm l) fun h' => ?_)
      exact absurd (hj' l (h'.trans hj)) (not_le.2 h)
    · refine (mul_le_mul_left (show valuation E (e l) ≤ valuation E (e j) from hj ▸ hm l) _).trans_lt ?_
      exact mul_lt_of_lt_one_right hpos (hl l j h)
  have := hb j hji
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), Valuation.map_add_eq_of_lt_left, map_mul, hd, mul_one] at this
  · exact absurd this (not_le.2 hγ)
  · rwa [map_mul, hd, mul_one]

private def Nr (γ : ValueGroupWithZero E) (a a' : E) : Prop :=
  valuation E a ≤ 1 ∧ valuation E a' ≤ 1 ∧ valuation E (a - a') ≤ γ

private theorem Nr.const {γ : ValueGroupWithZero E} {a : E} (h : valuation E a ≤ 1) : Nr γ a a :=
  ⟨h, h, by simp⟩

private theorem Nr.mul {γ : ValueGroupWithZero E} {a a' b b' : E} (h : Nr γ a a') (h' : Nr γ b b') :
    Nr γ (a * b) (a' * b') := by
  refine ⟨by rw [map_mul]; exact mul_le_one' h.1 h'.1, by rw [map_mul]; exact mul_le_one' h.2.1 h'.2.1, ?_⟩
  rw [show a * b - a' * b' = a * (b - b') + (a - a') * b' by ring]
  refine Valuation.map_add_le _ ?_ ?_ <;> rw [map_mul]
  · exact (mul_le_of_le_one_left' h.1).trans h'.2.2
  · exact (mul_le_of_le_one_right' h'.2.1).trans h.2.2

private theorem Nr.sum {γ : ValueGroupWithZero E} {n : ℕ} {a a' : Fin n → E} (h : ∀ l, Nr γ (a l) (a' l)) :
    Nr γ (∑ l, a l) (∑ l, a' l) := by
  refine ⟨Valuation.map_sum_le _ fun l _ => (h l).1, Valuation.map_sum_le _ fun l _ => (h l).2.1, ?_⟩
  rw [← Finset.sum_sub_distrib]
  exact Valuation.map_sum_le _ fun l _ => (h l).2.2

private theorem Nr.inv {γ : ValueGroupWithZero E} {a a' : E} (h : Nr γ a a') (h1 : valuation E a = 1)
    (h2 : valuation E a' = 1) : Nr γ a⁻¹ a'⁻¹ := by
  have ha : a ≠ 0 := by rintro rfl; simp at h1
  have ha' : a' ≠ 0 := by rintro rfl; simp at h2
  refine ⟨by simp [h1], by simp [h2], ?_⟩
  rw [show a⁻¹ - a'⁻¹ = -((a - a') * a⁻¹ * a'⁻¹) by field_simp; ring]
  simpa [h1, h2] using h.2.2

private theorem Nr.map {γ : ValueGroupWithZero E} {σ : E ≃+* E} (hσ : ∀ x, valuation E (σ x) = valuation E x)
    {a a' : E} (h : Nr γ a a') : Nr γ (σ a) (σ a') :=
  ⟨(hσ _).le.trans h.1, (hσ _).le.trans h.2.1, by rw [← map_sub, hσ]; exact h.2.2⟩

private theorem Nr.small {γ ρ : ValueGroupWithZero E} {a a' c : E} (h : Nr γ a a') (hc : valuation E c ≤ ρ)
    (hρ : ρ ≤ 1) : Nr (ρ * γ) (c * a) (c * a') := by
  refine ⟨by rw [map_mul]; exact mul_le_one' (hc.trans hρ) h.1,
    by rw [map_mul]; exact mul_le_one' (hc.trans hρ) h.2.1, ?_⟩
  rw [← mul_sub, map_mul]
  exact mul_le_mul' hc h.2.2

variable [TopologicalSpace E] [IsNonarchimedeanLocalField E]

private theorem isCompact_ball (a : E) (γ : ValueGroupWithZero E) : IsCompact {x | valuation E (x - a) ≤ γ} :=
  (Homeomorph.subRight a).isCompact_preimage.2 (IsNonarchimedeanLocalField.isCompact_closedBall E γ)

theorem exists_fixed {n : ℕ} (e : Fin n → E) (r ρ : ValueGroupWithZero E) (hρ : ρ < 1)
    (F : (Fin n → E) → (Fin n → E))
    (hF : ∀ x, (∀ l, valuation E (x l - e l) ≤ r) → ∀ l, valuation E (F x l - e l) ≤ r)
    (hc : ∀ x y γ, (∀ l, valuation E (x l - e l) ≤ r) → (∀ l, valuation E (y l - e l) ≤ r) →
      (∀ l, valuation E (x l - y l) ≤ γ) → ∀ l, valuation E (F x l - F y l) ≤ ρ * γ) :
    ∃ x, (∀ l, valuation E (x l - e l) ≤ r) ∧ F x = x := by
  haveI : T2Space E := by
    letI := IsTopologicalAddGroup.rightUniformSpace E
    haveI := isUniformAddGroup_of_addCommGroup (G := E)
    infer_instance
  have hX : ∀ m l, valuation E (F^[m] e l - e l) ≤ r := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Function.iterate_succ_apply']; exact hF _ ih
  have hD : ∀ m l, valuation E (F^[m + 1] e l - F^[m] e l) ≤ ρ ^ m * r := by
    intro m
    induction m with
    | zero => simpa using hX 1
    | succ m ih =>
      have := hc _ _ _ (hX _) (hX _) ih
      rwa [← Function.iterate_succ_apply' F, ← Function.iterate_succ_apply' F, ← mul_assoc, ← pow_succ'] at this
  let S : ℕ → Set (Fin n → E) := fun m => Set.pi Set.univ fun l => {x | valuation E (x - F^[m] e l) ≤ ρ ^ m * r}
  have hS : ∀ m, IsCompact (S m) := fun m => isCompact_univ_pi fun l => isCompact_ball _ _
  have hle : ∀ m, ρ ^ (m + 1) * r ≤ ρ ^ m * r := fun m =>
    mul_le_mul_left (by rw [pow_succ]; exact mul_le_of_le_one_right' hρ.le) _
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S (fun m x hx l _ => by
      have h := hx l trivial
      simp only [Set.mem_setOf_eq] at h ⊢
      rw [← sub_add_sub_cancel _ (F^[m + 1] e l)]
      exact Valuation.map_add_le _ (h.trans (hle m)) (hD m l))
    (fun m => ⟨F^[m] e, fun l _ => by simp⟩) (hS 0) fun m => (hS m).isClosed
  have hx' : ∀ m l, valuation E (x l - F^[m] e l) ≤ ρ ^ m * r := fun m l => Set.mem_iInter.1 hx m l trivial
  have hx0 : ∀ l, valuation E (x l - e l) ≤ r := by simpa using hx' 0
  refine ⟨x, hx0, funext fun l => ?_⟩
  have key : ∀ m, valuation E (F x l - x l) ≤ ρ ^ m * r := by
    intro m
    have h1 := hc _ _ _ hx0 (hX m) (hx' m) l
    rw [← Function.iterate_succ_apply' F, ← mul_assoc, ← pow_succ'] at h1
    rw [← sub_sub_sub_cancel_right _ _ (F^[m + 1] e l)]
    exact (Valuation.map_sub_le _ h1 (hx' _ l)).trans (hle m)
  by_contra hne
  have hpos : valuation E (F x l - x l) ≠ 0 := by simpa [sub_eq_zero] using hne
  have hr : r ≠ 0 := by
    rintro rfl
    exact hpos (by simpa using key 0)
  haveI : MulArchimedean (ValueGroupWithZero E) := isRankLeOne_iff_mulArchimedean.1 inferInstance
  obtain ⟨m, hm⟩ := exists_pow_lt₀ hρ (Units.mk0 (valuation E (F x l - x l) / r) (div_ne_zero hpos hr))
  rw [Units.val_mk0, lt_div_iff₀ (zero_lt_iff.2 hr)] at hm
  exact absurd (key m) (not_le.2 hm)

theorem exists_row {n : ℕ} {σ : E ≃+* E} (hσ : Isom σ) (t : Fin n → Eˣ) {r ρ : ValueGroupWithZero E} (hr : r ≤ ρ)
    (hρ : ρ < 1) (ht : ∀ j l, j < l → valuation E ((t j : E) / t l) ≤ ρ) (b c : Matrix (Fin n) (Fin n) E)
    (hcb : c * b = 1) (hb1 : ∀ j l, valuation E (b j l) ≤ 1) (hc1 : ∀ j l, valuation E (c j l) ≤ 1)
    (hbd : ∀ j, valuation E (b j j) = 1) (hcd : ∀ j, valuation E (c j j) = 1)
    (hbl : ∀ j l, l < j → valuation E (b j l) ≤ r)
    (hcu : ∀ j l, j < l → valuation E ((t j : E) / t l * c j l) ≤ r) (i : Fin n) :
    ∃ (x : Fin n → E) (μ : E), valuation E (μ - c i i) ≤ r ∧
      (∀ l, valuation E (x l - (1 : Matrix (Fin n) (Fin n) E) i l) ≤ r) ∧
      ∀ j, x j * t j * μ = t i * ∑ l, σ (x l) * c l j := by
  classical
  have hr1 : r < 1 := hr.trans_lt hρ
  have hσ' : ∀ x, valuation E (σ.symm x) = valuation E x := fun x => by rw [← hσ, RingEquiv.apply_symm_apply]
  set e : Fin n → E := fun l => (1 : Matrix (Fin n) (Fin n) E) i l with he
  let y : (Fin n → E) → Fin n → E := fun x j => ∑ l, σ (x l) * c l j
  let w : (Fin n → E) → Fin n → E := fun x l => if l < i then (t l : E) / t i * (x l * y x i) else y x l
  let F : (Fin n → E) → Fin n → E := fun x j =>
    if j < i then σ.symm (∑ l, w x l * b l j) else if i < j then (t i : E) / t j * (y x j * (y x i)⁻¹) else 1
  have he1 : ∀ l, valuation E (e l) ≤ 1 := fun l => by
    simp only [he, one_apply]; split_ifs <;> simp
  have hx1 : ∀ x : Fin n → E, (∀ l, valuation E (x l - e l) ≤ r) → ∀ l, valuation E (x l) ≤ 1 := fun x hx l => by
    rw [← sub_add_cancel (x l) (e l)]
    exact Valuation.map_add_le _ ((hx l).trans hr1.le) (he1 l)
  have hy : ∀ (x x' : Fin n → E) γ, (∀ l, Nr γ (x l) (x' l)) → ∀ j, Nr γ (y x j) (y x' j) := fun x x' γ h j =>
    Nr.sum fun l => ((h l).map hσ).mul (.const (hc1 l j))
  have hye : ∀ j, y e j = c i j := fun j => by
    simp [y, he, one_apply, apply_ite σ]
  have hyc : ∀ x : Fin n → E, (∀ l, valuation E (x l - e l) ≤ r) → ∀ j, Nr r (y x j) (c i j) := fun x hx j =>
    hye j ▸ hy x e r (fun l => ⟨hx1 x hx l, he1 l, hx l⟩) j
  have hμ : ∀ x : Fin n → E, (∀ l, valuation E (x l - e l) ≤ r) → valuation E (y x i) = 1 := fun x hx => by
    rw [← sub_add_cancel (y x i) (c i i), Valuation.map_add_eq_of_lt_right, hcd]
    exact hcd i ▸ (hyc x hx i).2.2.trans_lt hr1
  obtain ⟨x, hx, hF⟩ := exists_fixed e r ρ hρ F (fun x hx j => by
      rcases lt_trichotomy j i with h | h | h
      · simp only [F, if_pos h, he, one_apply_ne h.ne', sub_zero, hσ']
        refine Valuation.map_sum_le _ fun l _ => ?_
        rw [map_mul]
        by_cases hl : l < i
        · refine (mul_le_of_le_one_right' (hb1 l j)).trans ?_
          have := hx l
          simp only [he, one_apply_ne hl.ne', sub_zero] at this
          simp only [w, if_pos hl, map_mul, hμ x hx, mul_one]
          exact (mul_le_of_le_one_left' ((ht l i hl).trans hρ.le)).trans this
        · simp only [w, if_neg hl]
          exact (mul_le_of_le_one_left' (hyc x hx l).1).trans (hbl l j (h.trans_le (not_lt.1 hl)))
      · simp [F, h, he]
      · simp only [F, if_neg h.not_gt, if_pos h, he, one_apply_ne h.ne, sub_zero]
        rw [← mul_assoc, map_mul, map_inv₀, hμ x hx, inv_one, mul_one, ← sub_add_cancel (y x j) (c i j), mul_add]
        refine Valuation.map_add_le _ ?_ (hcu i j h)
        rw [map_mul]
        exact (mul_le_of_le_one_left' ((ht i j h).trans hρ.le)).trans (hyc x hx j).2.2)
    (fun x x' γ hx hx' hd j => by
      have hN : ∀ l, Nr γ (x l) (x' l) := fun l => ⟨hx1 x hx l, hx1 x' hx' l, hd l⟩
      rcases lt_trichotomy j i with h | h | h
      · simp only [F, if_pos h]
        refine ((Nr.sum fun l => ?_).map hσ').2.2
        by_cases hl : l < i
        · simp only [w, if_pos hl]
          exact (((hN l).mul (hy x x' γ hN i)).small (ht l i hl) hρ.le).mul (.const (hb1 l j))
        · simp only [w, if_neg hl, mul_comm _ (b l j)]
          exact (hy x x' γ hN l).small ((hbl l j (h.trans_le (not_lt.1 hl))).trans hr) hρ.le
      · simp [F, h]
      · simp only [F, if_neg h.not_gt, if_pos h]
        exact (((hy x x' γ hN j).mul ((hy x x' γ hN i).inv (hμ x hx) (hμ x' hx'))).small (ht i j h) hρ.le).2.2)
  have hμ0 : y x i ≠ 0 := fun h => by simpa [h] using hμ x hx
  have hw : ∀ l, w x l = y x l := fun l => by
    have := vecMul_bound b hb1 hbd (fun j l h => (hbl j l h).trans_lt hr1) i (fun l => w x l - y x l) 0
      (fun l hl => by simp only [w, if_neg (not_lt.2 (show i ≤ l from hl)), sub_self]) (fun j hj => by
        have h1 := congrFun hF j
        simp only [F, if_pos (show j < i from hj), RingEquiv.symm_apply_eq] at h1
        have h2 : ∑ l, y x l * b l j = σ (x j) := by
          have : (fun l => σ (x l)) ᵥ* c ᵥ* b = fun l => σ (x l) := by rw [vecMul_vecMul, hcb, vecMul_one]
          exact congrFun this j
        simp only [sub_mul, Finset.sum_sub_distrib, h1, h2, sub_self, map_zero, le_refl]) l
    simpa [sub_eq_zero] using this
  refine ⟨x, y x i, (hyc x hx i).2.2, hx, fun j => ?_⟩
  show _ = _ * y x j
  have h1 := congrFun hF j
  rcases lt_trichotomy j i with h | h | h
  · rw [← hw j]
    simp only [w, if_pos h]
    field_simp
  · subst h
    simp only [F, lt_irrefl, if_false] at h1
    rw [← h1, one_mul]
  · simp only [F, if_neg h.not_gt, if_pos h] at h1
    rw [← h1]
    field_simp

open GlobalTheory.PRep GlobalTheory.SmGL in

theorem exists_conj {n : ℕ} {σ : E ≃+* E} (hσ : Isom σ) (t : Fin n → Eˣ) {r ρ : ValueGroupWithZero E} (hr : r ≤ ρ)
    (hρ : ρ < 1) (ht : ∀ j l, j < l → valuation E ((t j : E) / t l) ≤ ρ) (b : GL (Fin n) E)
    (hb1 : ∀ j l, valuation E (b.val j l) ≤ 1) (hc1 : ∀ j l, valuation E (b⁻¹.val j l) ≤ 1)
    (hbd : ∀ j, valuation E (b.val j j) = 1) (hcd : ∀ j, valuation E (b⁻¹.val j j) = 1)
    (hbl : ∀ j l, l < j → valuation E (b.val j l) ≤ r)
    (hcu : ∀ j l, j < l → valuation E ((t j : E) / t l * b⁻¹.val j l) ≤ r) :
    ∃ k ∈ ball n r, (∀ i j, valuation E (k⁻¹.val i j) ≤ 1) ∧ ∃ s : Fin n → Eˣ,
      (∀ i, valuation E ((((s i)⁻¹ : Eˣ) : E) - b⁻¹.val i i) ≤ r) ∧
      diagT E (Fin n) t * b = k⁻¹ * diagT E (Fin n) (t * s) * sg σ k := by
  classical
  have hr1 : r < 1 := hr.trans_lt hρ
  choose x μ hμ hx hxe using exists_row hσ t hr hρ ht b.val b⁻¹.val b.inv_mul hb1 hc1 hbd hcd hbl hcu
  have hμ0 : ∀ i, μ i ≠ 0 := fun i h => by
    have := hμ i
    rw [h, zero_sub, Valuation.map_neg, hcd] at this
    exact absurd this (not_le.2 hr1)
  let M : Matrix (Fin n) (Fin n) E := Matrix.of x
  have hoff : ∀ j l, j ≠ l → valuation E (M j l) < 1 := fun j l h => by
    simpa [M, one_apply_ne h] using (hx j l).trans_lt hr1
  have hd : ∀ j, valuation E (M j j) = 1 := fun j => by
    have := (hx j j).trans_lt hr1
    rw [one_apply_eq] at this
    show valuation E (x j j) = 1
    rw [← sub_add_cancel (x j j) 1, Valuation.map_add_eq_of_lt_right] <;> simpa using this
  have hbd := vecMul_bound M (fun j l => by
    by_cases h : j = l
    · exact h ▸ (hd j).le
    · exact (hoff j l h).le) hd (fun j l h => hoff j l h.ne') n
  have hu : IsUnit M := by
    refine vecMul_injective_iff_isUnit.1 fun u v huv => funext fun l => ?_
    have := hbd (u - v) 0 (fun l hl => absurd l.2 (not_lt.2 hl)) (fun j _ => by
      have : (u - v) ᵥ* M = 0 := by rw [sub_vecMul, sub_eq_zero]; exact huv
      exact le_of_eq ((map_eq_zero _).2 (congrFun this j))) l
    simpa [sub_eq_zero] using this
  obtain ⟨k, hk⟩ := hu
  refine ⟨k, fun i j => by rw [hk]; exact hx i j, fun i j => ?_, fun i => (Units.mk0 _ (hμ0 i))⁻¹,
    fun i => by simpa using hμ i, ?_⟩
  · refine hbd (fun l => k⁻¹.val i l) 1 (fun l hl => absurd l.2 (not_lt.2 hl)) (fun j _ => ?_) j
    rw [← hk, ← mul_apply, k.inv_mul, one_apply]
    split_ifs <;> simp
  · rw [mul_assoc, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← eq_mul_inv_iff_mul_eq, mul_assoc]
    ext i j
    rw [Units.val_mul, Units.val_mul, Units.val_mul, val_diagT, val_diagT, mul_diagonal, diagonal_mul, mul_apply]
    have h2 : ∀ l, (sg σ k).val i l = σ (x i l) := fun l => by
      show σ (k.val i l) = _
      rw [hk]; rfl
    simp only [h2, Pi.mul_apply, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [mul_right_comm, ← hxe, hk, mul_inv_cancel_right₀ (hμ0 i)]
    rfl

end UpperTheory.ConvolutionTheory.Loc
