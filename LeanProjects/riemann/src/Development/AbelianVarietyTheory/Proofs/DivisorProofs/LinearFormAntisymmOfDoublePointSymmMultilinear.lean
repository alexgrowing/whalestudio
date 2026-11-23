import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.MultiLevel

noncomputable def lin {κ : Type} (l : κ →₀ ℤ) : MvPolynomial κ ℝ := l.sum fun x z => C (z : ℝ) * X x

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial in
open Classical in
private theorem exists_fin_sum_single_eq_of_degree_eq {κ : Type} :
    ∀ (n : ℕ) (m : κ →₀ ℕ), m.degree = n → ∃ s : Fin n → κ, ∑ i, Finsupp.single (s i) 1 = m := by
  intro n
  induction n with
  | zero =>
    intro m hm
    refine ⟨Fin.elim0, ?_⟩
    rw [Finsupp.degree_eq_zero_iff] at hm
    simp [hm]
  | succ n ih =>
    intro m hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp at hm
    obtain ⟨x, hx⟩ := Finsupp.ne_iff.mp hm0
    have hle : Finsupp.single x 1 ≤ m := by
      rw [Finsupp.single_le_iff]
      simp only [Finsupp.coe_zero, Pi.zero_apply] at hx
      omega
    have hsplit : m - Finsupp.single x 1 + Finsupp.single x 1 = m := tsub_add_cancel_of_le hle
    have hdeg : (m - Finsupp.single x 1).degree = n := by
      have h := congrArg Finsupp.degree hsplit
      rw [map_add, Finsupp.degree_single, hm] at h
      omega
    obtain ⟨s, hs⟩ := ih _ hdeg
    refine ⟨Fin.cons x s, ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hs, add_comm, hsplit]

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial in
open Classical in

theorem _root_.GlobalTheory.FlagPush.MultiLevel.antisymm_of_multilinear : ∀ (κ : Type) (a b : κ), a ≠ b → ∀ (A : Type) [AddCommGroup A] (n : ℕ) (T : MultilinearMap ℤ (fun _ : Fin (n + 1) => A) ℤ), (∀ (σ : Equiv.Perm (Fin (n + 1))) (y : Fin (n + 1) → A), T (y ∘ σ) = T y) → ∀ (u v : κ → A) (L : MvPolynomial κ ℝ →ₗ[ℝ] ℝ) (μ : ℤ), μ ≠ 0 → (∀ x, x ≠ a → x ≠ b → u x = v x) → u a + u b = v a + v b → (∀ s : Fin (n + 1) → κ, T (u ∘ s) = 0) → (∀ s : Fin (n + 1) → κ, T (v ∘ s) = 0) → (∀ (k : ℕ) (P : MvPolynomial κ ℝ), P.IsHomogeneous k → k ≠ n → L P = 0) → (∀ s : Fin n → κ ⊕ κ, ((T (Fin.cons (v b - u a) (Sum.elim u v ∘ s)) : ℤ) : ℝ) = μ * L (∏ i, X (Sum.elim id id (s i)))) → ∀ Q : MvPolynomial κ ℝ, L (rename (Equiv.swap a b) Q) = - L Q := by
  intro κ a b hab A _ n T hT u v L μ hμ hoff hsum hu hv hL hmix
  set w := v b - u a with hw
  set d := u a - v a with hd
  have hcons : ∀ (x y : A) (Z : Fin n → A),
      T (Fin.cons (x - y) Z) = T (Fin.cons x Z) - T (Fin.cons y Z) := by
    intro x y Z
    simp only [← MultilinearMap.curryLeft_apply, map_sub, MultilinearMap.sub_apply]
  have hmixeq : ∀ t t' : Fin n → κ ⊕ κ, (∀ i, Sum.elim id id (t i) = Sum.elim id id (t' i)) →
      T (Fin.cons w (Sum.elim u v ∘ t)) = T (Fin.cons w (Sum.elim u v ∘ t')) := by
    intro t t' htt
    have h1 := hmix t
    have h2 := hmix t'
    have e : (∏ i, X (Sum.elim id id (t i)) : MvPolynomial κ ℝ) = ∏ i, X (Sum.elim id id (t' i)) := by
      simp only [htt]
    rw [e, ← h2] at h1
    exact_mod_cast h1
  have hZ : ∀ (t : Fin n → κ ⊕ κ) (k : Fin n),
      T (Fin.cons w (Function.update (Sum.elim u v ∘ t) k d)) = 0 := by
    intro t k
    rw [Fin.cons_update, hd, T.map_update_sub, ← Fin.cons_update, ← Fin.cons_update]
    have e1 : Function.update (Sum.elim u v ∘ t) k (u a) =
        Sum.elim u v ∘ Function.update t k (Sum.inl a) := by
      funext i
      by_cases h : i = k <;> simp [h, Function.update_apply]
    have e2 : Function.update (Sum.elim u v ∘ t) k (v a) =
        Sum.elim u v ∘ Function.update t k (Sum.inr a) := by
      funext i
      by_cases h : i = k <;> simp [h, Function.update_apply]
    rw [e1, e2, sub_eq_zero]
    apply hmixeq
    intro i
    by_cases h : i = k <;> simp [h, Function.update_apply]
  have hposition : ∀ (Y : Fin n → A) (k : Fin n),
      T (Fin.cons d (Function.update Y k w)) = T (Fin.cons w (Function.update Y k d)) := by
    intro Y k
    rw [← hT (Equiv.swap 0 k.succ) (Fin.cons d (Function.update Y k w))]
    congr 1
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [Equiv.swap_apply_left]
    · by_cases h : i = k
      · subst h
        simp only [Function.comp_apply, Equiv.swap_apply_right, Fin.cons_zero, Fin.cons_succ,
          Function.update_self]
      · have hne : i.succ ≠ k.succ := fun e => h (Fin.succ_injective _ e)
        simp only [Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i) hne]
        simp [h]
  have hw' : w = u b - v a := by
    rw [hw, sub_eq_sub_iff_add_eq_add, add_comm (v b), add_comm (u b)]
    exact hsum.symm
  have hva : v a = u a - d := by rw [hd, sub_sub_cancel]
  have hua : u a = v a + d := by rw [hd, add_sub_cancel]
  have hu_side : ∀ s' : Fin n → κ, T (Fin.cons w (u ∘ s')) = T (Fin.cons d (u ∘ s')) := by
    intro s'
    have h1 : T (Fin.cons (u b) (u ∘ s')) = 0 := by rw [← Fin.comp_cons]; exact hu _
    have h2 : T (Fin.cons (u a) (u ∘ s')) = 0 := by rw [← Fin.comp_cons]; exact hu _
    rw [hw', hcons, hva, hcons, h1, h2]
    abel
  have hv_side : ∀ s' : Fin n → κ, T (Fin.cons w (v ∘ s')) = - T (Fin.cons d (v ∘ s')) := by
    intro s'
    have h1 : T (Fin.cons (v b) (v ∘ s')) = 0 := by rw [← Fin.comp_cons]; exact hv _
    have h2 : T (Fin.cons (v a) (v ∘ s')) = 0 := by rw [← Fin.comp_cons]; exact hv _
    rw [hw, hcons, h1, hua]
    simp only [← MultilinearMap.curryLeft_apply, map_add, MultilinearMap.add_apply] at h2 ⊢
    rw [h2]
    abel
  have hdiff : ∀ x : κ, ∃ ε : ℤ, u (Equiv.swap a b x) - v x = ε • w := by
    intro x
    by_cases hxa : x = a
    · subst hxa
      refine ⟨1, ?_⟩
      rw [Equiv.swap_apply_left, one_smul, hw']
    · by_cases hxb : x = b
      · subst hxb
        refine ⟨-1, ?_⟩
        rw [Equiv.swap_apply_right, neg_smul, one_smul, hw]
        abel
      · refine ⟨0, ?_⟩
        rw [Equiv.swap_apply_of_ne_of_ne hxa hxb, hoff x hxa hxb, sub_self, zero_smul]
  have hchain : ∀ s : Fin n → κ, T (Fin.cons d (v ∘ s)) = T (Fin.cons d (u ∘ Equiv.swap a b ∘ s)) := by
    intro s
    let Y : ℕ → Fin n → A := fun k i => if (i : ℕ) < k then u (Equiv.swap a b (s i)) else v (s i)
    have hY : ∀ k, ∃ t : Fin n → κ ⊕ κ, Y k = Sum.elim u v ∘ t := by
      intro k
      refine ⟨fun i => if (i : ℕ) < k then Sum.inl (Equiv.swap a b (s i)) else Sum.inr (s i), ?_⟩
      funext i
      simp only [Y, Function.comp_apply]
      split_ifs <;> rfl
    have hstep : ∀ k, T (Fin.cons d (Y k)) = T (Fin.cons d (Y 0)) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [← ih]
        by_cases hk : k < n
        · let K : Fin n := ⟨k, hk⟩
          have e1 : Y (k + 1) = Function.update (Y k) K (u (Equiv.swap a b (s K))) := by
            funext i
            by_cases hi : i = K
            · subst hi
              simp [Y, K]
            · have hik : (i : ℕ) ≠ k := fun e => hi (Fin.ext e)
              simp only [Y, Function.update_apply, hi, if_false]
              by_cases hlt : (i : ℕ) < k
              · rw [if_pos hlt, if_pos (by omega)]
              · rw [if_neg hlt, if_neg (by omega)]
          have e0 : Y k = Function.update (Y k) K (v (s K)) := by
            rw [eq_comm, Function.update_eq_self_iff]
            simp [Y, K]
          obtain ⟨ε, hε⟩ := hdiff (s K)
          obtain ⟨t, ht⟩ := hY k
          rw [← sub_eq_zero, e1]
          conv_lhs => rw [e0]
          rw [Function.update_idem, Fin.cons_update, Fin.cons_update, ← T.map_update_sub,
            ← Fin.cons_update, hε, Fin.cons_update, T.map_update_smul, ← Fin.cons_update, hposition, ht,
            hZ, smul_zero]
        · have e : Y (k + 1) = Y k := by
            funext i
            have h1 : (i : ℕ) < k := by omega
            have h2 : (i : ℕ) < k + 1 := by omega
            simp [Y, h1, h2]
          rw [e]
    have e0 : Y 0 = v ∘ s := by
      funext i
      simp [Y]
    have en : Y n = u ∘ Equiv.swap a b ∘ s := by
      funext i
      simp [Y, i.2]
    rw [← e0, ← en]
    exact (hstep n).symm
  have hkey : ∀ s : Fin n → κ,
      T (Fin.cons w (u ∘ Equiv.swap a b ∘ s)) = - T (Fin.cons w (u ∘ s)) := by
    intro s
    have hm := hmixeq (Sum.inl ∘ s) (Sum.inr ∘ s) (fun i => rfl)
    have el : Sum.elim u v ∘ (Sum.inl ∘ s) = u ∘ s := rfl
    have er : Sum.elim u v ∘ (Sum.inr ∘ s) = v ∘ s := rfl
    rw [el, er] at hm
    rw [hm, hv_side, hchain, ← hu_side (Equiv.swap a b ∘ s), neg_neg]
  have hmono : ∀ s : Fin n → κ,
      L (∏ i, X (Equiv.swap a b (s i))) = - L (∏ i, X (s i)) := by
    intro s
    have hμR : (μ : ℝ) ≠ 0 := by exact_mod_cast hμ
    have h1 := hmix (Sum.inl ∘ s)
    have h2 := hmix (Sum.inl ∘ (Equiv.swap a b ∘ s))
    have el : Sum.elim u v ∘ (Sum.inl ∘ s) = u ∘ s := rfl
    have el' : Sum.elim u v ∘ (Sum.inl ∘ (Equiv.swap a b ∘ s)) = u ∘ Equiv.swap a b ∘ s := rfl
    rw [el] at h1
    rw [el', hkey] at h2
    simp only [Function.comp_apply, Sum.elim_inl, id] at h1 h2
    apply mul_left_cancel₀ hμR
    rw [← h2, mul_neg, ← h1]
    push_cast
    ring
  have hlin : L ∘ₗ (rename (Equiv.swap a b) : MvPolynomial κ ℝ →ₐ[ℝ] MvPolynomial κ ℝ).toLinearMap = -L := by
    refine (basisMonomials κ ℝ).ext fun m => ?_
    simp only [coe_basisMonomials, LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.neg_apply]
    by_cases hm : m.degree = n
    · obtain ⟨s, hs⟩ := exists_fin_sum_single_eq_of_degree_eq n m hm
      have e1 : monomial m (1 : ℝ) = ∏ i, X (s i) := by
        rw [← hs, monomial_sum_one]
        rfl
      rw [e1, map_prod]
      simp only [rename_X]
      exact hmono s
    · rw [hL _ _ (isHomogeneous_monomial (1 : ℝ) rfl) hm,
        hL _ _ (isHomogeneous_monomial (1 : ℝ) rfl).rename_isHomogeneous hm, neg_zero]
  intro Q
  exact LinearMap.congr_fun hlin Q

end GlobalTheory.FlagPush.MultiLevel
