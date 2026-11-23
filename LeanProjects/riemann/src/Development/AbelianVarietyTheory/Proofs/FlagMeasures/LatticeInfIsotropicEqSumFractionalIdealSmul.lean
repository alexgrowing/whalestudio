import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Ia

noncomputable section

open NumberField

namespace GlobalTheory.RowLatAssembly

open Formalism.MainNotions.S

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T : E}

lemma Xa_le_X (F : FlagG S r T) (j : ℕ) : F.Xa j ≤ F.X := by
  unfold FlagG.Xa FlagG.X
  exact Submodule.span_mono (Set.image_subset_range _ _)

lemma X_eq_Xa (F : FlagG S r T) : F.X = F.Xa r := by
  unfold FlagG.Xa FlagG.X
  congr 1
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.isLt, rfl⟩
  · rintro ⟨i, -, rfl⟩
    exact ⟨i, rfl⟩

lemma e_mem (F : FlagG S r T) (a : Fin r) : F.e a ∈ F.Xa (a.val + 1) := by
  unfold FlagG.Xa
  exact Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩

private lemma coefX_linearCombination_eq (F : FlagG S r T) (l : Fin r →₀ E) (a : Fin r) :
    F.coefX (Finsupp.linearCombination E F.e l) a = l a := by
  have hmem : Finsupp.linearCombination E F.e l ∈ Submodule.span E (Set.range F.e) := by
    rw [← Finsupp.range_linearCombination]
    exact LinearMap.mem_range_self _ l
  unfold FlagG.coefX
  rw [dif_pos hmem, F.e_indep.repr_eq (l := l) rfl]

private lemma exists_linearCombination_eq_of_mem_flagX (F : FlagG S r T) {y : S.V} (hy : y ∈ F.X) :
    ∃ l : Fin r →₀ E, Finsupp.linearCombination E F.e l = y := by
  unfold FlagG.X at hy
  rw [← Finsupp.range_linearCombination] at hy
  exact LinearMap.mem_range.mp hy

lemma coefX_add (F : FlagG S r T) (a : Fin r) {x y : S.V} (hx : x ∈ F.X) (hy : y ∈ F.X) :
    F.coefX (x + y) a = F.coefX x a + F.coefX y a := by
  obtain ⟨l, rfl⟩ := exists_linearCombination_eq_of_mem_flagX F hx
  obtain ⟨m, rfl⟩ := exists_linearCombination_eq_of_mem_flagX F hy
  rw [← map_add, coefX_linearCombination_eq, coefX_linearCombination_eq, coefX_linearCombination_eq, Finsupp.add_apply]

lemma coefX_smul (F : FlagG S r T) (a : Fin r) (c : E) {x : S.V} (hx : x ∈ F.X) :
    F.coefX (c • x) a = c * F.coefX x a := by
  obtain ⟨l, rfl⟩ := exists_linearCombination_eq_of_mem_flagX F hx
  rw [← map_smul, coefX_linearCombination_eq, coefX_linearCombination_eq, Finsupp.smul_apply, smul_eq_mul]

lemma coefX_e (F : FlagG S r T) (i a : Fin r) :
    F.coefX (F.e i) a = if i = a then 1 else 0 := by
  have h : F.e i = Finsupp.linearCombination E F.e (Finsupp.single i 1) := by simp
  rw [h, coefX_linearCombination_eq, Finsupp.single_apply]

lemma mem_Xa_of_coefX_eq_zero (F : FlagG S r T) (a : Fin r) {y : S.V} (hy : y ∈ F.Xa (a.val + 1))
    (h0 : F.coefX y a = 0) : y ∈ F.Xa a.val := by
  unfold FlagG.Xa at hy ⊢
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination (R := E)).mp hy
  rw [coefX_linearCombination_eq] at h0
  refine (Finsupp.mem_span_image_iff_linearCombination (R := E)).mpr ⟨l, ?_, rfl⟩
  rw [Finsupp.mem_supported'] at hl ⊢
  intro i hi
  simp only [Set.mem_ofPred_eq, not_lt] at hi
  rcases lt_or_eq_of_le hi with h | h
  · exact hl i (by simp only [Set.mem_ofPred_eq]; omega)
  · have hia : i = a := Fin.ext h.symm
    rw [hia]
    exact h0

lemma sub_smul_mem (F : FlagG S r T) (a : Fin r) {y w : S.V} (hy : y ∈ F.Xa (a.val + 1))
    (hw : w ∈ F.Xa (a.val + 1)) (hw1 : F.coefX w a = 1) :
    y - F.coefX y a • w ∈ F.Xa a.val := by
  have hyX := Xa_le_X F _ hy
  have hwX := Xa_le_X F _ hw
  apply mem_Xa_of_coefX_eq_zero F a (Submodule.sub_mem _ hy (Submodule.smul_mem _ _ hw))
  rw [sub_eq_add_neg, ← neg_smul, coefX_add F a hyX (Submodule.smul_mem _ _ hwX),
    coefX_smul F a _ hwX, hw1]
  ring

lemma exists_section (F : FlagG S r T) (Λ : Submodule (𝓞 E) S.V)
    (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hJ : J ≠ 0) (a : Fin r)
    (h3 : ∀ t : E, t ∈ J → ∃ x ∈ Λ, x ∈ F.Xa (a.val + 1) ∧ F.coefX x a = t) :
    ∃ w ∈ F.Xa (a.val + 1), F.coefX w a = 1 ∧ ∀ t ∈ J, t • w ∈ Λ := by

  have key : ∀ s ∈ J * J⁻¹, ∃ w ∈ F.Xa (a.val + 1), F.coefX w a = s ∧ ∀ t ∈ J, t • w ∈ Λ := by
    intro s hs
    refine FractionalIdeal.mul_induction_on hs ?_ ?_
    · intro i hi j hj
      obtain ⟨x, hxΛ, hxX, hxc⟩ := h3 i hi
      refine ⟨j • x, Submodule.smul_mem _ j hxX, ?_, ?_⟩
      · rw [coefX_smul F a j (Xa_le_X F _ hxX), hxc, mul_comm]
      · intro t ht
        have htj : t * j ∈ J * J⁻¹ := FractionalIdeal.mul_mem_mul ht hj
        rw [mul_inv_cancel₀ hJ, FractionalIdeal.mem_one_iff] at htj
        obtain ⟨o, ho⟩ := htj
        rw [smul_smul, ← ho, algebraMap_smul]
        exact Λ.smul_mem o hxΛ
    · rintro s₁ s₂ ⟨w₁, hw₁, hc₁, hΛ₁⟩ ⟨w₂, hw₂, hc₂, hΛ₂⟩
      refine ⟨w₁ + w₂, Submodule.add_mem _ hw₁ hw₂, ?_, ?_⟩
      · rw [coefX_add F a (Xa_le_X F _ hw₁) (Xa_le_X F _ hw₂), hc₁, hc₂]
      · intro t ht
        rw [smul_add]
        exact Λ.add_mem (hΛ₁ t ht) (hΛ₂ t ht)
  have h1 : (1 : E) ∈ J * J⁻¹ := by
    rw [mul_inv_cancel₀ hJ, FractionalIdeal.mem_one_iff]
    exact ⟨1, map_one _⟩
  exact key 1 h1

theorem xLam_eq_span : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (r : ℕ) (T : E) (G : Formalism.MainNotions.S.Lat.LFlag S r T) (Λ : Submodule (𝓞 E) S.V) (J : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E), (∀ a, J a ≠ 0) → (∀ (a : Fin r) (x : S.V), x ∈ Λ → x ∈ G.fl.Xa (a.val + 1) → G.fl.coefX x a ∈ J a) → (∀ (a : Fin r) (t : E), t ∈ J a → ∃ x ∈ Λ, x ∈ G.fl.Xa (a.val + 1) ∧ G.fl.coefX x a = t) → ∃ e' : Fin r → S.V, (∀ a, e' a - G.fl.e a ∈ G.fl.Xa a.val) ∧ Formalism.MainNotions.S.Lat.XLam Λ G = Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ J a ∧ y = x • e' a} := by
  intro E _ _ _ S r T G Λ J hJ h2 h3
  have hsec : ∀ a : Fin r, ∃ w ∈ G.fl.Xa (a.val + 1), G.fl.coefX w a = 1 ∧ ∀ t ∈ J a, t • w ∈ Λ :=
    fun a => exists_section G.fl Λ (J a) (hJ a) a (h3 a)
  choose e' he'X he'c he'Λ using hsec
  refine ⟨e', fun a => ?_, ?_⟩
  · have hea : G.fl.coefX (G.fl.e a) a = 1 := by rw [coefX_e, if_pos rfl]
    have h := sub_smul_mem G.fl a (he'X a) (e_mem G.fl a) hea
    rwa [he'c a, one_smul] at h
  · apply le_antisymm
    ·
      have step : ∀ j : ℕ, j ≤ r → ∀ v ∈ Λ, v ∈ G.fl.Xa j →
          v ∈ Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ J a ∧ y = x • e' a} := by
        intro j
        induction j with
        | zero =>
          intro _ v _ hv
          have hv0 : v = 0 := by
            unfold Formalism.MainNotions.S.FlagG.Xa at hv
            simpa using hv
          rw [hv0]
          exact Submodule.zero_mem _
        | succ j ih =>
          intro hj v hvΛ hv
          obtain ⟨a, rfl⟩ : ∃ a : Fin r, a.val = j := ⟨⟨j, hj⟩, rfl⟩
          have hc : G.fl.coefX v a ∈ J a := h2 a v hvΛ hv
          have hrest : v - G.fl.coefX v a • e' a ∈ G.fl.Xa a.val :=
            sub_smul_mem G.fl a hv (he'X a) (he'c a)
          have hrestΛ : v - G.fl.coefX v a • e' a ∈ Λ := Λ.sub_mem hvΛ (he'Λ a _ hc)
          have hlow := ih (Nat.le_of_succ_le hj) _ hrestΛ hrest
          have htop : G.fl.coefX v a • e' a ∈
              Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ J a ∧ y = x • e' a} :=
            Submodule.subset_span ⟨a, _, hc, rfl⟩
          have hsum := Submodule.add_mem _ hlow htop
          rwa [sub_add_cancel] at hsum
      intro v hv
      obtain ⟨hvΛ, hvX⟩ : v ∈ Λ ∧ v ∈ G.fl.X := hv
      rw [X_eq_Xa] at hvX
      exact step r le_rfl v hvΛ hvX
    · rw [Submodule.span_le]
      rintro y ⟨a, x, hx, rfl⟩
      show x • e' a ∈ Λ ⊓ Formalism.MainNotions.S.Lat.toO S (Formalism.MainNotions.S.Lat.Xsp G)
      exact Submodule.mem_inf.mpr ⟨he'Λ a x hx, (G.fl.X).smul_mem x (Xa_le_X G.fl _ (he'X a))⟩

end GlobalTheory.RowLatAssembly
