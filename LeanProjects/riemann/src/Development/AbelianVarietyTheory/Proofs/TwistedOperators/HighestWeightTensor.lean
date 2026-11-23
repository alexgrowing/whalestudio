import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.TensorHW

variable {p q : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]

lemma same_refl (a : Ix p q) : sameBlock a a := by
  cases a <;> trivial

lemma same_of_pos {a b : Ix p q} (h : posC a b) : sameBlock a b := by
  cases a <;> cases b <;> simp_all [posC, sameBlock]

lemma same_of_pos' {a b : Ix p q} (h : posC a b) : sameBlock b a := by
  cases a <;> cases b <;> simp_all [posC, sameBlock]

lemma same_tri {a b : Ix p q} (h : sameBlock a b) : a = b ∨ posC a b ∨ posC b a := by
  rcases a with i | i <;> rcases b with j | j
  · rcases lt_trichotomy i j with h | h | h <;> simp [posC, h]
  · exact absurd h (by simp [sameBlock])
  · exact absurd h (by simp [sameBlock])
  · rcases lt_trichotomy i j with h | h | h <;> simp [posC, h]

lemma isKC_Eab {a b : Ix p q} (h : sameBlock a b) : IsKC (Eab a b) := by
  intro c d hcd
  rw [Eab, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hcd h

lemma isKC_diag (c : Ix p q → ℂ) : IsKC (Matrix.diagonal c : Mat p q) := by
  intro a b hab
  rw [Matrix.diagonal_apply, if_neg]
  rintro rfl
  exact hab (same_refl a)

lemma isKC_mul {Y Z : Mat p q} (hY : IsKC Y) (hZ : IsKC Z) : IsKC (Y * Z) := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hac : sameBlock a c
  · rw [hZ c b, mul_zero]
    intro hcb
    apply hab
    cases a <;> cases b <;> cases c <;> simp_all [sameBlock]
  · rw [hY a c hac, zero_mul]

lemma isKC_comm {Y Z : Mat p q} (hY : IsKC Y) (hZ : IsKC Z) : IsKC (Y * Z - Z * Y) := by
  intro a b hab
  rw [Matrix.sub_apply, isKC_mul hY hZ a b hab, isKC_mul hZ hY a b hab, sub_zero]

lemma kc_ind (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) (y : V)
    (h : ∀ a b, sameBlock a b → act (Eab a b) y ∈ N) {Z : Mat p q} (hZ : IsKC Z) : act Z y ∈ N := by
  rw [Matrix.matrix_eq_sum_single Z]
  simp only [map_sum, LinearMap.sum_apply]
  refine N.sum_mem fun a _ => N.sum_mem fun b _ => ?_
  by_cases hab : sameBlock a b
  · have : (Matrix.single a b (Z a b) : Mat p q) = Z a b • Eab a b := by
      rw [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul, LinearMap.smul_apply]
    exact N.smul_mem _ (h a b hab)
  · rw [hZ a b hab]
    simp

lemma lie_apply {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsKLieAct act) {Y Z : Mat p q}
    (hY : IsKC Y) (hZ : IsKC Z) (y : V) :
    act Y (act Z y) = act Z (act Y y) + act (Y * Z - Z * Y) y := by
  rw [hL Y Z hY hZ]
  simp

lemma diag_comm (c : Ix p q → ℂ) (a b : Ix p q) :
    (Matrix.diagonal c : Mat p q) * Eab a b - Eab a b * Matrix.diagonal c = (c a - c b) • Eab a b := by
  ext i j
  simp only [Eab, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply,
    Matrix.single_apply, smul_eq_mul]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    ring
  · ring

lemma eig_shift {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsKLieAct act) (c : Ix p q → ℂ)
    {a b : Ix p q} (hab : sameBlock a b) {t : ℂ} {y : V}
    (hy : y ∈ Module.End.eigenspace (act (Matrix.diagonal c)) t) :
    act (Eab a b) y ∈ Module.End.eigenspace (act (Matrix.diagonal c)) (t + (c a - c b)) := by
  rw [Module.End.mem_eigenspace_iff] at hy ⊢
  rw [lie_apply hL (isKC_diag c) (isKC_Eab hab), diag_comm, hy, map_smul, map_smul,
    LinearMap.smul_apply, add_smul]

lemma mem_wt {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {v : V} :
    v ∈ wtSub act μ ↔ ∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v := by
  simp [wtSub, Submodule.mem_iInf, sub_eq_zero]

lemma mem_hw {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {v : V} :
    v ∈ hwSub act μ ↔ (∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v) ∧
      ∀ a b, posC a b → act (Eab a b) v = 0 := by
  simp [hwSub, mem_wt, Submodule.mem_iInf]

lemma gen_top {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsKLieAct act) {μ : Ix p q → ℚ} {v : V}
    (hv : IsHW act μ v) (hirr : ∀ W, KStable act W → W = ⊥ ∨ W = ⊤) (N : Submodule ℂ V)
    (hvN : v ∈ N) (hN : ∀ a b, posC a b → ∀ y ∈ N, act (Eab b a) y ∈ N) : N = ⊤ := by
  obtain ⟨hv0, hv⟩ := hv
  rw [mem_hw] at hv
  set S : Set (Submodule ℂ V) :=
    {N | v ∈ N ∧ ∀ a b, posC a b → ∀ y ∈ N, act (Eab b a) y ∈ N} with hS
  have hG : sInf S ∈ S := by
    refine ⟨Submodule.mem_sInf.2 fun M hM => hM.1, fun a b hab y hy => ?_⟩
    exact Submodule.mem_sInf.2 fun M hM => hM.2 a b hab y (Submodule.mem_sInf.1 hy M hM)
  have hG' : (sInf S ⊓ ⨅ (Z : Mat p q) (_ : IsKC Z), (sInf S).comap (act Z)) ∈ S := by
    constructor
    · simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
      refine ⟨hG.1, fun Z hZ => kc_ind act _ v (fun a b hab => ?_) hZ⟩
      rcases same_tri hab with rfl | h | h
      · rw [hv.1]; exact Submodule.smul_mem _ _ hG.1
      · rw [hv.2 a b h]; exact Submodule.zero_mem _
      · exact hG.2 b a h v hG.1
    · intro a b hab y hy
      simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at hy ⊢
      refine ⟨hG.2 a b hab y hy.1, fun Z hZ => ?_⟩
      have hE := isKC_Eab (same_of_pos' hab)
      rw [lie_apply hL hZ hE]
      exact Submodule.add_mem _ (hG.2 a b hab _ (hy.2 Z hZ)) (hy.2 _ (isKC_comm hZ hE))
  have hK : KStable act (sInf S) := by
    intro Z hZ w hw
    have := sInf_le hG' hw
    simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at this
    exact this.2 Z hZ
  rcases hirr _ hK with h | h
  · have := hG.1
    rw [h] at this
    exact absurd this hv0
  · exact top_le_iff.1 (h ▸ sInf_le (show N ∈ S from ⟨hvN, hN⟩))

noncomputable def grad (p q : ℕ) : Ix p q → ℝ :=
  Sum.elim (fun i => -((i : ℕ) : ℝ)) (fun i => -((i : ℕ) : ℝ))

lemma grad_lt {a b : Ix p q} (h : posC a b) : grad p q b < grad p q a := by
  cases a <;> cases b <;> simp_all [posC, grad]

lemma exists_dual {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsKLieAct act) {μ : Ix p q → ℚ} {v : V}
    (hv : IsHW act μ v) (hirr : ∀ W, KStable act W → W = ⊥ ∨ W = ⊤) :
    ∃ φ : V →ₗ[ℂ] ℂ, φ v ≠ 0 ∧ (∀ a y, φ (act (Eab a a) y) = ((μ a : ℚ) : ℂ) * φ y) ∧
      ∀ a b, posC a b → ∀ y, φ (act (Eab b a) y) = 0 := by
  have hgen := gen_top hL hv hirr
  obtain ⟨hv0, hv⟩ := hv
  rw [mem_hw] at hv
  set c : Ix p q → ℂ := fun a => (grad p q a : ℂ) with hc
  set h : Module.End ℂ V := act (Matrix.diagonal c) with hh
  set m : ℂ := ∑ a, c a * ((μ a : ℚ) : ℂ) with hm
  have hvm : v ∈ h.eigenspace m := by
    rw [Module.End.mem_eigenspace_iff]
    have : (Matrix.diagonal c : Mat p q) = ∑ a, c a • Eab a a := by
      ext i j
      simp only [Matrix.sum_apply, Eab, Matrix.smul_apply, Matrix.single_apply, Matrix.diagonal_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    rw [hh, this, hm]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hv.1, Finset.sum_smul,
      mul_smul]
  set Q : Submodule ℂ V := ⨆ (t : ℂ) (_ : t.re < m.re), h.eigenspace t with hQ
  have hvQ : v ∉ Q := by
    intro hvQ
    have hd := Module.End.eigenspaces_iSupIndep h m
    have hle : Q ≤ ⨆ (j : ℂ) (_ : j ≠ m), h.eigenspace j := by
      refine iSup₂_le fun t ht => le_iSup₂_of_le t ?_ le_rfl
      rintro rfl
      exact lt_irrefl _ ht
    exact hv0 (Submodule.disjoint_def.1 hd v hvm (hle hvQ))
  have hshift : ∀ a b, sameBlock a b → ∀ t : ℂ, (t + (c a - c b)).re < m.re →
      ∀ y ∈ h.eigenspace t, act (Eab a b) y ∈ Q := by
    intro a b hab t ht y hy
    exact (le_iSup₂_of_le (f := fun (t : ℂ) (_ : t.re < m.re) => h.eigenspace t) _ ht le_rfl :
      _ ≤ Q) (eig_shift hL c hab hy)
  have hQst : ∀ a b, sameBlock a b → grad p q a ≤ grad p q b → ∀ y ∈ Q, act (Eab a b) y ∈ Q := by
    intro a b hab hle
    have : Q ≤ Q.comap (act (Eab a b)) := by
      refine iSup₂_le fun t ht y hy => hshift a b hab t ?_ y hy
      simp only [hc, Complex.add_re, Complex.sub_re, Complex.ofReal_re]
      linarith
    exact this
  have hvlow : ∀ a b, posC a b → act (Eab b a) v ∈ Q := by
    intro a b hab
    refine hshift b a (same_of_pos' hab) m ?_ v hvm
    simp only [hc, Complex.add_re, Complex.sub_re, Complex.ofReal_re]
    linarith [grad_lt hab]
  have hlow : ∀ a b, posC a b → ∀ y ∈ (ℂ ∙ v) ⊔ Q, act (Eab b a) y ∈ Q := by
    intro a b hab
    have : (ℂ ∙ v) ⊔ Q ≤ Q.comap (act (Eab b a)) := by
      refine sup_le ?_ (hQst b a (same_of_pos' hab) (grad_lt hab).le)
      rw [Submodule.span_singleton_le_iff_mem]
      exact hvlow a b hab
    exact this
  have htop : (ℂ ∙ v) ⊔ Q = ⊤ :=
    hgen _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self v))
      fun a b hab y hy => Submodule.mem_sup_right (hlow a b hab y hy)
  obtain ⟨φ, hφv, hφQ⟩ := Submodule.exists_le_ker_of_notMem hvQ
  refine ⟨φ, hφv, fun a y => ?_, fun a b hab y => hφQ (hlow a b hab y (htop ▸ Submodule.mem_top))⟩
  have hy : y ∈ (ℂ ∙ v) ⊔ Q := htop ▸ Submodule.mem_top
  obtain ⟨x, hx, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hx
  have h1 : φ z = 0 := hφQ hz
  have h2 : φ (act (Eab a a) z) = 0 := hφQ (hQst a a (same_refl a) le_rfl z hz)
  simp only [map_add, map_smul, hv.1, h1, h2, smul_eq_mul]
  ring

lemma ker_bot {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsKLieAct act) {μ : Ix p q → ℚ}
    (hirr : ∀ W, KStable act W → W = ⊥ ∨ W = ⊤) (φ : V →ₗ[ℂ] ℂ) {v : V} (hφ : φ v ≠ 0)
    (h1 : ∀ a y, φ (act (Eab a a) y) = ((μ a : ℚ) : ℂ) * φ y)
    (h2 : ∀ a b, posC a b → ∀ y, φ (act (Eab b a) y) = 0) (N : Submodule ℂ V)
    (hN : N ≤ LinearMap.ker φ) (hN' : ∀ a b, posC a b → N ≤ N.comap (act (Eab a b))) : N = ⊥ := by
  set S : Set (Submodule ℂ V) :=
    {N | N ≤ LinearMap.ker φ ∧ ∀ a b, posC a b → N ≤ N.comap (act (Eab a b))} with hS
  have hT : sSup S ∈ S := by
    refine ⟨sSup_le fun M hM => hM.1, fun a b hab => sSup_le fun M hM => ?_⟩
    exact (hM.2 a b hab).trans (Submodule.comap_mono (le_sSup hM))
  set T := sSup S with hTdef
  set T' := T ⊔ ⨆ (Z : Mat p q) (_ : IsKC Z), T.map (act Z) with hT'def
  have hmem : ∀ Z, IsKC Z → ∀ y ∈ T, act Z y ∈ T' := by
    intro Z hZ y hy
    exact Submodule.mem_sup_right ((le_iSup₂_of_le
      (f := fun (Z : Mat p q) (_ : IsKC Z) => T.map (act Z)) Z hZ le_rfl :
      T.map (act Z) ≤ _) (Submodule.mem_map_of_mem hy))
  have hT' : T' ∈ S := by
    constructor
    · refine sup_le hT.1 (iSup₂_le fun Z hZ => ?_)
      rintro _ ⟨y, hy, rfl⟩
      refine kc_ind act _ y (fun a b hab => ?_) hZ
      rcases same_tri hab with rfl | h | h
      · have : φ y = 0 := hT.1 hy
        rw [LinearMap.mem_ker, h1, this, mul_zero]
      · exact hT.1 (hT.2 a b h hy)
      · exact h2 b a h y
    · intro a b hab
      have hE := isKC_Eab (same_of_pos hab)
      refine sup_le (fun y hy => hmem _ hE y hy) (iSup₂_le fun Z hZ => ?_)
      rintro _ ⟨y, hy, rfl⟩
      rw [Submodule.mem_comap, lie_apply hL hE hZ]
      exact Submodule.add_mem _ (hmem Z hZ _ (hT.2 a b hab hy)) (hmem _ (isKC_comm hE hZ) y hy)
  have hK : KStable act T := fun Z hZ y hy => le_sSup hT' (hmem Z hZ y hy)
  rcases hirr _ hK with h | h
  · exact le_bot_iff.1 (h ▸ le_sSup (show N ∈ S from ⟨hN, hN'⟩))
  · exact absurd (hT.1 (h ▸ Submodule.mem_top : v ∈ T)) hφ

section Tensor

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]

noncomputable def ctrL (φ : V₁ →ₗ[ℂ] ℂ) : TensorProduct ℂ V₁ V₂ →ₗ[ℂ] V₂ :=
  (TensorProduct.lid ℂ V₂).toLinearMap ∘ₗ LinearMap.rTensor V₂ φ

noncomputable def ctrR (ψ : V₂ →ₗ[ℂ] ℂ) : TensorProduct ℂ V₁ V₂ →ₗ[ℂ] V₁ :=
  (TensorProduct.rid ℂ V₁).toLinearMap ∘ₗ LinearMap.lTensor V₁ ψ

@[simp] lemma ctrL_tmul (φ : V₁ →ₗ[ℂ] ℂ) (x : V₁) (y : V₂) :
    ctrL φ (x ⊗ₜ[ℂ] y) = φ x • y := by simp [ctrL]

@[simp] lemma ctrR_tmul (ψ : V₂ →ₗ[ℂ] ℂ) (x : V₁) (y : V₂) :
    ctrR ψ (x ⊗ₜ[ℂ] y) = ψ y • x := by simp [ctrR]

lemma tens_tmul (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ V₁) (a₂ : Mat p q →ₗ[ℂ] Module.End ℂ V₂)
    (Z : Mat p q) (x : V₁) (y : V₂) :
    tensAct a₁ a₂ Z (x ⊗ₜ[ℂ] y) = a₁ Z x ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] a₂ Z y := by
  simp [tensAct]

lemma eq_zero_of_ctrR [FiniteDimensional ℂ V₂] (u : TensorProduct ℂ V₁ V₂)
    (h : ∀ ψ : V₂ →ₗ[ℂ] ℂ, ctrR ψ u = 0) : u = 0 := by
  let b := Module.finBasis ℂ V₂
  have : ∀ w : TensorProduct ℂ V₁ V₂, w = ∑ i, ctrR (b.coord i) w ⊗ₜ[ℂ] b i := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      conv_lhs => rw [← b.sum_repr y]
      rw [TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ctrR_tmul, TensorProduct.smul_tmul]
      rfl
    | add x y hx hy =>
      conv_lhs => rw [hx, hy]
      simp [TensorProduct.add_tmul, Finset.sum_add_distrib]
  rw [this u]
  simp [h]

lemma ctr_swap (φ : V₁ →ₗ[ℂ] ℂ) (ψ : V₂ →ₗ[ℂ] ℂ) (u : TensorProduct ℂ V₁ V₂) :
    φ (ctrR ψ u) = ψ (ctrL φ u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [mul_comm]
  | add x y hx hy => simp [hx, hy]

lemma ctrR_act (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ V₁) (a₂ : Mat p q →ₗ[ℂ] Module.End ℂ V₂)
    (Z : Mat p q) (ψ : V₂ →ₗ[ℂ] ℂ) (u : TensorProduct ℂ V₁ V₂) :
    ctrR ψ (tensAct a₁ a₂ Z u) = a₁ Z (ctrR ψ u) + ctrR (ψ ∘ₗ a₂ Z) u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [tens_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]; abel

lemma ctrL_act (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ V₁) (a₂ : Mat p q →ₗ[ℂ] Module.End ℂ V₂)
    (Z : Mat p q) (φ : V₁ →ₗ[ℂ] ℂ) (s : ℂ) (hφ : ∀ y, φ (a₁ Z y) = s * φ y)
    (u : TensorProduct ℂ V₁ V₂) :
    ctrL φ (tensAct a₁ a₂ Z u) = s • ctrL φ u + a₂ Z (ctrL φ u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [tens_tmul, hφ, mul_smul]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]; abel

noncomputable def ctrMap (u : TensorProduct ℂ V₁ V₂) : (V₂ →ₗ[ℂ] ℂ) →ₗ[ℂ] V₁ where
  toFun ψ := ctrR ψ u
  map_add' ψ χ := by simp [ctrR, LinearMap.lTensor_add]
  map_smul' s ψ := by simp [ctrR, LinearMap.lTensor_smul]

end Tensor

theorem highestWeight_tensor : admQ7 := by
  intro p q V₁ V₂ _ _ _ _ a₁ a₂ hL₁ _ _ _ _ μ ⟨v, hv⟩ hirr ν u ⟨hu0, hu⟩
  obtain ⟨φ, hφ, h1, h2⟩ := exists_dual hL₁ hv hirr
  rw [mem_hw] at hu
  have hx0 : ctrL φ u ≠ 0 := by
    intro hx
    apply hu0
    have hbot := ker_bot hL₁ hirr φ hφ h1 h2 (LinearMap.range (ctrMap u)) ?_ ?_
    · refine eq_zero_of_ctrR u fun ψ => ?_
      have : ctrMap u ψ ∈ LinearMap.range (ctrMap u) := ⟨ψ, rfl⟩
      rw [hbot] at this
      exact this
    · rintro _ ⟨ψ, rfl⟩
      change φ (ctrR ψ u) = 0
      rw [ctr_swap, hx, map_zero]
    · rintro a b hab _ ⟨ψ, rfl⟩
      refine ⟨-(ψ ∘ₗ a₂ (Eab a b)), ?_⟩
      have := ctrR_act a₁ a₂ (Eab a b) ψ u
      rw [hu.2 a b hab, map_zero] at this
      rw [map_neg]
      change -ctrR _ u = a₁ _ (ctrR ψ u)
      exact neg_eq_of_add_eq_zero_left this.symm
  refine ⟨ν - μ, ?_, by abel⟩
  rw [Submodule.ne_bot_iff]
  refine ⟨ctrL φ u, mem_wt.2 fun a => ?_, hx0⟩
  have := ctrL_act a₁ a₂ (Eab a a) φ _ (h1 a) u
  rw [hu.1 a, map_smul] at this
  rw [Pi.sub_apply, Rat.cast_sub, sub_smul, this]
  abel

end GlobalTheory.TensorHW
