import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreDefs

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace TensorProduct

namespace PositivityTheory.KReal

namespace Delta

section Gen

variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]

theorem mulL (x : A) (t : A ⊗[ℂ] B) : (x ⊗ₜ[ℂ] (1 : B)) * t = (LinearMap.mulLeft ℂ x).rTensor B t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => rw [mul_add, map_add, ha, hb]

theorem mulR (y : B) (t : A ⊗[ℂ] B) : ((1 : A) ⊗ₜ[ℂ] y) * t = (LinearMap.mulLeft ℂ y).lTensor A t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => rw [mul_add, map_add, ha, hb]

theorem derL (D : Derivation ℂ A A) (t : A ⊗[ℂ] B) (x : A) (y : B) :
    D.toLinearMap.rTensor B (t * (x ⊗ₜ[ℂ] y)) =
      D.toLinearMap.rTensor B t * (x ⊗ₜ[ℂ] y) + t * (D x ⊗ₜ[ℂ] y) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.rTensor_tmul, Derivation.coeFn_coe,
      Derivation.leibniz, smul_eq_mul, TensorProduct.add_tmul]
    rw [add_comm, mul_comm x]
  | add a b ha hb => rw [add_mul, map_add, ha, hb, map_add, add_mul, add_mul]; abel

theorem derR (D : Derivation ℂ B B) (t : A ⊗[ℂ] B) (x : A) (y : B) :
    D.toLinearMap.lTensor A (t * (x ⊗ₜ[ℂ] y)) =
      D.toLinearMap.lTensor A t * (x ⊗ₜ[ℂ] y) + t * (x ⊗ₜ[ℂ] D y) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.lTensor_tmul, Derivation.coeFn_coe,
      Derivation.leibniz, smul_eq_mul, TensorProduct.tmul_add]
    rw [add_comm, mul_comm y]
  | add a b ha hb => rw [add_mul, map_add, ha, hb, map_add, add_mul, add_mul]; abel

end Gen

variable {p q r s : ℕ}

def dv (p q r s : ℕ) : Ln p q r s → Pol p q r 0 ⊗[ℂ] Pol p q 0 s
  | (a, .inl k) => (X (a, Sum.inl k) : Pol p q r 0) ⊗ₜ[ℂ] (1 : Pol p q 0 s)
  | (a, .inr l) => (1 : Pol p q r 0) ⊗ₜ[ℂ] (X (a, Sum.inr l) : Pol p q 0 s)

def dl (p q r s : ℕ) : Pol p q r s →ₐ[ℂ] Pol p q r 0 ⊗[ℂ] Pol p q 0 s := aeval (dv p q r s)

theorem dl_XL (a : Ix p q) (k : Fin r) :
    dl p q r s (X (a, Sum.inl k)) = (X (a, Sum.inl k) : Pol p q r 0) ⊗ₜ[ℂ] (1 : Pol p q 0 s) := by
  simp [dl, dv]

theorem dl_XR (a : Ix p q) (l : Fin s) :
    dl p q r s (X (a, Sum.inr l)) = (1 : Pol p q r 0) ⊗ₜ[ℂ] (X (a, Sum.inr l) : Pol p q 0 s) := by
  simp [dl, dv]

theorem dl_C (c : ℂ) : dl p q r s (C c) = c • ((1 : Pol p q r 0) ⊗ₜ[ℂ] (1 : Pol p q 0 s)) := by
  rw [dl, aeval_C, Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def]

theorem dl_mulL (a : Ix p q) (k : Fin r) (f : Pol p q r s) :
    dl p q r s (X (a, Sum.inl k) * f) =
      (LinearMap.mulLeft ℂ (X (a, Sum.inl k) : Pol p q r 0)).rTensor _ (dl p q r s f) := by
  rw [map_mul, dl_XL, mulL]

theorem dl_mulR (a : Ix p q) (l : Fin s) (f : Pol p q r s) :
    dl p q r s (X (a, Sum.inr l) * f) =
      (LinearMap.mulLeft ℂ (X (a, Sum.inr l) : Pol p q 0 s)).lTensor _ (dl p q r s f) := by
  rw [map_mul, dl_XR, mulR]

private theorem dl_pderiv_inl_X_eq_rTensor (a : Ix p q) (k : Fin r) (i : Ln p q r s) :
    dl p q r s (pderiv (a, Sum.inl k) (X i)) =
      (pderiv ((a, Sum.inl k) : Ln p q r 0)).toLinearMap.rTensor _ (dl p q r s (X i)) := by
  obtain ⟨b, m | m⟩ := i
  · rw [dl_XL, LinearMap.rTensor_tmul]
    by_cases h : b = a ∧ m = k
    · obtain ⟨rfl, rfl⟩ := h
      simp [Algebra.TensorProduct.one_def]
    · have h1 : ((b, Sum.inl m) : Ln p q r s) ≠ (a, Sum.inl k) := by simpa using h
      have h2 : ((b, Sum.inl m) : Ln p q r 0) ≠ (a, Sum.inl k) := by simpa using h
      simp [pderiv_X, Pi.single_apply, h1, h2]
  · rw [dl_XR, LinearMap.rTensor_tmul]
    simp [pderiv_X, Pi.single_apply]

theorem dl_pdL (a : Ix p q) (k : Fin r) (f : Pol p q r s) :
    dl p q r s (pderiv (a, Sum.inl k) f) =
      (pderiv ((a, Sum.inl k) : Ln p q r 0)).toLinearMap.rTensor _ (dl p q r s f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [dl_C]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf =>
    have h1 : pderiv (a, Sum.inl k) (f * X i) =
        pderiv (a, Sum.inl k) f * X i + f * pderiv (a, Sum.inl k) (X i) := by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      ring
    simp only [h1, map_add, map_mul, hf, dl_pderiv_inl_X_eq_rTensor]
    obtain ⟨b, m | m⟩ := i
    · rw [dl_XL, derL, LinearMap.rTensor_tmul]
      rfl
    · rw [dl_XR, derL, LinearMap.rTensor_tmul]
      rfl

private theorem dl_pderiv_inr_X_eq_lTensor (a : Ix p q) (k : Fin s) (i : Ln p q r s) :
    dl p q r s (pderiv (a, Sum.inr k) (X i)) =
      (pderiv ((a, Sum.inr k) : Ln p q 0 s)).toLinearMap.lTensor _ (dl p q r s (X i)) := by
  obtain ⟨b, m | m⟩ := i
  · rw [dl_XL, LinearMap.lTensor_tmul]
    simp [pderiv_X, Pi.single_apply]
  · rw [dl_XR, LinearMap.lTensor_tmul]
    by_cases h : b = a ∧ m = k
    · obtain ⟨rfl, rfl⟩ := h
      simp [Algebra.TensorProduct.one_def]
    · have h1 : ((b, Sum.inr m) : Ln p q r s) ≠ (a, Sum.inr k) := by simpa using h
      have h2 : ((b, Sum.inr m) : Ln p q 0 s) ≠ (a, Sum.inr k) := by simpa using h
      simp [pderiv_X, Pi.single_apply, h1, h2]

theorem dl_pdR (a : Ix p q) (k : Fin s) (f : Pol p q r s) :
    dl p q r s (pderiv (a, Sum.inr k) f) =
      (pderiv ((a, Sum.inr k) : Ln p q 0 s)).toLinearMap.lTensor _ (dl p q r s f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [dl_C]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf =>
    have h1 : pderiv (a, Sum.inr k) (f * X i) =
        pderiv (a, Sum.inr k) f * X i + f * pderiv (a, Sum.inr k) (X i) := by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      ring
    simp only [h1, map_add, map_mul, hf, dl_pderiv_inr_X_eq_lTensor]
    obtain ⟨b, m | m⟩ := i
    · rw [dl_XL, derR, LinearMap.lTensor_tmul]
      rfl
    · rw [dl_XR, derR, LinearMap.lTensor_tmul]
      rfl

theorem dl_lowL (a : Ix p q) (k : Fin r) (f : Pol p q r s) :
    dl p q r s (lowB (a, Sum.inl k) f) =
      (lowB ((a, Sum.inl k) : Ln p q r 0)).rTensor _ (dl p q r s f) := by
  obtain a | a := a <;> simp [lowB, linePos, dl_pdL, dl_mulL]

theorem dl_lowR (a : Ix p q) (k : Fin s) (f : Pol p q r s) :
    dl p q r s (lowB (a, Sum.inr k) f) =
      (lowB ((a, Sum.inr k) : Ln p q 0 s)).lTensor _ (dl p q r s f) := by
  obtain a | a := a <;> simp [lowB, linePos, dl_pdR, dl_mulR]

theorem dl_raiL (a : Ix p q) (k : Fin r) (f : Pol p q r s) :
    dl p q r s (raiB (a, Sum.inl k) f) =
      (raiB ((a, Sum.inl k) : Ln p q r 0)).rTensor _ (dl p q r s f) := by
  obtain a | a := a <;> simp [raiB, linePos, dl_pdL, dl_mulL, LinearMap.rTensor_neg]

theorem dl_raiR (a : Ix p q) (k : Fin s) (f : Pol p q r s) :
    dl p q r s (raiB (a, Sum.inr k) f) =
      (raiB ((a, Sum.inr k) : Ln p q 0 s)).lTensor _ (dl p q r s f) := by
  obtain a | a := a <;> simp [raiB, linePos, dl_pdR, dl_mulR, LinearMap.lTensor_neg]

theorem dl_omL (a b : Ix p q) (k : Fin r) (f : Pol p q r s) :
    dl p q r s (omE (a, Sum.inl k) (b, Sum.inl k) f) =
      (omE ((a, Sum.inl k) : Ln p q r 0) (b, Sum.inl k)).rTensor _ (dl p q r s f) := by
  simp only [omE, LinearMap.add_apply, Module.End.mul_apply, map_add, dl_raiL, dl_lowL,
    LinearMap.rTensor_add, LinearMap.rTensor_mul]
  by_cases h : a = b
  · subst h
    simp [LinearMap.rTensor_smul, Module.End.one_eq_id, LinearMap.rTensor_id]
  · have h' : ((a, Sum.inl k) : Ln p q r s) ≠ (b, Sum.inl k) := by simp [h]
    have h'' : ((a, Sum.inl k) : Ln p q r 0) ≠ (b, Sum.inl k) := by simp [h]
    simp [h', h'']

theorem dl_omR (a b : Ix p q) (k : Fin s) (f : Pol p q r s) :
    dl p q r s (omE (a, Sum.inr k) (b, Sum.inr k) f) =
      (omE ((a, Sum.inr k) : Ln p q 0 s) (b, Sum.inr k)).lTensor _ (dl p q r s f) := by
  simp only [omE, LinearMap.add_apply, Module.End.mul_apply, map_add, dl_raiR, dl_lowR,
    LinearMap.lTensor_add, LinearMap.lTensor_mul]
  by_cases h : a = b
  · subst h
    simp [LinearMap.lTensor_smul, Module.End.one_eq_id, LinearMap.lTensor_id]
  · have h' : ((a, Sum.inr k) : Ln p q r s) ≠ (b, Sum.inr k) := by simp [h]
    have h'' : ((a, Sum.inr k) : Ln p q 0 s) ≠ (b, Sum.inr k) := by simp [h]
    simp [h', h'']

theorem act_unit (a b : Ix p q) :
    fockAct1 p q r s (Eab a b) = ∑ c : Ix r s, omE ((a, c) : Ln p q r s) (b, c) := by
  simp only [fockAct1, LinearMap.comp_apply, LinearMap.flip_apply, kroneckerMapBilinear_apply_apply, omAct,
    LinearMap.sum_apply, LinearMap.smulRight_apply, entryLinearMap_apply]
  rw [Fintype.sum_prod_type]
  simp only [kroneckerMap_apply, Eab, Matrix.single_apply, Matrix.one_apply, LinearMap.mul_apply']
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.sum_eq_single (b, c)]
    · simp
    · rintro ⟨x2, d⟩ _ hl
      by_cases h1 : b = x2 <;> by_cases h2 : c = d <;> simp_all
    · simp
  · intro x1 _ hx
    simp [Ne.symm hx]
  · simp

section Form

variable (b : Pol p q r 0 →ₗ[ℂ] Pol p q 0 s →ₗ[ℂ] ℂ)

theorem sumL {ι : Type} [Fintype ι] (F : ι → Module.End ℂ (Pol p q r 0)) (t : Pol p q r 0 ⊗[ℂ] Pol p q 0 s) :
    (∑ i, F i).rTensor (Pol p q 0 s) t = ∑ i, (F i).rTensor (Pol p q 0 s) t := by
  classical
  have key : ∀ S : Finset ι, (∑ i ∈ S, F i).rTensor (Pol p q 0 s) t = ∑ i ∈ S, (F i).rTensor (Pol p q 0 s) t := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert j S hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, LinearMap.rTensor_add, LinearMap.add_apply, ih]
  exact key Finset.univ

theorem sumR {ι : Type} [Fintype ι] (F : ι → Module.End ℂ (Pol p q 0 s)) (t : Pol p q r 0 ⊗[ℂ] Pol p q 0 s) :
    (∑ i, F i).lTensor (Pol p q r 0) t = ∑ i, (F i).lTensor (Pol p q r 0) t := by
  classical
  have key : ∀ S : Finset ι, (∑ i ∈ S, F i).lTensor (Pol p q r 0) t = ∑ i ∈ S, (F i).lTensor (Pol p q r 0) t := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert j S hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, LinearMap.lTensor_add, LinearMap.add_apply, ih]
  exact key Finset.univ

end Form

theorem dl_unit (a b : Ix p q) (f : Pol p q r s) :
    dl p q r s (fockAct1 p q r s (Eab a b) f) =
      (fockAct1 p q r 0 (Eab a b)).rTensor _ (dl p q r s f) +
      (fockAct1 p q 0 s (Eab a b)).lTensor _ (dl p q r s f) := by
  rw [act_unit, act_unit, act_unit, sumL, sumR]
  simp only [Fintype.sum_sum_type, LinearMap.add_apply, map_add, LinearMap.sum_apply, map_sum, dl_omL, dl_omR,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add, Fin.sum_univ_zero]

theorem eq_sum_units (Z : Mat p q) : Z = ∑ a, ∑ b, Z a b • Eab a b := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ext i j
  simp [Eab, Matrix.single_apply]

theorem dl_act (Z : Mat p q) (f : Pol p q r s) :
    dl p q r s (fockAct1 p q r s Z f) =
      (fockAct1 p q r 0 Z).rTensor _ (dl p q r s f) + (fockAct1 p q 0 s Z).lTensor _ (dl p q r s f) := by
  rw [eq_sum_units Z]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, sumL, sumR, dl_unit,
    LinearMap.rTensor_smul, LinearMap.lTensor_smul, smul_add, Finset.sum_add_distrib]

def iA (p q r s : ℕ) : Ln p q r 0 → Ln p q r s := fun l => (l.1, Sum.elim Sum.inl Fin.elim0 l.2)

def iB (p q r s : ℕ) : Ln p q 0 s → Ln p q r s := fun l => (l.1, Sum.elim Fin.elim0 Sum.inr l.2)

theorem dl_iA (u : Pol p q r 0) : dl p q r s (rename (iA p q r s) u) = u ⊗ₜ[ℂ] (1 : Pol p q 0 s) := by
  have h : (dl p q r s).comp (rename (iA p q r s)) =
      (Algebra.TensorProduct.includeLeft (R := ℂ) (S := ℂ) (A := Pol p q r 0) (B := Pol p q 0 s)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, k | k⟩
    · simp [iA, dl_XL]
    · exact k.elim0
  simpa using DFunLike.congr_fun h u

theorem dl_iB (v : Pol p q 0 s) : dl p q r s (rename (iB p q r s) v) = (1 : Pol p q r 0) ⊗ₜ[ℂ] v := by
  have h : (dl p q r s).comp (rename (iB p q r s)) =
      (Algebra.TensorProduct.includeRight (R := ℂ) (A := Pol p q r 0) (B := Pol p q 0 s)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, k | k⟩
    · exact k.elim0
    · simp [iB, dl_XR]
  simpa using DFunLike.congr_fun h v

end Delta

open Delta in
theorem nontrivial_of_form {p q r s : ℕ} (c : ℂ) (b : Pol p q r 0 →ₗ[ℂ] Pol p q 0 s →ₗ[ℂ] ℂ)
    (hb : ∀ Z u v, b (fockAct1 p q r 0 Z u) v + b u (fockAct1 p q 0 s Z v) = c * Z.trace * b u v)
    (u0 : Pol p q r 0) (v0 : Pol p q 0 s) (hne : b u0 v0 ≠ 0) : Nontrivial (ThC p q r s c) := by
  classical
  set B' : Pol p q r 0 ⊗[ℂ] Pol p q 0 s →ₗ[ℂ] ℂ := TensorProduct.lift b with hB'
  have key : ∀ (Z : Mat p q) (t : Pol p q r 0 ⊗[ℂ] Pol p q 0 s),
      B' ((fockAct1 p q r 0 Z).rTensor _ t) + B' ((fockAct1 p q 0 s Z).lTensor _ t) = c * Z.trace * B' t := by
    intro Z t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul u v => simpa [hB'] using hb Z u v
    | add x y hx hy =>
      simp only [map_add]
      linear_combination hx + hy
  have hle : coinvSub (act1 p q r s) (chiTr c) ≤ LinearMap.ker (B' ∘ₗ (dl p q r s).toLinearMap) := by
    refine iSup_le fun Z => ?_
    intro x hx
    obtain ⟨f, rfl⟩ := LinearMap.mem_range.mp hx
    rw [LinearMap.mem_ker]
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      map_sub, map_smul, AlgHom.toLinearMap_apply, act1, chiTr, dl_act, map_add, key, smul_eq_mul]
    ring
  refine ⟨⟨Submodule.Quotient.mk (p := coinvSub (act1 p q r s) (chiTr c))
    (rename (iA p q r s) u0 * rename (iB p q r s) v0), 0, ?_⟩⟩
  intro h
  rw [Submodule.Quotient.mk_eq_zero] at h
  have h2 := hle h
  rw [LinearMap.mem_ker, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, dl_iA, dl_iB,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, hB', TensorProduct.lift.tmul] at h2
  exact hne h2

end PositivityTheory.KReal

end
