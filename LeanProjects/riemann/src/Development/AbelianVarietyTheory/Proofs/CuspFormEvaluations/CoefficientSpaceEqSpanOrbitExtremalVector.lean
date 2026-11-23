import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
import Formalism.LocalToGlobal.Columns.PolyFnLemmas

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrbitSpan

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.GradedWeylDivisibility
open scoped Classical Pointwise Matrix

theorem coeff_mem_of_eval_mem {K A : Type} [Field K] [CharZero K] [CommRing A] [Algebra K A] (M : Submodule K A)
    (p : Polynomial A) (h : ∀ c : ℕ, p.eval (c : A) ∈ M) (k : ℕ) : p.coeff k ∈ M := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ
  set q : Polynomial K := ∑ i ∈ Finset.range (p.natDegree + 1), Polynomial.monomial i (φ (p.coeff i)) with hq
  have hq0 : q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (s := Set.range (fun c : ℕ => (c : K))) ?_
      (Set.infinite_range_of_injective Nat.cast_injective)
    rintro _ ⟨c, rfl⟩
    have h1 := hφ _ (h c)
    rw [Polynomial.eval_eq_sum_range, map_sum] at h1
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, hq, Polynomial.eval_finset_sum, Polynomial.eval_monomial]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : p.coeff i * (c : A) ^ i = ((c : K) ^ i) • p.coeff i := by
      rw [Algebra.smul_def, map_pow, map_natCast, mul_comm]
    rw [this, map_smul, smul_eq_mul, mul_comm]
  by_cases hk : k ≤ p.natDegree
  · have := congrArg (fun r => r.coeff k) hq0
    simp only [hq, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range,
      Polynomial.coeff_zero] at this
    rwa [if_pos (by omega)] at this
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]

theorem eval_rowGen {K : Type} [Field K] {r n : ℕ} (a b : Fin r) (c : K) (f : MvPolynomial (Fin r × Fin n) K) :
    (rowGen K a b f).eval (C c) = rowAct K (1 + Matrix.single b a c) f := by
  induction f using MvPolynomial.induction_on with
  | C x => simp [rowGen, rowAct]
  | add f g hf hg => simp only [map_add, Polynomial.eval_add, hf, hg]
  | mul_X f v hf =>
    simp only [map_mul, Polynomial.eval_mul, hf]
    congr 1
    simp only [rowGen, rowAct, aeval_X, Matrix.add_apply, map_add, add_mul, Finset.sum_add_distrib,
      Polynomial.eval_add, Polynomial.eval_C]
    congr 1
    · rw [Finset.sum_eq_single v.1]
      · simp
      · intro x _ hx
        simp [Matrix.one_apply, Ne.symm hx]
      · simp
    · rw [Finset.sum_eq_single a]
      · by_cases hv : v.1 = b
        · simp only [hv, if_true, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C,
            Matrix.single_apply_same]
        · simp [hv, Matrix.single, Ne.symm hv]
      · intro x _ hx
        simp [Matrix.single, Ne.symm hx]
      · simp

theorem isUnit_elem {K : Type} [Field K] [CharZero K] {r : ℕ} (a b : Fin r) (c : ℕ) :
    IsUnit (1 + Matrix.single b a (c : K)) := by
  by_cases h : a = b
  · subst h
    have hc : (1 + c : K) ≠ 0 := by exact_mod_cast (by omega : 1 + c ≠ 0)
    refine IsUnit.of_mul_eq_one (1 + Matrix.single a a (-(c : K) / (1 + c))) ?_
    rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, Matrix.single_mul_single_same, add_assoc,
      ← Matrix.single_add, ← Matrix.single_add]
    have : -(c : K) / (1 + c) + (c + c * (-(c : K) / (1 + c))) = 0 := by field_simp; ring
    rw [this]; simp
  · refine IsUnit.of_mul_eq_one (1 + Matrix.single b a (-(c : K))) ?_
    rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, Matrix.single_mul_single_of_ne _ _ _ _ h, add_zero,
      add_assoc, ← Matrix.single_add]
    simp

def trGL {K : Type} [Field K] {r : ℕ} (g : GL (Fin r) K) : GL (Fin r) K := inside₂ K r g⁻¹

theorem trGL_coe {K : Type} [Field K] {r : ℕ} (g : GL (Fin r) K) :
    (trGL g : Matrix (Fin r) (Fin r) K) = (g : Matrix (Fin r) (Fin r) K)ᵀ := by
  simp [trGL, inside₂]

theorem rowDiv_mem_of_stable {K : Type} [Field K] [CharZero K] {r m : ℕ}
    (M : Submodule K (MvPolynomial (Fin r × Fin m) K))
    (hst : ∀ u : GL (Fin r) K, ∀ f ∈ M, rowAct K (u : Matrix (Fin r) (Fin r) K) f ∈ M)
    (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin m) K) (hf : f ∈ M) : rowDiv K a b k f ∈ M := by
  unfold rowDiv
  refine coeff_mem_of_eval_mem M _ (fun c => ?_) k
  have h1 := eval_rowGen a b (c : K) f
  rw [map_natCast] at h1
  rw [h1]
  obtain ⟨u, hu⟩ := isUnit_elem (K := K) a b c
  rw [← hu]
  exact hst u f hf

theorem applyWord_mem_of_stable {K : Type} [Field K] [CharZero K] {r m : ℕ}
    (M : Submodule K (MvPolynomial (Fin r × Fin m) K))
    (hst : ∀ u : GL (Fin r) K, ∀ f ∈ M, rowAct K (u : Matrix (Fin r) (Fin r) K) f ∈ M)
    (f : MvPolynomial (Fin r × Fin m) K) (hf : f ∈ M) (w : List (Fin r × Fin r × ℕ)) : applyWord K w f ∈ M := by
  unfold applyWord
  induction w with
  | nil => rw [List.foldr_nil]; exact hf
  | cons x w ih => rw [List.foldr_cons]; exact rowDiv_mem_of_stable M hst _ _ _ _ ih

theorem rowAct_one {K : Type} [Field K] {r m : ℕ} :
    rowAct K (n := m) (1 : Matrix (Fin r) (Fin r) K) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [rowAct, aeval_X, Matrix.one_apply, AlgHom.id_apply]
  rw [Finset.sum_eq_single v.1]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem orbit_stable {K : Type} [Field K] {r m : ℕ} (v : MvPolynomial (Fin r × Fin m) K) (u : GL (Fin r) K)
    (f : MvPolynomial (Fin r × Fin m) K)
    (hf : f ∈ Submodule.span K (Set.range fun g : GL (Fin r) K => rowAct K (g : Matrix (Fin r) (Fin r) K)ᵀ v)) :
    rowAct K (u : Matrix (Fin r) (Fin r) K) f ∈
      Submodule.span K (Set.range fun g : GL (Fin r) K => rowAct K (g : Matrix (Fin r) (Fin r) K)ᵀ v) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    refine Submodule.subset_span ⟨trGL u * g, ?_⟩
    have := DFunLike.congr_fun
      (rowActMul K r m (u : Matrix (Fin r) (Fin r) K) (g : Matrix (Fin r) (Fin r) K)ᵀ) v
    rw [AlgHom.comp_apply] at this
    beta_reduce
    rw [this, Units.val_mul, trGL_coe, Matrix.transpose_mul, Matrix.transpose_transpose]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem dualWeyl_le_span_orbit (K : Type) [Field K] [CharZero K] {r m : ℕ} (hm : m ≤ r) (ν : Fin m → ℕ)
    (hν : Antitone ν) :
    dualWeyl K r m ν ≤ Submodule.span K (Set.range fun g : GL (Fin r) K =>
      rowAct K (g : Matrix (Fin r) (Fin r) K)ᵀ (hw K hm ν)) := by
  rw [Formalism.L2.Col.dualWeyl_eq_weyl K hm ν hν, weyl, Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  generalize hw K hm ν = v
  refine applyWord_mem_of_stable _ (orbit_stable v) v (Submodule.subset_span ⟨1, ?_⟩) w
  beta_reduce
  rw [Units.val_one, Matrix.transpose_one, rowAct_one, AlgHom.id_apply]

theorem prod_mem_span_prod {K A ι : Type} [Field K] [CommRing A] [Algebra K A] (s : Finset ι) (S : ι → Set A)
    (x : ι → A) (hx : ∀ i, x i ∈ Submodule.span K (S i)) : ∏ i ∈ s, x i ∈ Submodule.span K (∏ i ∈ s, S i) := by
  induction s using Finset.induction_on with
  | empty => exact Submodule.subset_span (by simp)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ← Submodule.span_mul_span]
    exact Submodule.mul_mem_mul (hx a) ih

theorem trAct_ten {K : Type} [Field K] {Ix : Type} [Fintype Ix] {n : ℕ} (g : Ix → GL (Fin n) K)
    (f : Ix → MvPolynomial (Fin n × Fin n) K) :
    trAct g (ten f) = ten fun t => rowAct K (g t : Matrix (Fin n) (Fin n) K)ᵀ (f t) := by
  unfold trAct ten
  rw [map_prod]
  exact Finset.prod_congr rfl fun t _ =>
    (blockActTensor K K Ix n n (fun τ => (g τ : Matrix (Fin n) (Fin n) K)ᵀ)).1 t (f t)

theorem VV_eq_span_orbit (K : Type) [Field K] [CharZero K] (Ix : Type) [Fintype Ix] (n : ℕ)
    (lam : Ix → DomWeight n) :
    VV K lam = Submodule.span K
      (Set.range fun g : Ix → GL (Fin n) K => actP lam g (ten fun t => extremal K n (lam t))) := by
  apply le_antisymm
  · rw [VV, tensorLat, Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    have h1 := prod_mem_span_prod (K := K) Finset.univ
      (fun t => blockEmb K t '' (Set.range fun g : GL (Fin n) K =>
        rowAct K (g : Matrix (Fin n) (Fin n) K)ᵀ (extremal K n (lam t))))
      (fun t => blockEmb K t (F t)) (fun t => by
        have := dualWeyl_le_span_orbit K le_rfl (lam t).natW (Formalism.L2.Col.natW_anti (lam t)) (hF t)
        exact Submodule.apply_mem_span_image_of_mem_span (blockEmb K t).toLinearMap this)
    refine Submodule.span_le.mpr ?_ h1
    intro y hy
    rw [Set.mem_fintype_prod] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    choose w hw hw' using hz
    choose g hg using hw
    have hd : detTwK lam g ≠ 0 := Finset.prod_ne_zero_iff.mpr fun t _ => Units.ne_zero _
    have h2 : ∏ t, z t = (detTwK lam g)⁻¹ • actP lam g (ten fun t => extremal K n (lam t)) := by
      simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_smul, inv_mul_cancel₀ hd, one_smul,
        trAct_ten]
      unfold ten
      exact Finset.prod_congr rfl fun t _ => by rw [← hw', ← hg]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    refine polyAction_mem_VV lam g (Submodule.subset_span ⟨_, fun t => ?_, rfl⟩)
    exact Formalism.GradedWeylDivisibility.weylLeDual K n n le_rfl _ (Formalism.L2.Col.natW_anti (lam t)) (Submodule.subset_span ⟨[], rfl⟩)

end GlobalTheory.OrbitSpan
