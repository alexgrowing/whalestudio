import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDetChangeOfBasesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4.Kap

section Lin

variable {K : Type} [Field K] {n : ℕ}

theorem conj_pow (P : GL (Fin n) K) (D : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    ((P : Matrix (Fin n) (Fin n) K) * D * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ^ k =
      (P : Matrix (Fin n) (Fin n) K) * D ^ k * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have hPP : ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (P : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    calc (P : Matrix (Fin n) (Fin n) K) * D ^ k * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((P : Matrix (Fin n) (Fin n) K) * D * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        = (P : Matrix (Fin n) (Fin n) K) * D ^ k *
            (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (P : Matrix (Fin n) (Fin n) K)) * D *
            ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPP, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem aeval_conj (P : GL (Fin n) K) (D : Matrix (Fin n) (Fin n) K) (Q : K[X]) :
    aeval ((P : Matrix (Fin n) (Fin n) K) * D * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) Q =
      (P : Matrix (Fin n) (Fin n) K) * aeval D Q * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, Matrix.mul_add, Matrix.add_mul]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, conj_pow]
    have hc : algebraMap K (Matrix (Fin n) (Fin n) K) a * (P : Matrix (Fin n) (Fin n) K) =
        (P : Matrix (Fin n) (Fin n) K) * algebraMap K (Matrix (Fin n) (Fin n) K) a := Algebra.commutes a _
    calc algebraMap K (Matrix (Fin n) (Fin n) K) a *
          ((P : Matrix (Fin n) (Fin n) K) * D ^ k * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        = (algebraMap K (Matrix (Fin n) (Fin n) K) a * (P : Matrix (Fin n) (Fin n) K)) * D ^ k *
            ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by simp only [Matrix.mul_assoc]
      _ = (P : Matrix (Fin n) (Fin n) K) * (algebraMap K (Matrix (Fin n) (Fin n) K) a * D ^ k) *
            ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [hc]; simp only [Matrix.mul_assoc]

theorem aeval_diagonal' (u : Fin n → K) (Q : K[X]) :
    aeval (Matrix.diagonal u) Q = Matrix.diagonal fun i => Q.eval (u i) := by
  have h := Polynomial.aeval_algHom_apply (Matrix.diagonalAlgHom K : (Fin n → K) →ₐ[K] Matrix (Fin n) (Fin n) K) u Q
  rw [Matrix.diagonalAlgHom_apply] at h
  rw [h, Matrix.diagonalAlgHom_apply, aeval_pi_apply]
  congr 1

theorem mulVec_inv_mulVec (P : GL (Fin n) K) (x : Fin n → K) :
    (P : Matrix (Fin n) (Fin n) K) *ᵥ (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem inv_mulVec_mulVec (P : GL (Fin n) K) (x : Fin n → K) :
    ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ ((P : Matrix (Fin n) (Fin n) K) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem mem_ker_conj_diagonal (P : GL (Fin n) K) (d : Fin n → K) (x : Fin n → K) :
    x ∈ LinearMap.ker (Matrix.toLin' ((P : Matrix (Fin n) (Fin n) K) * Matrix.diagonal d *
        ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) ↔
      ∀ i, d i * ((((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ x) i = 0 := by
  rw [LinearMap.mem_ker, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  constructor
  · intro h i
    have h2 := congrArg (fun z => ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ z) h
    simp only [inv_mulVec_mulVec, Matrix.mulVec_zero] at h2
    have h3 := congrFun h2 i
    simpa [Matrix.mulVec_diagonal] using h3
  · intro h
    have : Matrix.diagonal d *ᵥ (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) = 0 := by
      funext i
      rw [Matrix.mulVec_diagonal]
      exact h i
    rw [this, Matrix.mulVec_zero]

theorem ker_conj_diagonal_eq_span (P : GL (Fin n) K) (d : Fin n → K) (S : Finset (Fin n))
    (hd : ∀ i, d i = 0 ↔ i ∈ S) :
    LinearMap.ker (Matrix.toLin' ((P : Matrix (Fin n) (Fin n) K) * Matrix.diagonal d *
        ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) =
      Submodule.span K (Set.range fun i : S => fun k => (P : Matrix (Fin n) (Fin n) K) k i.1) := by
  apply le_antisymm
  · intro x hx
    rw [mem_ker_conj_diagonal] at hx
    have hy0 : ∀ j, j ∉ S → ((((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ x) j = 0 := by
      intro j hj
      rcases mul_eq_zero.1 (hx j) with h | h
      · exact absurd ((hd j).1 h) hj
      · exact h
    have hx' : x = ∑ j ∈ S, ((((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ x) j •
        (fun k => (P : Matrix (Fin n) (Fin n) K) k j) := by
      conv_lhs => rw [← mulVec_inv_mulVec P x]
      funext k
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Matrix.mulVec, dotProduct]
      rw [← Finset.sum_subset (Finset.subset_univ S)]
      · exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      · intro j _ hj
        rw [hy0 j hj, mul_zero]
    rw [hx']
    exact Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, mem_ker_conj_diagonal]
    intro j
    have e : (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ fun k => (P : Matrix (Fin n) (Fin n) K) k i.1) j =
        (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (P : Matrix (Fin n) (Fin n) K)) j i.1 := by
      rw [Matrix.mul_apply]; rfl
    rw [e, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply]
    by_cases hj : j = i.1
    · subst hj
      rw [(hd _).2 i.2, zero_mul]
    · rw [if_neg hj, mul_zero]

theorem exists_eigvec (γ : Matrix (Fin n) (Fin n) K) (t : K) (ht : γ.charpoly.eval t = 0) :
    ∃ x : Fin n → K, x ≠ 0 ∧ γ *ᵥ x = t • x := by
  rw [Matrix.eval_charpoly] at ht
  obtain ⟨x, hx, hx0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 ht
  refine ⟨x, hx, ?_⟩
  rw [Matrix.sub_mulVec, sub_eq_zero] at hx0
  rw [← hx0]
  funext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem exists_diagonalize (γ : Matrix (Fin n) (Fin n) K) (u : Fin n → K) (hu : Function.Injective u)
    (hr : ∀ i, γ.charpoly.eval (u i) = 0) :
    ∃ P : GL (Fin n) K, γ * (P : Matrix (Fin n) (Fin n) K) = (P : Matrix (Fin n) (Fin n) K) * Matrix.diagonal u := by
  choose x hx0 hx using fun i => exists_eigvec γ (u i) (hr i)
  have hli : LinearIndependent K x := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' γ) u hu x fun i => ?_
    refine Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 ?_, hx0 i⟩
    rw [Matrix.toLin'_apply]
    exact hx i
  let M : Matrix (Fin n) (Fin n) K := Matrix.of fun k i => x i k
  have hcol : M.col = x := by funext j k; rfl
  have hM : IsUnit M := Matrix.linearIndependent_cols_iff_isUnit.1 (by rw [hcol]; exact hli)
  refine ⟨hM.unit, ?_⟩
  rw [IsUnit.unit_spec]
  ext k i
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  have h1 := congrFun (hx i) k
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
  simp only [M, Matrix.of_apply]
  rw [h1, mul_comm]

def revOn (S : Finset (Fin n)) (hS : ∀ i ∈ S, Fin.rev i ∈ S) : Equiv.Perm S where
  toFun i := ⟨Fin.rev i.1, hS _ i.2⟩
  invFun i := ⟨Fin.rev i.1, hS _ i.2⟩
  left_inv i := Subtype.ext (Fin.rev_rev _)
  right_inv i := Subtype.ext (Fin.rev_rev _)

theorem det_submatrix_rev (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, j ≠ Fin.rev i → A i j = 0)
    (S : Finset (Fin n)) (hS : ∀ i ∈ S, Fin.rev i ∈ S) :
    (A.submatrix (fun i : S => i.1) (fun i : S => i.1)).det =
      ((Equiv.Perm.sign (revOn S hS) : ℤ) : K) * ∏ j : S, A (Fin.rev j.1) j.1 := by
  have e : A.submatrix (fun i : S => i.1) (fun i : S => i.1) =
      (revOn S hS).permMatrix K * Matrix.diagonal fun j : S => A (Fin.rev j.1) j.1 := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.mul_diagonal, Matrix.submatrix_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
    by_cases h : (revOn S hS) i = j
    · rw [if_pos h, one_mul]
      subst h
      simp [revOn, Fin.rev_rev]
    · rw [if_neg h, zero_mul]
      apply hA
      intro hj
      apply h
      exact Subtype.ext (by rw [hj]; rfl)
  rw [e, Matrix.det_mul, Matrix.det_permutation, Matrix.det_diagonal]

theorem det_rev (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, j ≠ Fin.rev i → A i j = 0) :
    A.det = ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : K) * ∏ j, A (Fin.rev j) j := by
  have e : A = (Fin.revPerm : Equiv.Perm (Fin n)).permMatrix K * Matrix.diagonal fun j => A (Fin.rev j) j := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.mul_diagonal, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Fin.revPerm_apply]
    by_cases h : Fin.rev i = j
    · rw [if_pos h, one_mul]
      subst h
      rw [Fin.rev_rev]
    · rw [if_neg h, zero_mul]
      exact hA i j (fun hj => h hj.symm)
  conv_lhs => rw [e]
  rw [Matrix.det_mul, Matrix.det_permutation, Matrix.det_diagonal]

theorem sum_rev_parity (f : Fin n → ℤ) (hf : ∀ j, f (Fin.rev j) = f j) (S : Finset (Fin n))
    (hS : ∀ i ∈ S, Fin.rev i ∈ S) :
    (((∑ j ∈ S, f j : ℤ)) : ZMod 2) = (((∑ j ∈ S.filter (fun j => Fin.rev j = j), f j : ℤ)) : ZMod 2) := by
  rw [← Finset.sum_filter_add_sum_filter_not S (fun j => Fin.rev j = j), Int.cast_add]
  have h0 : (((∑ j ∈ S.filter (fun j => ¬ Fin.rev j = j), f j : ℤ)) : ZMod 2) = 0 := by
    rw [Int.cast_sum]
    refine Finset.sum_involution (fun j _ => Fin.rev j) ?_ ?_ ?_ ?_
    · intro j _
      rw [hf]
      exact CharTwo.add_self_eq_zero _
    · intro j hj _
      exact (Finset.mem_filter.1 hj).2
    · intro j hj
      rw [Finset.mem_filter] at hj ⊢
      exact ⟨hS _ hj.1, by rw [Fin.rev_rev]; exact fun h => hj.2 h.symm⟩
    · intro j _
      exact Fin.rev_rev j
  rw [h0, add_zero]

theorem rev_fixed_unique {i j : Fin n} (hi : Fin.rev i = i) (hj : Fin.rev j = j) : i = j := by
  have a := congrArg Fin.val hi
  have b := congrArg Fin.val hj
  rw [Fin.val_rev] at a b
  exact Fin.ext (by omega)

end Lin

section Ord

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ordL_eq_of_v {x y : L} (h : Valued.v x = Valued.v y) : ordL x = ordL y := by
  unfold ordL
  by_cases hx : Valued.v x = 0
  · have hy : Valued.v y = 0 := by rw [← h]; exact hx
    rw [dif_pos hx, dif_pos hy]
  · have hy : Valued.v y ≠ 0 := by rw [← h]; exact hx
    rw [dif_neg hx, dif_neg hy]
    have e : WithZero.unzero hx = WithZero.unzero hy := by
      apply WithZero.coe_injective
      rw [WithZero.coe_unzero, WithZero.coe_unzero, h]
    rw [e]

theorem ordL_mul' {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) : ordL (x * y) = ordL x + ordL y := by
  have h0 : Valued.v x ≠ 0 := by simpa using hx
  have h0' : Valued.v y ≠ 0 := by simpa using hy
  have h1 : Valued.v (x * y) ≠ 0 := by rw [map_mul]; exact mul_ne_zero h0 h0'
  unfold ordL
  rw [dif_neg h1, dif_neg h0, dif_neg h0']
  have e : WithZero.unzero h1 = WithZero.unzero h0 * WithZero.unzero h0' := by
    apply WithZero.coe_injective
    rw [WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, WithZero.coe_unzero, map_mul]
  rw [e, toAdd_mul]
  ring

theorem ordL_one' : ordL (1 : L) = 0 := by
  have h := ordL_mul' (one_ne_zero : (1 : L) ≠ 0) (one_ne_zero : (1 : L) ≠ 0)
  rw [one_mul] at h
  omega

theorem ordL_zero' : ordL (0 : L) = 0 := by
  unfold ordL
  simp

theorem ordL_prod' {ι : Type} (T : Finset ι) (g : ι → L) (hg : ∀ j ∈ T, g j ≠ 0) :
    ordL (∏ j ∈ T, g j) = ∑ j ∈ T, ordL (g j) := by
  induction T using Finset.induction_on with
  | empty => simp [ordL_one']
  | @insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ordL_mul' (hg a (Finset.mem_insert_self a T))
        (Finset.prod_ne_zero_iff.2 fun j hj => hg j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hg j (Finset.mem_insert_of_mem hj)]

theorem ordL_sign_mul (s : ℤˣ) (x : L) : ordL (((s : ℤ) : L) * x) = ordL x := by
  rcases Int.units_eq_one_or s with h | h <;> subst h
  · simp
  · apply ordL_eq_of_v
    simp

end Ord

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

set_option maxHeartbeats 1000000 in

theorem kapSign_eq_one_of_vals (hU : Unr E) (w : Pl E) (n : ℕ) (γ : GLw n w) (hγ : γ ∈ UL n w)
    (v : Fin n → ℤ) (hv : Function.Injective v) (hrev : ∀ i j, v j = -v i → j = Fin.rev i)
    (hV : HasVals γ.val.charpoly v) (Q : (w.adicCompletion E)[X]) : kapSign n w Q γ = 1 := by
  obtain ⟨-, hinv, hcj, -⟩ := GlobalTheory.T.placeConjugation_properties_cmField E hU w
  unfold kapSign
  split_ifs with hs
  · rfl
  simp only []
  have hUn : ((γ.val.map (cj w))ᵀ) * γ.val = 1 := by
    have h := hγ
    unfold UL at h
    rw [if_neg hs] at h
    have h2 : cT (cj w) (γ : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * 1 *
        (γ : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = 1 := h
    rw [Matrix.mul_one] at h2
    exact h2
  obtain ⟨u, hu_prod, hu⟩ := hV
  have huinj : Function.Injective u := fun i j h => hv (by rw [← (hu i).2, ← (hu j).2, h])
  have hroot : ∀ i, γ.val.charpoly.eval (u i) = 0 := by
    intro i
    rw [hu_prod, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  obtain ⟨P, hP⟩ := exists_diagonalize γ.val u huinj hroot
  have hγP : γ.val = (P : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * Matrix.diagonal u *
      ((P⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    calc γ.val = γ.val * (P : Matrix (Fin n) (Fin n) (w.adicCompletion E)) *
          ((P⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
            rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = _ := by rw [hP]

  set H : Matrix (Fin n) (Fin n) (w.adicCompletion E) :=
    ((P : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map (cj w))ᵀ * (P : Matrix (Fin n) (Fin n) (w.adicCompletion E))
    with hHdef
  have hPdet : (P : Matrix (Fin n) (Fin n) (w.adicCompletion E)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 P.isUnit).ne_zero
  have hHdet : H.det = cj w (P : Matrix (Fin n) (Fin n) (w.adicCompletion E)).det *
      (P : Matrix (Fin n) (Fin n) (w.adicCompletion E)).det := by
    rw [hHdef, Matrix.det_mul, Matrix.det_transpose,
      show ((P : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map (cj w)).det =
        cj w (P : Matrix (Fin n) (Fin n) (w.adicCompletion E)).det by rw [RingHom.map_det]; rfl]
  have hH0 : H.det ≠ 0 := by
    rw [hHdet]
    exact mul_ne_zero ((map_ne_zero (cj w)).2 hPdet) hPdet
  have hherm : ∀ i j, cj w (H j i) = H i j := by
    intro i j
    simp only [hHdef, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hinv]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hun : ∀ i j, cj w (u i) * H i j * u j = H i j := by
    have e1 : (((γ.val * (P : Matrix (Fin n) (Fin n) (w.adicCompletion E))).map (cj w))ᵀ *
        (γ.val * (P : Matrix (Fin n) (Fin n) (w.adicCompletion E)))) = H := by
      rw [Matrix.map_mul, Matrix.transpose_mul]
      calc ((P : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map (cj w))ᵀ * (γ.val.map (cj w))ᵀ *
            (γ.val * (P : Matrix (Fin n) (Fin n) (w.adicCompletion E)))
          = ((P : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map (cj w))ᵀ *
            (((γ.val.map (cj w))ᵀ * γ.val) * (P : Matrix (Fin n) (Fin n) (w.adicCompletion E))) := by
              simp only [Matrix.mul_assoc]
        _ = H := by rw [hUn, Matrix.one_mul]
    have e2 : (((γ.val * (P : Matrix (Fin n) (Fin n) (w.adicCompletion E))).map (cj w))ᵀ *
        (γ.val * (P : Matrix (Fin n) (Fin n) (w.adicCompletion E)))) =
        Matrix.diagonal (fun i => cj w (u i)) * H * Matrix.diagonal u := by
      rw [hP, Matrix.map_mul, Matrix.transpose_mul, Matrix.diagonal_map (map_zero (cj w)),
        Matrix.diagonal_transpose, hHdef]
      simp only [Matrix.mul_assoc]
    intro i j
    have := congrFun (congrFun (e2.symm.trans e1) i) j
    rwa [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
  have hsupp : ∀ i j, j ≠ Fin.rev i → H i j = 0 := by
    intro i j hj
    by_contra hne
    have h1 : cj w (u i) * u j = 1 := by
      have h2 : (cj w (u i) * u j) * H i j = 1 * H i j := by
        rw [one_mul]
        calc (cj w (u i) * u j) * H i j = cj w (u i) * H i j * u j := by ring
          _ = H i j := hun i j
      exact mul_right_cancel₀ hne h2
    apply hj
    apply hrev
    have h2 := ordL_mul' ((map_ne_zero (cj w)).2 (hu i).1) (hu j).1
    rw [h1, ordL_one', ordL_eq_of_v (hcj (u i)), (hu i).2, (hu j).2] at h2
    omega

  have hg0 : ∀ j, H (Fin.rev j) j ≠ 0 := by
    intro j h
    apply hH0
    refine Matrix.det_eq_zero_of_row_eq_zero (Fin.rev j) fun j' => ?_
    by_cases hj' : j' = j
    · rw [hj']; exact h
    · exact hsupp _ _ (by rw [Fin.rev_rev]; exact hj')
  set f : Fin n → ℤ := fun j => ordL (H (Fin.rev j) j) with hfdef
  have hf : ∀ j, f (Fin.rev j) = f j := by
    intro j
    simp only [hfdef, Fin.rev_rev]
    rw [← hherm]
    exact ordL_eq_of_v (hcj _)
  have hordS : ∀ (S : Finset (Fin n)) (hS : ∀ i ∈ S, Fin.rev i ∈ S),
      ordL (H.submatrix (fun i : S => i.1) (fun i : S => i.1)).det = ∑ j ∈ S, f j := by
    intro S hS
    rw [det_submatrix_rev H hsupp S hS, ordL_sign_mul,
      ordL_prod' _ _ (fun j _ => hg0 j.1)]
    exact Finset.sum_coe_sort S (fun j => f j)
  have htot : Even (∑ j ∈ (Finset.univ : Finset (Fin n)), f j) := by
    have e : ordL H.det = ∑ j, f j := by
      rw [det_rev H hsupp, ordL_sign_mul, ordL_prod' _ _ (fun j _ => hg0 j)]
    rw [hHdet, ordL_mul' ((map_ne_zero (cj w)).2 hPdet) hPdet, ordL_eq_of_v (hcj _)] at e
    exact ⟨ordL (P : Matrix (Fin n) (Fin n) (w.adicCompletion E)).det, by rw [← e]⟩
  have hevenS : ∀ (S : Finset (Fin n)) (hS : ∀ i ∈ S, Fin.rev i ∈ S), Even (∑ j ∈ S, f j) := by
    intro S hS
    rw [← ZMod.intCast_eq_zero_iff_even, sum_rev_parity f hf S hS]
    by_cases hm : ∃ m ∈ S, Fin.rev m = m
    · obtain ⟨m, hmS, hm⟩ := hm
      have e : S.filter (fun j => Fin.rev j = j) = (Finset.univ : Finset (Fin n)).filter (fun j => Fin.rev j = j) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact fun h => h.2
        · intro h
          exact ⟨(rev_fixed_unique h hm) ▸ hmS, h⟩
      rw [e, ← sum_rev_parity f hf _ (fun i _ => Finset.mem_univ _)]
      exact (ZMod.intCast_eq_zero_iff_even).2 htot
    · have e : S.filter (fun j => Fin.rev j = j) = ∅ := by
        ext j
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        exact fun hj h => hm ⟨j, hj, h⟩
      rw [e, Finset.sum_empty, Int.cast_zero]

  set S : Finset (Fin n) := Finset.univ.filter fun i => Q.eval (u i) = 0 with hSdef
  set V₁ := LinearMap.ker (Matrix.toLin' (aeval γ.val Q)) with hV
  have hVspan : V₁ = Submodule.span (w.adicCompletion E)
      (Set.range fun i : S => fun k => (P : Matrix (Fin n) (Fin n) (w.adicCompletion E)) k i.1) := by
    rw [hV, hγP, aeval_conj, aeval_diagonal']
    exact ker_conj_diagonal_eq_span P _ S fun i => by simp [hSdef]
  have hli : LinearIndependent (w.adicCompletion E)
      (fun i : S => fun k => (P : Matrix (Fin n) (Fin n) (w.adicCompletion E)) k i.1) := by
    have h := (Matrix.linearIndependent_cols_iff_isUnit.2 P.isUnit).comp (fun i : S => i.1) Subtype.val_injective
    exact h
  set B := Module.finBasis (w.adicCompletion E) V₁
  have hBli : LinearIndependent (w.adicCompletion E) (fun i => ((B i : V₁) : Fin n → w.adicCompletion E)) :=
    B.linearIndependent.map' V₁.subtype (Submodule.ker_subtype V₁)
  have hBspan : Submodule.span (w.adicCompletion E)
      (Set.range fun i => ((B i : V₁) : Fin n → w.adicCompletion E)) = V₁ := by
    have e : (Set.range fun i => ((B i : V₁) : Fin n → w.adicCompletion E)) = V₁.subtype '' Set.range B := by
      ext x; simp
    rw [e, Submodule.span_image, B.span_eq, Submodule.map_top, Submodule.range_subtype]
  obtain ⟨d, hd0, hdet⟩ := GlobalTheory.T.gram_det_change_of_basis' (cj w) V₁
    (fun i : S => fun k => (P : Matrix (Fin n) (Fin n) (w.adicCompletion E)) k i.1)
    (fun i => ((B i : V₁) : Fin n → w.adicCompletion E)) hli hVspan.symm hBli hBspan
  have hG : (Matrix.of fun i j : S => ∑ k, cj w ((P : Matrix (Fin n) (Fin n) (w.adicCompletion E)) k i.1) *
      (P : Matrix (Fin n) (Fin n) (w.adicCompletion E)) k j.1) = H.submatrix (fun i : S => i.1) (fun i : S => i.1) := by
    ext i j
    rfl
  have key : (Matrix.of fun i j => ∑ k, cj w ((B i).1 k) * (B j).1 k).det =
      cj w d * d * (H.submatrix (fun i : S => i.1) (fun i : S => i.1)).det := by
    rw [← hG]
    exact hdet
  rw [key]
  by_cases hS : ∀ i ∈ S, Fin.rev i ∈ S
  · have hne : (H.submatrix (fun i : S => i.1) (fun i : S => i.1)).det ≠ 0 := by
      rw [det_submatrix_rev H hsupp S hS]
      exact mul_ne_zero (by rcases Int.units_eq_one_or (Equiv.Perm.sign (revOn S hS)) with h | h <;> simp [h])
        (Finset.prod_ne_zero_iff.2 fun j _ => hg0 j.1)
    rw [ordL_mul' (mul_ne_zero ((map_ne_zero (cj w)).2 hd0) hd0) hne,
      ordL_mul' ((map_ne_zero (cj w)).2 hd0) hd0, ordL_eq_of_v (hcj d), hordS S hS]
    obtain ⟨r, hr⟩ := hevenS S hS
    exact Even.neg_one_zpow ⟨ordL d + r, by rw [hr]; ring⟩
  · push_neg at hS
    obtain ⟨i, hi, hri⟩ := hS
    have hz : (H.submatrix (fun i : S => i.1) (fun i : S => i.1)).det = 0 := by
      refine Matrix.det_eq_zero_of_row_eq_zero ⟨i, hi⟩ fun j => ?_
      rw [Matrix.submatrix_apply]
      apply hsupp
      intro h
      apply hri
      rw [← h]
      exact j.2
    rw [hz, mul_zero, ordL_zero', zpow_zero]

end PositivityTheory.Rg.Bc.ArchbcB.B.M4.Kap
