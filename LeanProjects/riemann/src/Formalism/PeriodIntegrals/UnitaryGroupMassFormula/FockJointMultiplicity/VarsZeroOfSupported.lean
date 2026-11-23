import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.GlobalTheory
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.ShapeProdVarMatNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.ExistGen

noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FJMA

open PI.FJM

section Generic

variable {σ : Type}

def FreeOf (S : Set σ) (G : MvPolynomial σ ℂ) : Prop := ∀ e ∈ G.support, ∀ v ∈ S, e v = 0

theorem vars_zero_of_supported {S : Set σ} {F : MvPolynomial σ ℂ} (hF : F ∈ supported ℂ S) :
    ∀ x ∈ F.support, ∀ v ∉ S, x v = 0 := by
  intro x hx v hv
  by_contra h
  exact hv ((mem_supported.1 hF) ((mem_vars_iff_mem_support v).2 ⟨x, hx, Finsupp.mem_support_iff.2 h⟩))

theorem exists_support_mul {S : Set σ} {F G : MvPolynomial σ ℂ} (hF : F ∈ supported ℂ S) (hF0 : F ≠ 0)
    (hG : FreeOf S G) {e' : σ →₀ ℕ} (he' : e' ∈ G.support) :
    ∃ e ∈ (F * G).support, ∀ v ∉ S, e v = e' v := by
  classical
  obtain ⟨e0, he0⟩ : F.support.Nonempty := Finset.nonempty_iff_ne_empty.2 (mt support_eq_empty.1 hF0)
  have hvars := vars_zero_of_supported hF
  refine ⟨e0 + e', ?_, fun v hv => by simp [hvars e0 he0 v hv]⟩
  rw [mem_support_iff, coeff_mul, Finset.sum_eq_single (e0, e')]
  · exact mul_ne_zero (mem_support_iff.1 he0) (mem_support_iff.1 he')
  · rintro ⟨x, y⟩ hxy hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hxy
    by_contra h
    have hx : x ∈ F.support := mem_support_iff.2 (left_ne_zero_of_mul h)
    have hy : y ∈ G.support := mem_support_iff.2 (right_ne_zero_of_mul h)
    apply hne
    have h1 : x = e0 := by
      ext v
      have := congrArg (fun f => f v) hxy
      simp only [Finsupp.add_apply] at this
      by_cases hv : v ∈ S
      · rw [hG y hy v hv, hG e' he' v hv] at this; omega
      · rw [hvars x hx v hv, hvars e0 he0 v hv]
    subst h1
    have h2 : y = e' := by
      ext v
      have := congrArg (fun f => f v) hxy
      simp only [Finsupp.add_apply] at this
      omega
    subst h2
    rfl
  · intro h
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (show (e0, e').1 + (e0, e').2 = e0 + e' from rfl)) h

theorem freeOf_of_mul {S T : Set σ} {F G : MvPolynomial σ ℂ} (hF : F ∈ supported ℂ S) (hF0 : F ≠ 0)
    (hG : FreeOf S G) (hH : FreeOf T (F * G)) (hST : Disjoint S T) : FreeOf T G := by
  intro e' he' v hv
  obtain ⟨e, he, hee⟩ := exists_support_mul hF hF0 hG he'
  have hvS : v ∉ S := fun h => Set.disjoint_left.1 hST h hv
  rw [← hee v hvS]
  exact hH e he v hv

theorem bRow_mul {m n : ℕ} (ι : Fin m × Fin n → σ) (a b : Fin m) (F G : MvPolynomial σ ℂ)
    (hF : ∀ x, pderiv (ι x) F = 0) : bRow ι a b (F * G) = F * bRow ι a b G := by
  unfold bRow
  simp only [LinearMap.sum_apply, Module.End.mul_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, Derivation.leibniz, hF, smul_eq_mul, mul_zero, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => by ring)

theorem bCol_mul {m n : ℕ} (ι : Fin m × Fin n → σ) (c d : Fin n) (F G : MvPolynomial σ ℂ)
    (hF : ∀ x, pderiv (ι x) F = 0) : bCol ι c d (F * G) = F * bCol ι c d G := by
  unfold bCol
  simp only [LinearMap.sum_apply, Module.End.mul_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, Derivation.leibniz, hF, smul_eq_mul, mul_zero, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => by ring)

theorem shapeProd_supported {m n : ℕ} (ι : Fin m × Fin n → σ) (α : List ℕ) :
    shapeProd (Matrix.of fun i k => (X (ι (i, k)) : MvPolynomial σ ℂ)) α ∈ supported ℂ (Set.range ι) :=
  PI.FJMD.shapeProd_mem _ _ _ (fun i k _ _ => by
    simp only [Matrix.of_apply]
    exact X_mem_supported.2 ⟨(i, k), rfl⟩)

theorem peel (hC : CauchyHW) {m n : ℕ} (ι : Fin m × Fin n → σ) (hι : Function.Injective ι)
    (α : Fin m → ℕ) (β : Fin n → ℕ) (S : Set σ) (F G : MvPolynomial σ ℂ) (hF : F ∈ supported ℂ S)
    (hF0 : F ≠ 0) (hG : FreeOf S G) (hS : ∀ x, ι x ∉ S) (hG0 : G ≠ 0) (hP : IsBlockHighestWeight ι α β (F * G)) :
    SqFacts α β ∧ ∃ Q, FreeOf (Set.range ι) Q ∧
      G = shapeProd (Matrix.of fun i k => (X (ι (i, k)) : MvPolynomial σ ℂ)) (List.ofFn α) * Q := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP
  have hFd : ∀ x, pderiv (ι x) F = 0 := fun x => PI.FJMX.pderiv_eq_zero_of_supported hF (hS x)
  have g1 : ∀ a b : Fin m, a < b → bRow ι a b G = 0 := by
    intro a b hab
    have := h1 a b hab
    rw [bRow_mul ι a b F G hFd] at this
    exact (mul_eq_zero.1 this).resolve_left hF0
  have g2 : ∀ c d : Fin n, c < d → bCol ι c d G = 0 := by
    intro c d hcd
    have := h2 c d hcd
    rw [bCol_mul ι c d F G hFd] at this
    exact (mul_eq_zero.1 this).resolve_left hF0
  have g3 : ∀ e ∈ G.support, (∀ i, ∑ k : Fin n, e (ι (i, k)) = α i) ∧ (∀ k, ∑ i : Fin m, e (ι (i, k)) = β k) := by
    intro e' he'
    obtain ⟨e, he, hee⟩ := exists_support_mul hF hF0 hG he'
    obtain ⟨k1, k2⟩ := h3 e he
    refine ⟨fun i => ?_, fun k => ?_⟩
    · rw [← k1 i]; exact Finset.sum_congr rfl (fun k _ => (hee _ (hS _)).symm)
    · rw [← k2 k]; exact Finset.sum_congr rfl (fun i _ => (hee _ (hS _)).symm)
  obtain ⟨r1, r2, r3, Q, hQ, hGQ⟩ := hC σ m n ι hι α β G hG0 g1 g2 g3 h4 h5
  refine ⟨⟨r1, r2, r3⟩, Q, ?_, hGQ⟩
  intro e he v hv
  obtain ⟨x, rfl⟩ := hv
  exact hQ e he x

end Generic

section Blocks

variable {σ : Type}

abbrev blkP {m n : ℕ} (ι : Fin m × Fin n → σ) (α : Fin m → ℕ) : MvPolynomial σ ℂ :=
  shapeProd (Matrix.of fun i k => (X (ι (i, k)) : MvPolynomial σ ℂ)) (List.ofFn α)

theorem freeOf_union {S T : Set σ} {G : MvPolynomial σ ℂ} (h1 : FreeOf S G) (h2 : FreeOf T G) :
    FreeOf (S ∪ T) G := by
  intro e he v hv
  rcases hv with hv | hv
  · exact h1 e he v hv
  · exact h2 e he v hv

theorem eq_C_of_support {Q : MvPolynomial σ ℂ} (h : ∀ e ∈ Q.support, e = 0) : Q = C (coeff 0 Q) := by
  classical
  ext m
  rw [coeff_C]
  by_cases hm : m = 0
  · subst hm; simp
  · rw [if_neg (Ne.symm hm)]
    by_contra hc
    exact hm (h m (mem_support_iff.2 hc))

end Blocks

section Line

variable (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ)

theorem injA : Function.Injective (ιA p q r s μ μ') := by
  rintro ⟨i, k⟩ ⟨i', k'⟩ h
  simp only [ιA, Prod.mk.injEq, Sum.inl.injEq] at h
  exact Prod.ext (Fin.castLE_injective _ h.1) (Fin.castLE_injective _ h.2)

theorem injB : Function.Injective (ιB p q r s μ μ') := by
  rintro ⟨i, k⟩ ⟨i', k'⟩ h
  simp only [ιB, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, Fin.rev_inj] at h
  exact Prod.ext (Fin.castLE_injective _ h.1) (Fin.castLE_injective _ h.2)

theorem injC : Function.Injective (ιC p q r s μ μ') := by
  rintro ⟨i, k⟩ ⟨i', k'⟩ h
  simp only [ιC, Prod.mk.injEq, Sum.inr.injEq] at h
  exact Prod.ext (Fin.castLE_injective _ h.1) (Fin.castLE_injective _ h.2)

theorem injD : Function.Injective (ιD p q r s μ μ') := by
  rintro ⟨i, k⟩ ⟨i', k'⟩ h
  simp only [ιD, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, Fin.rev_inj] at h
  exact Prod.ext (Fin.castLE_injective _ h.1) (Fin.castLE_injective _ h.2)

theorem dBA : ∀ x, ιB p q r s μ μ' x ∉ Set.range (ιA p q r s μ μ') := by
  rintro x ⟨y, hy⟩
  simp [ιA, ιB] at hy

theorem dCAB : ∀ x, ιC p q r s μ μ' x ∉ Set.range (ιA p q r s μ μ') ∪ Set.range (ιB p q r s μ μ') := by
  rintro x (⟨y, hy⟩ | ⟨y, hy⟩) <;> simp [ιA, ιB, ιC] at hy

theorem dDABC : ∀ x, ιD p q r s μ μ' x ∉
    Set.range (ιA p q r s μ μ') ∪ Set.range (ιB p q r s μ μ') ∪ Set.range (ιC p q r s μ μ') := by
  rintro x ((⟨y, hy⟩ | ⟨y, hy⟩) | ⟨y, hy⟩) <;> simp [ιA, ιB, ιC, ιD] at hy

theorem disj_of {S : Set (Ln p q r s)} {m n : ℕ} (ι : Fin m × Fin n → Ln p q r s) (h : ∀ x, ι x ∉ S) :
    Disjoint (Set.range ι) S := by
  refine Set.disjoint_left.2 ?_
  rintro v ⟨x, rfl⟩ hv
  exact h x hv

end Line

theorem line_of (hC : CauchyHW) (hA : HypA) (hB : HypB) (hCc : HypC) (hD : HypD) (hCov : CoverJ)
    (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (P : Pol p q r s) (hP : MinHyp p q r s μ μ' P) :
    BlockFacts p q r s μ μ' ∧ ∃ c : ℂ, P = C c * vLine p q r s μ μ' := by
  have hP0 : P ≠ 0 := hP.2.1

  obtain ⟨sqA, QA, fA, eA⟩ := peel hC (ιA p q r s μ μ') (injA p q r s μ μ') _ _ ∅ 1 P
    (supported ℂ (∅ : Set (Ln p q r s))).one_mem one_ne_zero (fun _ _ _ h => h.elim) (fun _ h => h) hP0
    (by rw [one_mul]; exact hA p q r s μ μ' P hP)
  have hQA0 : QA ≠ 0 := by rintro rfl; rw [mul_zero] at eA; exact hP0 eA
  have shA0 : blkP (ιA p q r s μ μ') (αA p q r s μ) ≠ 0 :=
    left_ne_zero_of_mul (show blkP (ιA p q r s μ μ') (αA p q r s μ) * QA ≠ 0 from eA ▸ hP0)
  have suA := shapeProd_supported (ιA p q r s μ μ') (List.ofFn (αA p q r s μ))

  obtain ⟨sqB, QB, fB, eB⟩ := peel hC (ιB p q r s μ μ') (injB p q r s μ μ') _ _ (Set.range (ιA p q r s μ μ'))
    _ QA suA shA0 fA (dBA p q r s μ μ') hQA0 (by rw [← eA]; exact hB p q r s μ μ' P hP)
  have hQB0 : QB ≠ 0 := by rintro rfl; rw [mul_zero] at eB; exact hQA0 eB
  have shB0 : blkP (ιB p q r s μ μ') (αB p q r s μ) ≠ 0 :=
    left_ne_zero_of_mul (show blkP (ιB p q r s μ μ') (αB p q r s μ) * QB ≠ 0 from eB ▸ hQA0)
  have suB := shapeProd_supported (ιB p q r s μ μ') (List.ofFn (αB p q r s μ))
  have fBA : FreeOf (Set.range (ιA p q r s μ μ')) QB :=
    freeOf_of_mul suB shB0 fB (eB ▸ fA) (disj_of p q r s (ιB p q r s μ μ') (dBA p q r s μ μ'))

  obtain ⟨sqC, QC, fC, eC⟩ := peel hC (ιC p q r s μ μ') (injC p q r s μ μ') _ _
    (Set.range (ιA p q r s μ μ') ∪ Set.range (ιB p q r s μ μ')) _ QB
    (Subalgebra.mul_mem _ (supported_mono Set.subset_union_left suA) (supported_mono Set.subset_union_right suB))
    (mul_ne_zero shA0 shB0) (freeOf_union fBA fB) (dCAB p q r s μ μ') hQB0
    (by rw [mul_assoc, ← eB, ← eA]; exact hCc p q r s μ μ' P hP)
  have hQC0 : QC ≠ 0 := by rintro rfl; rw [mul_zero] at eC; exact hQB0 eC
  have shC0 : blkP (ιC p q r s μ μ') (αC p q r s μ) ≠ 0 :=
    left_ne_zero_of_mul (show blkP (ιC p q r s μ μ') (αC p q r s μ) * QC ≠ 0 from eC ▸ hQB0)
  have suC := shapeProd_supported (ιC p q r s μ μ') (List.ofFn (αC p q r s μ))
  have fCAB : FreeOf (Set.range (ιA p q r s μ μ') ∪ Set.range (ιB p q r s μ μ')) QC :=
    freeOf_of_mul suC shC0 fC (eC ▸ freeOf_union fBA fB) (disj_of p q r s (ιC p q r s μ μ') (dCAB p q r s μ μ'))

  obtain ⟨sqD, QD, fD, eD⟩ := peel hC (ιD p q r s μ μ') (injD p q r s μ μ') _ _
    (Set.range (ιA p q r s μ μ') ∪ Set.range (ιB p q r s μ μ') ∪ Set.range (ιC p q r s μ μ')) _ QC
    (Subalgebra.mul_mem _ (Subalgebra.mul_mem _
      (supported_mono (Set.subset_union_left.trans Set.subset_union_left) suA)
      (supported_mono (Set.subset_union_right.trans Set.subset_union_left) suB))
      (supported_mono Set.subset_union_right suC))
    (mul_ne_zero (mul_ne_zero shA0 shB0) shC0) (freeOf_union fCAB fC) (dDABC p q r s μ μ') hQC0
    (by rw [mul_assoc, ← eC, mul_assoc, ← eB, ← eA]; exact hD p q r s μ μ' P hP)
  have shD0 : blkP (ιD p q r s μ μ') (αD p q r s μ) ≠ 0 :=
    left_ne_zero_of_mul (show blkP (ιD p q r s μ μ') (αD p q r s μ) * QD ≠ 0 from eD ▸ hQC0)
  have suD := shapeProd_supported (ιD p q r s μ μ') (List.ofFn (αD p q r s μ))
  have fDABC : FreeOf (Set.range (ιA p q r s μ μ') ∪ Set.range (ιB p q r s μ μ') ∪ Set.range (ιC p q r s μ μ')) QD :=
    freeOf_of_mul suD shD0 fD (eD ▸ freeOf_union fCAB fC) (disj_of p q r s (ιD p q r s μ μ') (dDABC p q r s μ μ'))
  have hF4 : blkP (ιA p q r s μ μ') (αA p q r s μ) * blkP (ιB p q r s μ μ') (αB p q r s μ) *
      blkP (ιC p q r s μ μ') (αC p q r s μ) * blkP (ιD p q r s μ μ') (αD p q r s μ) ∈
      supported ℂ (Set.range (ιA p q r s μ μ') ∪ Set.range (ιB p q r s μ μ') ∪ Set.range (ιC p q r s μ μ') ∪
        Set.range (ιD p q r s μ μ')) :=
    Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _
      (supported_mono ((Set.subset_union_left.trans Set.subset_union_left).trans Set.subset_union_left) suA)
      (supported_mono ((Set.subset_union_right.trans Set.subset_union_left).trans Set.subset_union_left) suB))
      (supported_mono (Set.subset_union_right.trans Set.subset_union_left) suC))
      (supported_mono Set.subset_union_right suD)
  have hF40 := mul_ne_zero (mul_ne_zero (mul_ne_zero shA0 shB0) shC0) shD0
  have hPeq : P = blkP (ιA p q r s μ μ') (αA p q r s μ) * blkP (ιB p q r s μ μ') (αB p q r s μ) *
      blkP (ιC p q r s μ μ') (αC p q r s μ) * blkP (ιD p q r s μ μ') (αD p q r s μ) * QD := by
    rw [eA, eB, eC, eD]; ring
  have fD4 := freeOf_union fDABC fD
  have hsupp : ∀ e' ∈ QD.support, e' = 0 := by
    intro e' he'
    obtain ⟨e, he, hee⟩ := exists_support_mul hF4 hF40 fD4 he'
    rw [← hPeq] at he
    ext v
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    by_contra hv
    have hvS : v ∉ Set.range (ιA p q r s μ μ') ∪ Set.range (ιB p q r s μ μ') ∪ Set.range (ιC p q r s μ μ') ∪
        Set.range (ιD p q r s μ μ') := fun h => hv (fD4 e' he' v h)
    exact hvS (hCov p q r s μ μ' P hP e he v (by rw [hee v hvS]; exact hv))
  refine ⟨⟨sqA, sqB, sqC, sqD⟩, coeff 0 QD, ?_⟩
  conv_lhs => rw [hPeq, eq_C_of_support hsupp]
  unfold vLine
  ring

end PI.FJMA
