import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsMemRowHighestTotalDegreeEqTwo
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CommuteRowOpRightMixedOp
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Sl2NonnegWeightOfHighestWeightVector
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsJointIntEigenvectorOfStable
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SumSmulMemOfSumZpowSmulMem
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsEqMulProdMinors
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EventuallyExistsMulIsLowerTriangular

open MvPolynomial Matrix TensorProduct
open GlobalTheory.MvPoly

namespace GlobalTheory.Harm

section CoeffForm

variable {F K σ : Type*} [Field F] [CommRing K] [Algebra F K]

noncomputable def coeffForm (φ : K →ₗ[F] F) : MvPolynomial σ K →ₗ[F] MvPolynomial σ F :=
  (TensorProduct.lid F _).toLinearMap ∘ₗ φ.rTensor _ ∘ₗ
    ((algebraTensorAlgEquiv (σ := σ) F K).symm.toLinearEquiv.toLinearMap.restrictScalars F)

theorem coeffForm_smul_map (φ : K →ₗ[F] F) (r : K) (Q : MvPolynomial σ F) :
    coeffForm φ (r • MvPolynomial.map (algebraMap F K) Q) = φ r • Q := by
  rw [← algebraTensorAlgEquiv_tmul]
  simp [coeffForm, -algebraTensorAlgEquiv_tmul]

theorem coeffForm_monomial (φ : K →ₗ[F] F) (m : σ →₀ ℕ) (r : K) :
    coeffForm φ (monomial m r) = monomial m (φ r) := by
  have := coeffForm_smul_map φ r (monomial m (1 : F))
  simpa [smul_monomial] using this

theorem coeff_coeffForm (φ : K →ₗ[F] F) (m : σ →₀ ℕ) (P : MvPolynomial σ K) :
    coeff m (coeffForm φ P) = φ (coeff m P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d r => rw [coeffForm_monomial, coeff_monomial, coeff_monomial]; split_ifs <;> simp
  | add P Q hP hQ => simp only [map_add, coeff_add, hP, hQ]

theorem coeffForm_comm (φ : K →ₗ[F] F) (L : MvPolynomial σ F →ₗ[F] MvPolynomial σ F)
    (L' : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (h : ∀ Q, MvPolynomial.map (algebraMap F K) (L Q) = L' (MvPolynomial.map (algebraMap F K) Q))
    (P : MvPolynomial σ K) : coeffForm φ (L' P) = L (coeffForm φ P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial d r =>
    have e : (monomial d r : MvPolynomial σ K) =
        r • MvPolynomial.map (algebraMap F K) (monomial d 1) := by simp [smul_monomial]
    rw [e, map_smul, ← h, coeffForm_smul_map, coeffForm_smul_map, map_smul]
  | add P Q hP hQ => simp only [map_add, hP, hQ]

theorem mem_span_map_of_coeffForm_mem (V : Set (MvPolynomial σ F)) {P : MvPolynomial σ K}
    (h : ∀ φ : K →ₗ[F] F, coeffForm φ P ∈ V) :
    P ∈ Submodule.span K (MvPolynomial.map (algebraMap F K) '' V) := by
  classical
  let b := Module.Basis.ofVectorSpace F K
  let x := TensorProduct.equivFinsuppOfBasisLeft b ((algebraTensorAlgEquiv F K).symm P)
  have hx (i) : x i = coeffForm (b.coord i) P := TensorProduct.equivFinsuppOfBasisLeft_apply b _ i
  have e : P = algebraTensorAlgEquiv F K ((TensorProduct.equivFinsuppOfBasisLeft b).symm x) := by
    simp [x]
  rw [e, TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [algebraTensorAlgEquiv_tmul, hx]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h _, rfl⟩)

theorem coeffForm_mem_span (φ : K →ₗ[F] F) (V : Set (MvPolynomial σ F)) {P : MvPolynomial σ K}
    (h : P ∈ Submodule.span K (MvPolynomial.map (algebraMap F K) '' V)) :
    coeffForm φ P ∈ Submodule.span F V := by
  suffices ∀ r : K, coeffForm φ (r • P) ∈ Submodule.span F V by simpa using this 1
  induction h using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨Q, hQ, rfl⟩ := hP
    intro r
    rw [coeffForm_smul_map]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hQ)
  | zero => simp
  | add P Q _ _ hP hQ => intro r; rw [smul_add, map_add]; exact add_mem (hP r) (hQ r)
  | smul s P _ hP => intro r; rw [smul_smul]; exact hP _

theorem mem_span_of_map_mem_span [Nontrivial K] (V : Set (MvPolynomial σ F))
    {P : MvPolynomial σ F} (h : MvPolynomial.map (algebraMap F K) P ∈
      Submodule.span K (MvPolynomial.map (algebraMap F K) '' V)) : P ∈ Submodule.span F V := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F (one_ne_zero (α := K))
  have := coeffForm_mem_span φ V h
  rwa [← one_smul K (MvPolynomial.map _ P), coeffForm_smul_map, hφ, one_smul] at this

variable {T κ : Type*} [Fintype κ] {p q : ℕ}

theorem coeffForm_mem_rowHighest (φ : K →ₗ[F] F) {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ}
    {P : Poly K T p q κ} (hP : P ∈ rowHighest K c c') : coeffForm φ P ∈ rowHighest F c c' := by
  obtain ⟨h₁, h₂, h₃⟩ := mem_rowHighest_iff_rowAdd.1 hP
  refine mem_rowHighest_iff_rowAdd.2 ⟨fun t a b => ?_, fun t r m hm => h₂ t r fun e => hm ?_,
    fun t r r' hr s => ?_⟩
  · rw [← coeffForm_comm φ _ _ (map_laplacian _ t a b), h₁, map_zero]
  · rw [coeff_coeffForm, e, map_zero]
  · have := coeffForm_comm φ (rowAdd t r r' (s : F)).toLinearMap
      (rowAdd t r r' (s : K)).toLinearMap
      (fun Q => by simpa using map_rowAdd (algebraMap F K) t r r' (s : F) Q) P
    simpa [h₃ t r r' hr s] using this.symm

theorem span_map_rowHighest_algebraMap (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) :
    Submodule.span K (MvPolynomial.map (algebraMap F K) ''
      (rowHighest (κ := κ) F c c' : Set (Poly F T p q κ))) = rowHighest K c c' :=
  le_antisymm (Submodule.span_le.2 (by rintro _ ⟨P, hP, rfl⟩; exact map_mem_rowHighest _ hP))
    fun _ hP => mem_span_map_of_coeffForm_mem _ fun φ => coeffForm_mem_rowHighest φ hP

end CoeffForm

section Words

variable {R S : Type*} [CommRing R] [CommRing S] {T κ : Type*} {p q n : ℕ}

theorem map_colLie (f : R →+* S) (t : T) (k l : κ) (P : Poly R T p q κ) :
    MvPolynomial.map f (colLie R p q t k l P) = colLie S p q t k l (MvPolynomial.map f P) := by
  simp [colLie_apply, pderiv_map]

theorem colLie_lie [DecidableEq κ] (t : T) (i j k l : κ) :
    colLie R p q t i j * colLie R p q t k l - colLie R p q t k l * colLie R p q t i j =
      (if j = k then colLie R p q t i l else 0) - (if l = i then colLie R p q t k j else 0) := by
  have e (k l : κ) : colLie R p q t k l = Capelli.mixedOp R (fun w : Fin p × κ => xVar t w.1 w.2)
      (fun w : Fin q × κ => yVar t w.1 w.2) k l :=
    LinearMap.ext fun P => by rw [colLie_apply, Capelli.mixedOp_apply]
  simp only [e]
  exact Capelli.mixedOp_lie _ (fun u w e => by simpa [Prod.ext_iff] using e) _
    (fun u w e => by simpa [Prod.ext_iff] using e) (fun u w => by simp) i j k l

theorem fockInner_colLie (t : T) (k l : κ) (P Q : Poly ℂ T p q κ) :
    fockInner (colLie ℂ p q t k l P) Q = fockInner P (colLie ℂ p q t l k Q) := by
  rw [colLie_apply, colLie_apply, ← fockInnerₛₗ_apply, ← fockInnerₛₗ_apply]
  simp only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, fockInnerₛₗ_apply,
    fockInner_X_mul_left, fockInner_pderiv_left]

variable [Fintype T] (h : p + q ≤ n) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)

variable (R) in

noncomputable def colWord (w : List (T × Fin n × Fin n)) : Poly R T p q (Fin n) :=
  w.foldr (fun i P => colLie R p q i.1 i.2.1 i.2.2 P) (basePoly R h c c')

theorem map_colWord (f : R →+* S) (w : List (T × Fin n × Fin n)) :
    MvPolynomial.map f (colWord R h c c' w) = colWord S h c c' w := by
  induction w with
  | nil => exact map_basePoly h c c' f
  | cons i w ih => exact (map_colLie f _ _ _ _).trans (congrArg _ ih)

theorem image_map_range_colWord (f : R →+* S) :
    MvPolynomial.map f '' Set.range (colWord R h c c') = Set.range (colWord S h c c') := by
  rw [← Set.range_comp]
  exact congrArg _ (funext (map_colWord h c c' f))

theorem colWord_mem_orbitSpan {K : Type*} [Field K] [Infinite K] (w : List (T × Fin n × Fin n)) :
    colWord K h c c' w ∈ orbitSpan K h c c' := by
  induction w with
  | nil => exact basePoly_mem h c c'
  | cons i w ih => exact colLie_mem_orbitSpan h c c' _ _ _ ih

theorem colWord_mem_rowHighest (w : List (T × Fin n × Fin n)) :
    colWord R h c c' w ∈ rowHighest R c c' := by
  rw [← map_colWord h c c' (Int.castRingHom R)]
  refine map_mem_rowHighest _ ((map_mem_rowHighest_iff (f := Int.castRingHom ℚ)
    Int.cast_injective).1 ?_)
  rw [map_colWord]
  exact orbitSpan_le_rowHighest h c c' (colWord_mem_orbitSpan h c c' w)

theorem colLie_mem_span_colWord (t : T) (k l : Fin n) {P : Poly R T p q (Fin n)}
    (hP : P ∈ Submodule.span R (Set.range (colWord R h c c'))) :
    colLie R p q t k l P ∈ Submodule.span R (Set.range (colWord R h c c')) := by
  refine (Submodule.span_le (p := Submodule.comap (colLie R p q t k l)
    (Submodule.span R (Set.range (colWord R h c c'))))).2 ?_ hP
  rintro _ ⟨w, rfl⟩
  exact Submodule.subset_span ⟨(t, k, l) :: w, rfl⟩

theorem basePoly_mem_of_colLie_stable {K : Type*} [Field K] [CharZero K]
    (W : Submodule K (Poly K T p q (Fin n))) (hW : W ≤ rowHighest K c c')
    (hs : ∀ t k l, ∀ w ∈ W, colLie K p q t k l w ∈ W) (hW0 : W ≠ ⊥) : basePoly K h c c' ∈ W := by
  classical
  have := Submodule.finiteDimensional_of_le hW
  obtain ⟨v, hv, hv0, hup, μ, hμ⟩ := exists_highest_vector (colLie K p q) colLie_diag_comm
    (iSup_iInf_eigenspace_colLie K T p q (Fin n)) W hs hW0
  obtain ⟨r, rfl⟩ := exists_eq_smul_basePoly h c c' (hW hv) μ
    (fun t => highest_weight_antitone _ (colLie_lie t) W (hs t) v hv hv0 _ (hup t) (hμ t))
    (fun t k l hkl => (colLie_apply t k l v).symm.trans (hup t k l hkl))
    fun t k => (colLie_apply t k k v).symm.trans (hμ t k)
  exact (W.smul_mem_iff (left_ne_zero_of_smul hv0)).1 hv

theorem rowHighest_le_span_colWord_complex :
    rowHighest ℂ c c' ≤ Submodule.span ℂ (Set.range (colWord ℂ h c c')) := by
  have hself (P : Poly ℂ T p q (Fin n)) (hP : fockInner P P = 0) : P = 0 := by
    rw [fockInner_self] at hP
    exact fockNormSq_eq_zero.mp (RCLike.ofReal_eq_zero.mp hP)
  set U := Submodule.span ℂ (Set.range (colWord ℂ h c c')) with hU
  have hUle : U ≤ rowHighest ℂ c c' :=
    Submodule.span_le.2 (by rintro _ ⟨w, rfl⟩; exact colWord_mem_rowHighest h c c' w)
  have := Submodule.finiteDimensional_of_le hUle
  let W : Submodule ℂ (Poly ℂ T p q (Fin n)) :=
    rowHighest ℂ c c' ⊓ ⨅ u ∈ U, LinearMap.ker ((fockInnerₛₗ _ ℂ).flip u)
  have hW (P) : P ∈ W ↔ P ∈ rowHighest ℂ c c' ∧ ∀ u ∈ U, fockInner P u = 0 := by
    simp [W, Submodule.mem_iInf]
  have hW0 : W = ⊥ := by
    by_contra hW0
    have := basePoly_mem_of_colLie_stable h c c' W inf_le_left (fun t k l w hw => ?_) hW0
    · exact basePoly_ne_zero h c c'
        (hself _ (((hW _).1 this).2 _ (Submodule.subset_span ⟨[], rfl⟩)))
    · rw [hW] at hw ⊢
      refine ⟨colLie_mem_of_colAct_mem _ (fun g _ hP => colAct_mem_rowHighest g hP) t k l hw.1,
        fun u hu => ?_⟩
      rw [fockInner_colLie]
      exact hw.2 _ (colLie_mem_span_colWord h c c' t l k hu)
  intro P hP
  obtain ⟨Q, hQ, hperp⟩ := exists_fockInner_sub_eq_zero U P
  have : P - Q ∈ W := (hW _).2 ⟨sub_mem hP (hUle hQ), hperp⟩
  rw [hW0, Submodule.mem_bot, sub_eq_zero] at this
  exact this ▸ hQ

variable (K : Type*)

theorem rowHighest_eq_span_colWord [CommRing K] [Algebra ℚ K] :
    rowHighest K c c' = Submodule.span K (Set.range (colWord K h c c')) := by
  refine le_antisymm ?_
    (Submodule.span_le.2 (by rintro _ ⟨w, rfl⟩; exact colWord_mem_rowHighest h c c' w))
  rw [← span_map_rowHighest_algebraMap (F := ℚ), Submodule.span_le]
  rintro _ ⟨P, hP, rfl⟩
  have h₁ := rowHighest_le_span_colWord_complex h c c' (map_mem_rowHighest (algebraMap ℚ ℂ) hP)
  rw [← image_map_range_colWord h c c' (algebraMap ℚ ℂ)] at h₁
  have h₂ := mem_span_of_map_mem_span _ h₁
  clear hP h₁
  induction h₂ using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨w, rfl⟩ := hP
    rw [map_colWord]
    exact Submodule.subset_span ⟨w, rfl⟩
  | zero => simp
  | add P Q _ _ hP hQ => rw [map_add]; exact add_mem hP hQ
  | smul r P _ hP =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hP

theorem rowHighest_eq_orbitSpan [Field K] [CharZero K] :
    rowHighest K c c' = orbitSpan K h c c' := by
  refine le_antisymm ?_ (orbitSpan_le_rowHighest h c c')
  rw [rowHighest_eq_span_colWord h, Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  exact colWord_mem_orbitSpan h c c' w

include h in

theorem span_map_rowHighest_int [CommRing K] [Algebra ℚ K] :
    Submodule.span K (MvPolynomial.map (Int.castRingHom K) ''
      (rowHighest (κ := Fin n) ℤ c c' : Set (Poly ℤ T p q (Fin n)))) = rowHighest K c c' := by
  refine le_antisymm
    (Submodule.span_le.2 (by rintro _ ⟨P, hP, rfl⟩; exact map_mem_rowHighest _ hP)) ?_
  rw [rowHighest_eq_span_colWord h c c' K, ← image_map_range_colWord h c c' (Int.castRingHom K)]
  refine Submodule.span_mono (Set.image_mono ?_)
  rintro _ ⟨w, rfl⟩
  exact colWord_mem_rowHighest h c c' w

end Words

theorem rowHighest_orbitSpan_main {T : Type*} [Fintype T] {p q n : ℕ} (h : p + q ≤ n)
    (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) (K : Type*) [Field K] [CharZero K] :
    rowHighest ℂ c c' = orbitSpan ℂ h c c' ∧ rowHighest K c c' = orbitSpan K h c c' ∧
      Submodule.span K (MvPolynomial.map (Int.castRingHom K) ''
        (rowHighest (κ := Fin n) ℤ c c' : Set (Poly ℤ T p q (Fin n)))) = rowHighest K c c' :=
  ⟨rowHighest_eq_orbitSpan h c c' ℂ, rowHighest_eq_orbitSpan h c c' K,
    span_map_rowHighest_int h c c' K⟩

end GlobalTheory.Harm
