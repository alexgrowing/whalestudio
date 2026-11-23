import Mathlib
import GroundTheory.Brauer.TensorSimple
set_option maxSynthPendingDepth 1

namespace GroundTheory.Brauer

open TensorProduct

universe u v w

section Azumaya

variable {K : Type u} [Field K] {A : Type v} [Ring A] [Algebra K A]
  [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]

omit [FiniteDimensional K A] in
variable (K A) in

theorem mulLeftRight_injective : Function.Injective (AlgHom.mulLeftRight K A) :=
  RingHom.injective (AlgHom.mulLeftRight K A).toRingHom

variable (K A) in

theorem mulLeftRight_bijective : Function.Bijective (AlgHom.mulLeftRight K A) := by
  refine ⟨mulLeftRight_injective K A, ?_⟩
  have h := LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (AlgHom.mulLeftRight K A).toLinearMap)
    (by rw [Module.finrank_tensorProduct, MulOpposite.finrank, Module.finrank_linearMap])
  exact h.mp (mulLeftRight_injective K A)

variable (K A) in

noncomputable def tensorOpAlgEquivEnd : A ⊗[K] Aᵐᵒᵖ ≃ₐ[K] Module.End K A :=
  AlgEquiv.ofBijective (AlgHom.mulLeftRight K A) (mulLeftRight_bijective K A)

end Azumaya

section Equivalence

variable {K : Type u} [Field K]

variable (K) in

noncomputable def csaOf (R : Type v) [Ring R] [Algebra K R] [Algebra.IsCentral K R]
    [IsSimpleRing R] [FiniteDimensional K R] : CSA.{u, v} K where
  toAlgCat := AlgCat.of K R

@[simp]
theorem csaOf_carrier (R : Type v) [Ring R] [Algebra K R] [Algebra.IsCentral K R]
    [IsSimpleRing R] [FiniteDimensional K R] : (csaOf K R : Type v) = R := rfl

noncomputable def matrixCSA (A : CSA.{u, v} K) (n : ℕ) [NeZero n] : CSA.{u, v} K :=
  csaOf K (Matrix (Fin n) (Fin n) A)

noncomputable def opCSA (A : CSA.{u, v} K) : CSA.{u, v} K :=
  csaOf K (A : Type v)ᵐᵒᵖ

theorem isBrauerEquivalent_of_algEquiv {A B : CSA.{u, v} K} (e : A ≃ₐ[K] B) :
    IsBrauerEquivalent A B :=
  ⟨1, 1, one_ne_zero, one_ne_zero, ⟨e.mapMatrix⟩⟩

theorem isBrauerEquivalent_of_algEquiv_matrix {A B : CSA.{u, v} K} {C : Type w} [Ring C]
    [Algebra K C] {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype ι']
    [DecidableEq ι'] [Nonempty ι'] (eA : A ≃ₐ[K] Matrix ι ι C) (eB : B ≃ₐ[K] Matrix ι' ι' C) :
    IsBrauerEquivalent A B := by
  refine ⟨Fintype.card ι', Fintype.card ι, Fintype.card_ne_zero, Fintype.card_ne_zero, ⟨?_⟩⟩
  exact (Matrix.reindexAlgEquiv K A (Fintype.equivFin ι').symm).trans <|
    eA.mapMatrix.trans <| (Matrix.compAlgEquiv ι' ι C K).trans <|
    (Matrix.reindexAlgEquiv K C (Equiv.prodComm ι' ι)).trans <|
    (Matrix.compAlgEquiv ι ι' C K).symm.trans <| eB.symm.mapMatrix.trans <|
    Matrix.reindexAlgEquiv K B (Fintype.equivFin ι)

theorem isBrauerEquivalent_matrixCSA (A : CSA.{u, v} K) (n : ℕ) [NeZero n] :
    IsBrauerEquivalent (matrixCSA A n) A :=
  ⟨1, n, one_ne_zero, NeZero.ne n, ⟨(Matrix.compAlgEquiv (Fin 1) (Fin n) A K).trans
    (Matrix.reindexAlgEquiv K A (Equiv.uniqueProd (Fin n) (Fin 1)))⟩⟩

theorem IsBrauerEquivalent.tensor {A A' B B' : CSA.{u, v} K} (hA : IsBrauerEquivalent A A')
    (hB : IsBrauerEquivalent B B') :
    IsBrauerEquivalent (tensorCSA A B) (tensorCSA A' B') := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := hA
  obtain ⟨p, q, hp, hq, ⟨f⟩⟩ := hB
  refine ⟨n * p, m * q, mul_ne_zero hn hp, mul_ne_zero hm hq, ⟨?_⟩⟩
  exact (Matrix.reindexAlgEquiv K _ finProdFinEquiv.symm).trans <|
    (Matrix.kroneckerTMulAlgEquiv (Fin n) (Fin p) K K A B).symm.trans <|
    (Algebra.TensorProduct.congr e f).trans <|
    (Matrix.kroneckerTMulAlgEquiv (Fin m) (Fin q) K K A' B').trans <|
    Matrix.reindexAlgEquiv K _ finProdFinEquiv

theorem IsBrauerEquivalent.op {A B : CSA.{u, v} K} (h : IsBrauerEquivalent A B) :
    IsBrauerEquivalent (opCSA A) (opCSA B) := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  exact ⟨n, m, hn, hm, ⟨(AlgEquiv.mopMatrix (R := K)).trans <| (AlgEquiv.op e).trans
    (AlgEquiv.mopMatrix (R := K)).symm⟩⟩

end Equivalence

section Group

variable (K : Type u) [Field K]

noncomputable def oneCSA : CSA.{u, u} K := csaOf K K

variable {K}

noncomputable def opTensorAlgEquivMatrix (A : Type v) [Ring A] [Algebra K A]
    [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] :
    Aᵐᵒᵖ ⊗[K] A ≃ₐ[K] Matrix (Fin (Module.finrank K A)) (Fin (Module.finrank K A)) K :=
  (Algebra.TensorProduct.comm K Aᵐᵒᵖ A).trans <| (tensorOpAlgEquivEnd K A).trans <|
    LinearMap.toMatrixAlgEquiv (Module.finBasis K A)

instance neZero_finrank (A : Type v) [Ring A] [Algebra K A] [IsSimpleRing A]
    [FiniteDimensional K A] : NeZero (Module.finrank K A) :=
  ⟨Module.finrank_pos.ne'⟩

noncomputable instance : Mul (BrauerGroup.{u, u} K) where
  mul := Quotient.map₂ tensorCSA fun _ _ hA _ _ hB => IsBrauerEquivalent.tensor hA hB

noncomputable instance : One (BrauerGroup.{u, u} K) where
  one := ⟦oneCSA K⟧

noncomputable instance : Inv (BrauerGroup.{u, u} K) where
  inv := Quotient.map opCSA fun _ _ h => IsBrauerEquivalent.op h

theorem BrauerGroup.mk_mul_mk (A B : CSA.{u, u} K) :
    (⟦A⟧ * ⟦B⟧ : BrauerGroup.{u, u} K) = ⟦tensorCSA A B⟧ := rfl

theorem BrauerGroup.one_def : (1 : BrauerGroup.{u, u} K) = ⟦oneCSA K⟧ := rfl

noncomputable instance : CommGroup (BrauerGroup.{u, u} K) where
  mul_assoc := by
    rintro ⟨A⟩ ⟨B⟩ ⟨C⟩
    exact Quotient.sound <| isBrauerEquivalent_of_algEquiv <|
      Algebra.TensorProduct.assoc K K K A B C
  one_mul := by
    rintro ⟨A⟩
    exact Quotient.sound <| isBrauerEquivalent_of_algEquiv <| Algebra.TensorProduct.lid K A
  mul_one := by
    rintro ⟨A⟩
    exact Quotient.sound <| isBrauerEquivalent_of_algEquiv <| Algebra.TensorProduct.rid K K A
  inv_mul_cancel := by
    rintro ⟨A⟩
    exact Quotient.sound <| IsBrauerEquivalent.trans
      (isBrauerEquivalent_of_algEquiv (B := matrixCSA (oneCSA K) (Module.finrank K A))
        (opTensorAlgEquivMatrix A))
      (isBrauerEquivalent_matrixCSA _ _)
  mul_comm := by
    rintro ⟨A⟩ ⟨B⟩
    exact Quotient.sound <| isBrauerEquivalent_of_algEquiv <| Algebra.TensorProduct.comm K A B

end Group

section DivisionPart

variable {K : Type u} [Field K]

section ColumnIdeal

variable {R : Type v} [Ring R] [Algebra K R] {D : Type w} [DivisionRing D] [Algebra K D]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def columnIdeal (e : R ≃ₐ[K] Matrix ι ι D) (i₀ : ι) : Ideal R where
  carrier := {x | ∀ i j, j ≠ i₀ → e x i j = 0}
  add_mem' {x y} hx hy i j hj := by
    simp only [map_add, Matrix.add_apply, hx i j hj, hy i j hj, add_zero]
  zero_mem' i j _ := by simp
  smul_mem' c x hx i j hj := by
    simp only [smul_eq_mul, map_mul, Matrix.mul_apply]
    exact Finset.sum_eq_zero fun k _ => by rw [hx k j hj, mul_zero]

variable (e : R ≃ₐ[K] Matrix ι ι D) (i₀ : ι)

theorem symm_single_mem_columnIdeal (d : D) :
    e.symm (Matrix.single i₀ i₀ d) ∈ columnIdeal e i₀ := by
  intro i j hj
  rw [e.apply_symm_apply]
  exact Matrix.single_apply_of_col_ne i₀ i (Ne.symm hj) d

theorem mul_symm_single_one {x : R} (hx : x ∈ columnIdeal e i₀) :
    x * e.symm (Matrix.single i₀ i₀ 1) = x := by
  apply e.injective
  rw [map_mul, e.apply_symm_apply]
  ext i j
  by_cases hj : j = i₀
  · rw [hj, Matrix.mul_single_apply_same, mul_one]
  · rw [Matrix.mul_single_apply_of_ne (hbj := hj), hx i j hj]

theorem apply_symm_single_one_mul {y : R} (hy : y ∈ columnIdeal e i₀) :
    e (e.symm (Matrix.single i₀ i₀ 1) * y) = Matrix.single i₀ i₀ (e y i₀ i₀) := by
  rw [map_mul, e.apply_symm_apply]
  ext i j
  by_cases hi : i = i₀
  · rw [hi, Matrix.single_mul_apply_same, one_mul]
    by_cases hj : j = i₀
    · rw [hj, Matrix.single_apply_same]
    · rw [Matrix.single_apply_of_col_ne i₀ i₀ (Ne.symm hj), hy i₀ j hj]
  · rw [Matrix.single_mul_apply_of_ne (h := hi), Matrix.single_apply_of_row_ne (Ne.symm hi)]

theorem isSimpleModule_columnIdeal : IsSimpleModule R (columnIdeal e i₀) := by
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨⟨⟨⟨_, symm_single_mem_columnIdeal e i₀ 1⟩, 0, fun h => ?_⟩⟩, fun x hx y => ?_⟩
  · have h' := congrArg (fun z : columnIdeal e i₀ => e (z : R) i₀ i₀) h
    simp at h'
  · have hx' : ∃ i, e (x : R) i i₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hx
      apply Subtype.ext
      apply e.injective
      ext i j
      by_cases hj : j = i₀
      · subst hj
        simpa using hcon i
      · simpa using x.2 i j hj
    obtain ⟨i, hi⟩ := hx'
    refine ⟨e.symm (Matrix.of fun k l => if l = i then e (y : R) k i₀ * (e (x : R) i i₀)⁻¹
      else 0), ?_⟩
    apply Subtype.ext
    apply e.injective
    ext k j
    simp only [LinearMap.toSpanSingleton_apply, Submodule.coe_smul, smul_eq_mul, map_mul,
      e.apply_symm_apply, Matrix.mul_apply, Matrix.of_apply, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hj : j = i₀
    · subst hj
      rw [mul_assoc, inv_mul_cancel₀ hi, mul_one]
    · rw [x.2 i j hj, y.2 k j hj, mul_zero]

def columnIdealUnit : columnIdeal e i₀ :=
  ⟨e.symm (Matrix.single i₀ i₀ 1), symm_single_mem_columnIdeal e i₀ 1⟩

def endEntry (f : Module.End R (columnIdeal e i₀)) : D :=
  e (f (columnIdealUnit e i₀) : R) i₀ i₀

theorem apply_endomorphism (f : Module.End R (columnIdeal e i₀)) (x : columnIdeal e i₀) :
    e (f x : R) = e (x : R) * Matrix.single i₀ i₀ (endEntry e i₀ f) := by
  have hx : x = (x : R) • columnIdealUnit e i₀ :=
    Subtype.ext (mul_symm_single_one e i₀ x.2).symm
  have hu : columnIdealUnit e i₀ =
      (e.symm (Matrix.single i₀ i₀ 1) : R) • columnIdealUnit e i₀ :=
    Subtype.ext (mul_symm_single_one e i₀ (symm_single_mem_columnIdeal e i₀ 1)).symm
  have hfu : e (f (columnIdealUnit e i₀) : R) = Matrix.single i₀ i₀ (endEntry e i₀ f) := by
    conv_lhs => rw [hu, map_smul, Submodule.coe_smul, smul_eq_mul]
    exact apply_symm_single_one_mul e i₀ (f _).2
  conv_lhs => rw [hx, map_smul, Submodule.coe_smul, smul_eq_mul, map_mul, hfu]

theorem endEntry_one : endEntry e i₀ (1 : Module.End R (columnIdeal e i₀)) = 1 := by
  simp [endEntry, columnIdealUnit]

theorem endEntry_mul (f g : Module.End R (columnIdeal e i₀)) :
    endEntry e i₀ (f * g) = endEntry e i₀ g * endEntry e i₀ f := by
  have h := apply_endomorphism e i₀ f (g (columnIdealUnit e i₀))
  have hu : e (columnIdealUnit e i₀ : R) = Matrix.single i₀ i₀ 1 := e.apply_symm_apply _
  rw [apply_endomorphism e i₀ g, hu, Matrix.single_mul_single_same, one_mul,
    Matrix.single_mul_single_same] at h
  conv_lhs => unfold endEntry
  rw [Module.End.mul_apply, h, Matrix.single_apply_same]

theorem endEntry_injective : Function.Injective (endEntry e i₀) := by
  intro f g h
  ext x
  apply e.injective
  rw [apply_endomorphism, apply_endomorphism, h]

def rightMulEnd (d : D) : Module.End R (columnIdeal e i₀) where
  toFun x := ⟨x * e.symm (Matrix.single i₀ i₀ d),
    Ideal.mul_mem_left _ _ (symm_single_mem_columnIdeal e i₀ d)⟩
  map_add' _ _ := Subtype.ext (add_mul _ _ _)
  map_smul' _ _ := Subtype.ext (mul_assoc _ _ _)

theorem endEntry_rightMulEnd (d : D) : endEntry e i₀ (rightMulEnd e i₀ d) = d := by
  simp [endEntry, rightMulEnd, columnIdealUnit]

noncomputable def endColumnIdealAlgEquiv : Module.End R (columnIdeal e i₀) ≃ₐ[K] Dᵐᵒᵖ :=
  AlgEquiv.ofBijective
    { toFun := fun f => MulOpposite.op (endEntry e i₀ f)
      map_one' := by rw [endEntry_one, MulOpposite.op_one]
      map_mul' := fun f g => by rw [endEntry_mul, MulOpposite.op_mul]
      map_zero' := by simp [endEntry]
      map_add' := fun f g => by simp [endEntry]
      commutes' := fun k => by
        simp [endEntry, columnIdealUnit, Module.algebraMap_end_apply, Algebra.smul_def,
          Matrix.algebraMap_matrix_apply] }
    ⟨fun f g h => endEntry_injective e i₀ (MulOpposite.op_injective h),
      fun d => ⟨rightMulEnd e i₀ d.unop, by
        show MulOpposite.op (endEntry e i₀ (rightMulEnd e i₀ d.unop)) = d
        rw [endEntry_rightMulEnd, MulOpposite.op_unop]⟩⟩

end ColumnIdeal

theorem exists_isSimpleModule_algEquiv_end {R : Type v} [Ring R] [Algebra K R] {D : Type w}
    [DivisionRing D] [Algebra K D] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (e : R ≃ₐ[K] Matrix ι ι D) :
    ∃ I : Ideal R, IsSimpleModule R I ∧ Nonempty (Module.End R I ≃ₐ[K] Dᵐᵒᵖ) :=
  ⟨_, isSimpleModule_columnIdeal e (Classical.arbitrary ι),
    ⟨endColumnIdealAlgEquiv e (Classical.arbitrary ι)⟩⟩

theorem nonempty_algEquiv_of_algEquiv_matrix {D : Type w} [DivisionRing D] [Algebra K D]
    {D' : Type*} [DivisionRing D'] [Algebra K D'] {ι ι' : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] [Fintype ι'] [DecidableEq ι'] [Nonempty ι']
    (e : Matrix ι ι D ≃ₐ[K] Matrix ι' ι' D') : Nonempty (D ≃ₐ[K] D') := by
  obtain ⟨I, hI, ⟨φ⟩⟩ := exists_isSimpleModule_algEquiv_end (AlgEquiv.refl : Matrix ι ι D ≃ₐ[K] _)
  obtain ⟨J, hJ, ⟨ψ⟩⟩ := exists_isSimpleModule_algEquiv_end e
  obtain ⟨g⟩ := IsSimpleRing.isIsotypic (Matrix ι ι D) (Matrix ι ι D) I J
  exact ⟨AlgEquiv.op.symm (φ.symm.trans ((g.conjAlgEquiv K).symm.trans ψ))⟩

theorem isCentral_of_isCentral_matrix {D : Type w} [Ring D] [Algebra K D] {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [Algebra.IsCentral K (Matrix ι ι D)] :
    Algebra.IsCentral K D where
  out z hz := by
    have hs : Matrix.scalar ι z ∈ Subalgebra.center K (Matrix ι ι D) := by
      rw [Subalgebra.mem_center_iff] at hz ⊢
      intro M
      ext i j
      simp [hz]
    obtain ⟨k, hk⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out hs)
    refine Algebra.mem_bot.mpr ⟨k, ?_⟩
    have := congrFun (congrFun hk (Classical.arbitrary ι)) (Classical.arbitrary ι)
    simpa [Matrix.algebraMap_matrix_apply] using this

theorem isBrauerEquivalent_iff_nonempty_algEquiv {A B : CSA.{u, v} K} {D : Type w}
    [DivisionRing D] [Algebra K D] {D' : Type*} [DivisionRing D'] [Algebra K D'] {ι ι' : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype ι'] [DecidableEq ι'] [Nonempty ι']
    (eA : A ≃ₐ[K] Matrix ι ι D) (eB : B ≃ₐ[K] Matrix ι' ι' D') :
    IsBrauerEquivalent A B ↔ Nonempty (D ≃ₐ[K] D') := by
  constructor
  · rintro ⟨n, m, hn, hm, ⟨f⟩⟩
    have : NeZero n := ⟨hn⟩
    have : NeZero m := ⟨hm⟩
    exact nonempty_algEquiv_of_algEquiv_matrix <|
      (Matrix.compAlgEquiv (Fin n) ι D K).symm.trans <| eA.symm.mapMatrix.trans <| f.trans <|
        eB.mapMatrix.trans <| Matrix.compAlgEquiv (Fin m) ι' D' K
  · rintro ⟨g⟩
    exact isBrauerEquivalent_of_algEquiv_matrix eA (eB.trans g.symm.mapMatrix)

def matrixFinOneAlgEquiv (C : Type*) [Ring C] [Algebra K C] :
    Matrix (Fin 1) (Fin 1) C ≃ₐ[K] C :=
  AlgEquiv.ofLinearEquiv Matrix.uniqueLinearEquiv (by simp)
    (fun x y => by simp [Matrix.mul_apply])

end DivisionPart

end GroundTheory.Brauer
