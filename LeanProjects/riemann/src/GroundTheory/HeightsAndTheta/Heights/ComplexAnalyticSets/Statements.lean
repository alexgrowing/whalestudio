import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial Pointwise

noncomputable section

variable {n d : ℕ}

def zeroSet (J : Ideal (MvPolynomial (Fin n) ℂ)) : Set (Fin n → ℂ) :=
  {x | ∀ q ∈ J, eval x q = 0}

def linPoly (A : Matrix (Fin d) (Fin n) ℂ) (i : Fin d) : MvPolynomial (Fin n) ℂ :=
  ∑ j, C (A i j) * X j

def pullback (A : Matrix (Fin d) (Fin n) ℂ) : MvPolynomial (Fin d) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  aeval (linPoly A)

def projHom (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) :
    MvPolynomial (Fin d) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ ⧸ J :=
  (Ideal.Quotient.mkₐ ℂ J).comp (pullback A)

structure IsFiniteProjection (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) :
    Prop where

  injective : Function.Injective (projHom J A)

  finite : (projHom J A).toRingHom.Finite

def projDegree (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) : ℕ :=
  letI : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (projHom J A).toRingHom.toAlgebra
  letI : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.toModule
  Module.finrank (FractionRing (MvPolynomial (Fin d) ℂ))
    (TensorProduct (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))
      (MvPolynomial (Fin n) ℂ ⧸ J))

def fibre (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (y : Fin d → ℂ) :
    Set (Fin n → ℂ) :=
  {x | x ∈ zeroSet J ∧ A.mulVec x = y}

def IsZariskiOpen (U : Set (Matrix (Fin d) (Fin n) ℂ)) : Prop :=
  ∃ S : Set (MvPolynomial (Fin d × Fin n) ℂ),
    U = {A | ∃ p ∈ S, eval (fun ij : Fin d × Fin n => A ij.1 ij.2) p ≠ 0}

def orthoRows (d n : ℕ) : Set (Matrix (Fin d) (Fin n) ℂ) :=
  {A | A * A.conjTranspose = 1}

def GenericProjectionFinite.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
      (∃ U : Set (Matrix (Fin d) (Fin n) ℂ), IsZariskiOpen U ∧ U.Nonempty ∧
        ∀ A ∈ U, IsFiniteProjection J A) ∧
      {A : Matrix (Fin d) (Fin n) ℂ | IsFiniteProjection J A}.Nonempty ∧
      (∀ D : Set (Matrix (Fin d) (Fin n) ℂ), D ⊆ orthoRows d n → orthoRows d n ⊆ closure D →
        ∃ A ∈ D, IsFiniteProjection J A) ∧
      (∀ (m : ℕ) (F : Fin m → Matrix.unitaryGroup (Fin n) ℂ),
        ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ (k : Fin m) (s : Fin d ↪ Fin n),
          IsFiniteProjection J (((F k : Matrix (Fin n) (Fin n) ℂ) * U).submatrix s id))

def FibreBound.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
      ∀ y : Fin d → ℂ, (fibre J A y).Nonempty ∧ (fibre J A y).Finite ∧
        (fibre J A y).ncard ≤ projDegree J A

def DiscriminantCover.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
      ∃ P : MvPolynomial (Fin d) ℂ, P ≠ 0 ∧ ∀ y : Fin d → ℂ, eval y P ≠ 0 →
        (fibre J A y).Finite ∧ (fibre J A y).ncard = projDegree J A ∧
        ∀ x ∈ fibre J A y, ∃ (U : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
          (g : (Fin d → ℂ) → (Fin n → ℂ)), IsOpen U ∧ y ∈ U ∧ IsOpen V ∧ x ∈ V ∧
            DifferentiableOn ℂ g U ∧ g y = x ∧ (∀ w ∈ U, A.mulVec (g w) = w) ∧
            zeroSet J ∩ V = g '' U

def BadSetSmaller.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
      ∀ P : MvPolynomial (Fin d) ℂ, P ≠ 0 →
        zeroSet (J ⊔ Ideal.span {pullback A P}) = zeroSet J ∩ {x | eval (A.mulVec x) P = 0} ∧
        ∀ Q ∈ (J ⊔ Ideal.span {pullback A P}).minimalPrimes,
          ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) < d

attribute [local instance] MvPolynomial.gradedAlgebra in

def ConeScaling.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) →
    ∀ t : ℂ, t ≠ 0 → t • zeroSet J = zeroSet J

section Inhabitants

theorem line_isPrime : (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)).IsPrime := Ideal.isPrime_bot

theorem line_dim : ringKrullDim (MvPolynomial (Fin 1) ℂ ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ))) =
    (1 : ℕ) := by
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

theorem pullback_one : pullback (1 : Matrix (Fin 1) (Fin 1) ℂ) = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  simp [pullback, linPoly]

theorem line_isFiniteProjection :
    IsFiniteProjection (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  have hb : Function.Bijective (Ideal.Quotient.mkₐ ℂ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ))) :=
    (Ideal.Quotient.mk_bijective_iff_eq_bot _).mpr rfl
  have he : (projHom (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (1 : Matrix (Fin 1) (Fin 1) ℂ) :
      MvPolynomial (Fin 1) ℂ → _) = Ideal.Quotient.mkₐ ℂ _ := by
    rw [projHom, pullback_one, AlgHom.comp_id]
  refine ⟨?_, ?_⟩
  · rw [he]; exact hb.1
  · apply RingHom.Finite.of_surjective
    change Function.Surjective (projHom _ _ : MvPolynomial (Fin 1) ℂ → _)
    rw [he]; exact hb.2

def coneEq : MvPolynomial (Fin 3) ℂ := X 0 ^ 2 - X 1 * X 2

def coneIdeal : Ideal (MvPolynomial (Fin 3) ℂ) := Ideal.span {coneEq}

def coneProj : Matrix (Fin 2) (Fin 3) ℂ := !![0, 1, 0; 0, 0, 1]

theorem finSuccEquiv_coneEq :
    finSuccEquiv ℂ 2 coneEq = Polynomial.X ^ 2 - Polynomial.C (X 0 * X 1) := by
  have h1 : (X 1 : MvPolynomial (Fin 3) ℂ) = X (Fin.succ 0) := rfl
  have h2 : (X 2 : MvPolynomial (Fin 3) ℂ) = X (Fin.succ 1) := rfl
  rw [coneEq, h1, h2, map_sub, map_pow, map_mul, finSuccEquiv_X_zero, finSuccEquiv_X_succ,
    finSuccEquiv_X_succ, Polynomial.C_mul]

theorem coneEq_irreducible : Irreducible coneEq := by
  rw [← MulEquiv.irreducible_iff (finSuccEquiv ℂ 2).toMulEquiv]
  change Irreducible (finSuccEquiv ℂ 2 coneEq)
  rw [finSuccEquiv_coneEq]
  have hm : (Polynomial.X ^ 2 - Polynomial.C (X 0 * X 1 : MvPolynomial (Fin 2) ℂ)).Monic :=
    Polynomial.monic_X_pow_sub_C _ (by norm_num)
  have hd : (Polynomial.X ^ 2 - Polynomial.C (X 0 * X 1 : MvPolynomial (Fin 2) ℂ)).natDegree = 2 :=
    Polynomial.natDegree_X_pow_sub_C
  rw [hm.irreducible_iff_roots_eq_zero_of_degree_le_three (by rw [hd]) (by rw [hd]; norm_num),
    Multiset.eq_zero_iff_forall_notMem]
  intro r hr
  rw [Polynomial.mem_roots hm.ne_zero, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hr
  have hx : (X 0 * X 1 : MvPolynomial (Fin 2) ℂ) ≠ 0 := mul_ne_zero (X_ne_zero _) (X_ne_zero _)
  have r0 : r ≠ 0 := by
    rintro rfl
    exact hx (by rw [← hr]; simp)
  have h := congrArg (degreeOf 0) hr
  rw [degreeOf_pow_eq 0 r 2 r0, degreeOf_mul_eq (X_ne_zero _) (X_ne_zero _), degreeOf_X,
    degreeOf_X] at h
  simp at h

theorem coneEq_prime : Prime coneEq := coneEq_irreducible.prime

theorem coneEq_ne_zero : coneEq ≠ 0 := coneEq_prime.ne_zero

theorem cone_isPrime : coneIdeal.IsPrime :=
  (Ideal.span_singleton_prime coneEq_ne_zero).mpr coneEq_prime

theorem withBot_le_two_of_add_one_le (x : WithBot ℕ∞) (hx : x + 1 ≤ 3) : x ≤ 2 := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact absurd hx (by decide)
    | coe k =>
      have h1 : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ ((3 : ℕ) : WithBot ℕ∞) := by simpa using hx
      have h2 : k + 1 ≤ 3 := by exact_mod_cast h1
      have h3 : ((k : ℕ) : WithBot ℕ∞) ≤ ((2 : ℕ) : WithBot ℕ∞) := by
        exact_mod_cast (show k ≤ 2 by omega)
      simpa using h3

theorem X_zero_not_mem_coneIdeal : (X 0 : MvPolynomial (Fin 3) ℂ) ∉ coneIdeal := by
  intro h
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp h
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact X_ne_zero (0 : Fin 3) (by rw [← hq, zero_mul])
  have hhom : coneEq.IsHomogeneous 2 :=
    (isHomogeneous_X_pow (0 : Fin 3) 2).sub ((isHomogeneous_X ℂ (1 : Fin 3)).mul
      (isHomogeneous_X ℂ (2 : Fin 3)))
  have h := congrArg totalDegree hq
  rw [totalDegree_mul_of_isDomain hq0 coneEq_ne_zero, hhom.totalDegree coneEq_ne_zero,
    totalDegree_X] at h
  omega

theorem cone_dim :
    ringKrullDim (MvPolynomial (Fin 3) ℂ ⧸ coneIdeal) = (2 : ℕ) := by
  have hup : ringKrullDim (MvPolynomial (Fin 3) ℂ ⧸ coneIdeal) ≤ 2 := by
    apply withBot_le_two_of_add_one_le
    have h3 : ringKrullDim (MvPolynomial (Fin 3) ℂ) = 3 := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
      simp
    rw [← h3]
    exact ringKrullDim_quotient_succ_le_of_nonZeroDivisor
      (mem_nonZeroDivisors_of_ne_zero coneEq_ne_zero)

  let ψ1 : MvPolynomial (Fin 3) ℂ →ₐ[ℂ] MvPolynomial (Fin 1) ℂ := aeval ![0, 0, X 0]
  let ψ2 : MvPolynomial (Fin 3) ℂ →ₐ[ℂ] ℂ := aeval (fun _ => 0)
  have c2 : ψ2 = (aeval (fun _ => (0 : ℂ))).comp ψ1 := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [ψ1, ψ2]
  have l2 : RingHom.ker ψ1 ≤ RingHom.ker ψ2 := by
    intro p hp
    rw [RingHom.mem_ker] at hp ⊢
    rw [c2, AlgHom.comp_apply, hp, map_zero]
  have l1 : coneIdeal ≤ RingHom.ker ψ1 := by
    rw [coneIdeal, Ideal.span_le, Set.singleton_subset_iff]
    show ψ1 coneEq = 0
    simp [ψ1, coneEq]
  have : (RingHom.ker ψ1).IsPrime := RingHom.ker_isPrime _
  have : (RingHom.ker ψ2).IsPrime := RingHom.ker_isPrime _
  let p0 : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin 3) ℂ) (coneIdeal : Set _) :=
    ⟨⟨coneIdeal, cone_isPrime⟩, (show (coneIdeal : Set (MvPolynomial (Fin 3) ℂ)) ⊆ coneIdeal from subset_rfl)⟩
  let p1 : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin 3) ℂ) (coneIdeal : Set _) :=
    ⟨⟨RingHom.ker ψ1, inferInstance⟩, (show (coneIdeal : Set (MvPolynomial (Fin 3) ℂ)) ⊆ RingHom.ker ψ1 from l1)⟩
  let p2 : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin 3) ℂ) (coneIdeal : Set _) :=
    ⟨⟨RingHom.ker ψ2, inferInstance⟩, (show (coneIdeal : Set (MvPolynomial (Fin 3) ℂ)) ⊆ RingHom.ker ψ2 from l1.trans l2)⟩
  have h01 : p0 < p1 := by
    refine lt_of_le_not_ge (show coneIdeal ≤ RingHom.ker ψ1 from l1) fun h => ?_
    have hx : (X 0 : MvPolynomial (Fin 3) ℂ) ∈ RingHom.ker ψ1 := by
      rw [RingHom.mem_ker]; simp [ψ1]
    exact X_zero_not_mem_coneIdeal ((show RingHom.ker ψ1 ≤ coneIdeal from h) hx)
  have h12 : p1 < p2 := by
    refine lt_of_le_not_ge (show RingHom.ker ψ1 ≤ RingHom.ker ψ2 from l2) fun h => ?_
    have hx : (X 2 : MvPolynomial (Fin 3) ℂ) ∈ RingHom.ker ψ2 := by
      rw [RingHom.mem_ker]; simp [ψ2]
    have hx' := (show RingHom.ker ψ2 ≤ RingHom.ker ψ1 from h) hx
    rw [RingHom.mem_ker] at hx'
    simp [ψ1] at hx'
  let s : LTSeries (PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin 3) ℂ) (coneIdeal : Set _)) :=
    { length := 2
      toFun := ![p0, p1, p2]
      step := fun i => by fin_cases i; exacts [h01, h12] }
  have hlow : (2 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin 3) ℂ ⧸ coneIdeal) := by
    rw [ringKrullDim_quotient]
    exact Order.LTSeries.length_le_krullDim s
  rw [le_antisymm hup hlow]
  rfl

theorem pullback_coneProj (P : MvPolynomial (Fin 2) ℂ) :
    finSuccEquiv ℂ 2 (pullback coneProj P) = Polynomial.C P := by
  have h : ((finSuccEquiv ℂ 2).toAlgHom.comp (pullback coneProj) :
      MvPolynomial (Fin 2) ℂ →ₐ[ℂ] Polynomial (MvPolynomial (Fin 2) ℂ)) =
      (Algebra.ofId (MvPolynomial (Fin 2) ℂ) (Polynomial (MvPolynomial (Fin 2) ℂ))).restrictScalars ℂ := by
    apply MvPolynomial.algHom_ext
    intro i
    have h1 : (X 1 : MvPolynomial (Fin 3) ℂ) = X (Fin.succ 0) := rfl
    have h2 : (X 2 : MvPolynomial (Fin 3) ℂ) = X (Fin.succ 1) := rfl
    fin_cases i <;>
      simp [pullback, linPoly, coneProj, Fin.sum_univ_three, h1, h2, finSuccEquiv_X_succ]
  exact DFunLike.congr_fun h P

theorem projHom_cone_X (i : Fin 2) :
    projHom coneIdeal coneProj (X i) = Ideal.Quotient.mk coneIdeal (X i.succ) := by
  fin_cases i <;> simp [projHom, pullback, linPoly, coneProj, Fin.sum_univ_three]

theorem cone_isFiniteProjection : IsFiniteProjection coneIdeal coneProj := by
  set φ := (projHom coneIdeal coneProj).toRingHom with hφ
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro P hP
    have hmem : pullback coneProj P ∈ coneIdeal := Ideal.Quotient.eq_zero_iff_mem.mp hP
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp hmem
    have h := congrArg (finSuccEquiv ℂ 2) hq
    rw [map_mul, finSuccEquiv_coneEq, pullback_coneProj] at h
    by_contra hP0
    have hq0 : finSuccEquiv ℂ 2 q ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h
      exact hP0 (Polynomial.C_eq_zero.mp h.symm)
    have hd := congrArg Polynomial.natDegree h
    rw [Polynomial.natDegree_C, Polynomial.natDegree_mul hq0
      (Polynomial.monic_X_pow_sub_C _ (by norm_num)).ne_zero, Polynomial.natDegree_X_pow_sub_C] at hd
    omega
  · rw [RingHom.finite_iff_isIntegral_and_finiteType]
    refine ⟨?_, ?_⟩
    · intro x
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      induction p using MvPolynomial.induction_on with
      | C a =>
        have : Ideal.Quotient.mk coneIdeal (C a) = φ (C a) := by
          rw [hφ, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, projHom, AlgHom.comp_apply, pullback,
            aeval_C, Ideal.Quotient.mkₐ_eq_mk, MvPolynomial.algebraMap_eq]
        rw [this]
        exact RingHom.isIntegralElem_map φ
      | add p q hp hq =>
        rw [map_add]
        exact RingHom.IsIntegralElem.add φ hp hq
      | mul_X p i hp =>
        rw [map_mul]
        refine RingHom.IsIntegralElem.mul φ hp ?_
        fin_cases i
        · refine ⟨Polynomial.X ^ 2 - Polynomial.C (X 0 * X 1),
            Polynomial.monic_X_pow_sub_C _ (by norm_num), ?_⟩
          have e0 : φ (X 0) = Ideal.Quotient.mk coneIdeal (X 1) := projHom_cone_X 0
          have e1 : φ (X 1) = Ideal.Quotient.mk coneIdeal (X 2) := projHom_cone_X 1
          rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, map_mul, e0, e1,
            ← map_pow, ← map_mul, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.subset_span rfl
        · have e : Ideal.Quotient.mk coneIdeal (X 1) = φ (X 0) := (projHom_cone_X 0).symm
          simp only [Fin.mk_one]
          rw [e]; exact RingHom.isIntegralElem_map φ
        · have e : Ideal.Quotient.mk coneIdeal (X 2) = φ (X 1) := (projHom_cone_X 1).symm
          rw [show ((⟨2, by norm_num⟩ : Fin 3)) = 2 from rfl, e]
          exact RingHom.isIntegralElem_map φ
    · have hc : φ.comp (algebraMap ℂ (MvPolynomial (Fin 2) ℂ)) =
          algebraMap ℂ (MvPolynomial (Fin 3) ℂ ⧸ coneIdeal) :=
        (projHom coneIdeal coneProj).comp_algebraMap
      refine RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℂ (MvPolynomial (Fin 2) ℂ)) ?_
      rw [hc, RingHom.finiteType_algebraMap]
      infer_instance

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem cone_isHomogeneous : coneIdeal.IsHomogeneous (homogeneousSubmodule (Fin 3) ℂ) := by
  apply Ideal.homogeneous_span
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  refine ⟨2, (mem_homogeneousSubmodule 2 coneEq).mpr ?_⟩
  exact (isHomogeneous_X_pow (0 : Fin 3) 2).sub ((isHomogeneous_X ℂ (1 : Fin 3)).mul
    (isHomogeneous_X ℂ (2 : Fin 3)))

theorem coneProj_mem_orthoRows : coneProj ∈ orthoRows 2 3 := by
  show coneProj * coneProj.conjTranspose = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coneProj, Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply]

def coneMinPoly : Polynomial (MvPolynomial (Fin 2) ℂ) := Polynomial.X ^ 2 - Polynomial.C (X 0 * X 1)

def coneQuotEquiv : (MvPolynomial (Fin 3) ℂ ⧸ coneIdeal) ≃+* AdjoinRoot coneMinPoly :=
  Ideal.quotientEquiv coneIdeal (Ideal.span {coneMinPoly}) (finSuccEquiv ℂ 2).toRingEquiv (by
    rw [coneIdeal, Ideal.map_span]
    congr 1
    simp only [Set.image_singleton]
    congr 1
    exact (finSuccEquiv_coneEq).symm)

theorem cone_hyps : coneIdeal.IsPrime ∧ ringKrullDim (MvPolynomial (Fin 3) ℂ ⧸ coneIdeal) = (2 : ℕ) ∧
    IsFiniteProjection coneIdeal coneProj :=
  ⟨cone_isPrime, cone_dim, cone_isFiniteProjection⟩

theorem line_hyps : (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)).IsPrime ∧
    ringKrullDim (MvPolynomial (Fin 1) ℂ ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ))) = (1 : ℕ) ∧
    IsFiniteProjection (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (1 : Matrix (Fin 1) (Fin 1) ℂ) :=
  ⟨line_isPrime, line_dim, line_isFiniteProjection⟩

theorem GenericProjectionFinite.hypotheses_inhabited :
    (coneIdeal.IsPrime ∧ ringKrullDim (MvPolynomial (Fin 3) ℂ ⧸ coneIdeal) = (2 : ℕ)) ∧
      (orthoRows 2 3 ⊆ orthoRows 2 3 ∧ orthoRows 2 3 ⊆ closure (orthoRows 2 3) ∧
        coneProj ∈ orthoRows 2 3) ∧
      (1 : Matrix (Fin 3) (Fin 3) ℂ) ∈ Matrix.unitaryGroup (Fin 3) ℂ :=
  ⟨⟨cone_isPrime, cone_dim⟩, ⟨subset_rfl, subset_closure, coneProj_mem_orthoRows⟩, one_mem _⟩

theorem FibreBound.hypotheses_inhabited :
    (coneIdeal.IsPrime ∧ ringKrullDim (MvPolynomial (Fin 3) ℂ ⧸ coneIdeal) = (2 : ℕ) ∧
      IsFiniteProjection coneIdeal coneProj) ∧
    ((⊥ : Ideal (MvPolynomial (Fin 1) ℂ)).IsPrime ∧
      ringKrullDim (MvPolynomial (Fin 1) ℂ ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ))) = (1 : ℕ) ∧
      IsFiniteProjection (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (1 : Matrix (Fin 1) (Fin 1) ℂ)) :=
  ⟨cone_hyps, line_hyps⟩

theorem DiscriminantCover.hypotheses_inhabited :
    (coneIdeal.IsPrime ∧ ringKrullDim (MvPolynomial (Fin 3) ℂ ⧸ coneIdeal) = (2 : ℕ) ∧
      IsFiniteProjection coneIdeal coneProj) ∧
    ((⊥ : Ideal (MvPolynomial (Fin 1) ℂ)).IsPrime ∧
      ringKrullDim (MvPolynomial (Fin 1) ℂ ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ))) = (1 : ℕ) ∧
      IsFiniteProjection (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (1 : Matrix (Fin 1) (Fin 1) ℂ)) :=
  ⟨cone_hyps, line_hyps⟩

theorem BadSetSmaller.hypotheses_inhabited :
    (coneIdeal.IsPrime ∧ ringKrullDim (MvPolynomial (Fin 3) ℂ ⧸ coneIdeal) = (2 : ℕ) ∧
      IsFiniteProjection coneIdeal coneProj) ∧ (X 0 : MvPolynomial (Fin 2) ℂ) ≠ 0 :=
  ⟨cone_hyps, X_ne_zero _⟩

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem ConeScaling.hypotheses_inhabited :
    coneIdeal.IsHomogeneous (homogeneousSubmodule (Fin 3) ℂ) ∧ (2 : ℂ) ≠ 0 :=
  ⟨cone_isHomogeneous, two_ne_zero⟩

end Inhabitants

end

end GroundTheory.Heights₂.Heights.ComplexSets
