import Mathlib

noncomputable section

namespace GroundTheory.Automorphic

namespace Spherical

open AddMonoidAlgebra

variable {n : ℕ}

variable (n) in

abbrev LaurentRing : Type := AddMonoidAlgebra ℂ (Fin n → ℤ)

abbrev monomial (l : Fin n → ℤ) : LaurentRing n := single l 1

def monomialChar (l : Fin n → ℤ) : (Fin n → ℂˣ) →* ℂ where
  toFun w := ∏ i, ((w i ^ l i : ℂˣ) : ℂ)
  map_one' := by simp
  map_mul' w w' := by
    simp only [Pi.mul_apply, mul_zpow, Units.val_mul, Finset.prod_mul_distrib]

theorem monomialChar_apply (l : Fin n → ℤ) (w : Fin n → ℂˣ) :
    monomialChar l w = ∏ i, ((w i ^ l i : ℂˣ) : ℂ) := rfl

@[simp]
theorem monomialChar_zero (w : Fin n → ℂˣ) : monomialChar 0 w = 1 := by
  simp [monomialChar_apply]

theorem monomialChar_add (l l' : Fin n → ℤ) (w : Fin n → ℂˣ) :
    monomialChar (l + l') w = monomialChar l w * monomialChar l' w := by
  simp only [monomialChar_apply, Pi.add_apply, zpow_add, Units.val_mul, Finset.prod_mul_distrib]

def pointHom (w : Fin n → ℂˣ) : Multiplicative (Fin n → ℤ) →* ℂ where
  toFun l := monomialChar (Multiplicative.toAdd l) w
  map_one' := by simp [monomialChar_apply]
  map_mul' l l' := by
    simp only [toAdd_mul, monomialChar_apply, Pi.add_apply, zpow_add, Units.val_mul,
      Finset.prod_mul_distrib]

def evalAt (w : Fin n → ℂˣ) : LaurentRing n →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (Fin n → ℤ) (pointHom w)

theorem evalAt_single (w : Fin n → ℂˣ) (l : Fin n → ℤ) (c : ℂ) :
    evalAt w (single l c) = c * monomialChar l w := by
  rw [evalAt, AddMonoidAlgebra.lift_single, smul_eq_mul]
  rfl

theorem evalAt_apply (w : Fin n → ℂˣ) (p : LaurentRing n) :
    evalAt w p = p.coeff.sum fun l c => c * monomialChar l w := by
  rw [evalAt, AddMonoidAlgebra.lift_apply]
  rfl

theorem monomialChar_injective : Function.Injective (monomialChar : (Fin n → ℤ) → _) := by
  intro l l' h
  funext i
  have h2 := DFunLike.congr_fun h (Pi.mulSingle i (Units.mk0 (2 : ℂ) two_ne_zero))
  simp only [monomialChar_apply] at h2
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle_eq_of_ne hj])
      (by simp), Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle_eq_of_ne hj])
      (by simp)] at h2
  simp only [Pi.mulSingle_eq_same, Units.val_zpow_eq_zpow_val, Units.val_mk0] at h2
  have hn : ‖(2 : ℂ) ^ l i‖ = ‖(2 : ℂ) ^ l' i‖ := by rw [h2]
  rw [norm_zpow, norm_zpow, Complex.norm_two] at hn
  exact zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num) hn

theorem eq_zero_of_forall_evalAt {p : LaurentRing n} (h : ∀ w, evalAt w p = 0) : p = 0 := by
  have hli : LinearIndependent ℂ (fun l : Fin n → ℤ => ((monomialChar l : (Fin n → ℂˣ) →* ℂ) :
      (Fin n → ℂˣ) → ℂ)) :=
    (linearIndependent_monoidHom (Fin n → ℂˣ) ℂ).comp _ monomialChar_injective
  have hz : Finsupp.linearCombination ℂ (fun l : Fin n → ℤ =>
      ((monomialChar l : (Fin n → ℂˣ) →* ℂ) : (Fin n → ℂˣ) → ℂ)) p.coeff =
      Finsupp.linearCombination ℂ (fun l : Fin n → ℤ =>
      ((monomialChar l : (Fin n → ℂˣ) →* ℂ) : (Fin n → ℂˣ) → ℂ)) 0 := by
    rw [map_zero]
    funext w
    rw [Finsupp.linearCombination_apply, Pi.zero_apply, ← h w, evalAt_apply, Finsupp.sum,
      Finsupp.sum, Finset.sum_apply]
    rfl
  exact AddMonoidAlgebra.coeff_eq_zero.1 (hli hz)

theorem eq_of_forall_evalAt {p q : LaurentRing n} (h : ∀ w, evalAt w p = evalAt w q) : p = q :=
  sub_eq_zero.1 (eq_zero_of_forall_evalAt fun w => by rw [map_sub, h, sub_self])

theorem exists_eq_evalAt (ψ : LaurentRing n →ₐ[ℂ] ℂ) : ∃ w : Fin n → ℂˣ, ψ = evalAt w := by
  set M : Multiplicative (Fin n → ℤ) →* ℂ := (AddMonoidAlgebra.lift ℂ ℂ (Fin n → ℤ)).symm ψ
  let U : Multiplicative (Fin n → ℤ) →* ℂˣ := M.toHomUnits
  set w : Fin n → ℂˣ := fun i => U (Multiplicative.ofAdd (Pi.single i 1))
  refine ⟨w, ?_⟩
  have hl : ∀ l : Multiplicative (Fin n → ℤ),
      l = ∏ i, (Multiplicative.ofAdd (Pi.single i 1 : Fin n → ℤ)) ^ (Multiplicative.toAdd l i) := by
    intro l
    apply Multiplicative.toAdd.injective
    rw [toAdd_prod]
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hM : M = pointHom w := by
    refine MonoidHom.ext fun l => ?_
    have h1 : M l = (U l : ℂ) := rfl
    rw [h1]
    conv_lhs => rw [hl l]
    rw [map_prod, Units.coe_prod]
    simp only [map_zpow]
    rfl
  rw [evalAt, ← hM, Equiv.apply_symm_apply]

instance : Algebra.FiniteType ℂ (LaurentRing n) := by
  infer_instance

theorem exists_ker_evalAt_comp_eq {A : Type*} [CommRing A] [Algebra ℂ A]
    (Φ : A →ₐ[ℂ] LaurentRing n) (hΦ : Function.Injective Φ)
    [hint : Algebra.IsIntegral Φ.range (LaurentRing n)] (I : Ideal A) [hI : I.IsMaximal] :
    ∃ w : Fin n → ℂˣ, RingHom.ker ((evalAt w).comp Φ) = I := by
  let e : A ≃ₐ[ℂ] Φ.range := AlgEquiv.ofInjective Φ hΦ
  let P : Ideal Φ.range := I.comap (e.symm : Φ.range →+* A)
  haveI : P.IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
  have hP : RingHom.ker (algebraMap Φ.range (LaurentRing n)) ≤ P := by
    intro x hx
    have : x = 0 := Subtype.ext hx
    rw [this]
    exact P.zero_mem
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral P hP
  letI := Ideal.Quotient.field Q
  haveI : Algebra.FiniteType ℂ (LaurentRing n ⧸ Q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ Q)
      (Ideal.Quotient.mkₐ_surjective ℂ Q)
  haveI := finite_of_finite_type_of_isJacobsonRing ℂ (LaurentRing n ⧸ Q)
  have hbij : Function.Bijective (Algebra.ofId ℂ (LaurentRing n ⧸ Q)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := LaurentRing n ⧸ Q)
  let e' : ℂ ≃ₐ[ℂ] LaurentRing n ⧸ Q := AlgEquiv.ofBijective (Algebra.ofId ℂ (LaurentRing n ⧸ Q)) hbij
  let ψ : LaurentRing n →ₐ[ℂ] ℂ := e'.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ Q)
  have hker : ∀ p, ψ p = 0 ↔ p ∈ Q := by
    intro p
    simp only [ψ, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_algHom,
      Ideal.Quotient.mkₐ_eq_mk]
    rw [AlgEquiv.symm_apply_eq, map_zero, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨w, hw⟩ := exists_eq_evalAt ψ
  refine ⟨w, Ideal.ext fun a => ?_⟩
  rw [RingHom.mem_ker, AlgHom.comp_apply, ← hw, hker]
  have h1 : Φ a = algebraMap Φ.range (LaurentRing n) (e a) := rfl
  rw [h1, ← Ideal.mem_comap, hQP]
  change e.symm (e a) ∈ I ↔ a ∈ I
  rw [AlgEquiv.symm_apply_apply]

theorem isIntegral_of_forall (A : Subalgebra ℂ (LaurentRing n))
    (h₁ : ∀ i, IsIntegral A (monomial (Pi.single i 1 : Fin n → ℤ)))
    (h₂ : ∀ i, IsIntegral A (monomial (Pi.single i (-1) : Fin n → ℤ))) :
    Algebra.IsIntegral A (LaurentRing n) := by
  let S : Subalgebra ℂ (LaurentRing n) := (integralClosure A (LaurentRing n)).restrictScalars ℂ
  have hmono : ∀ l : Fin n → ℤ, monomial l ∈ S := by
    intro l
    have hl : monomial l = ∏ i, monomial (Pi.single i (l i) : Fin n → ℤ) := by
      rw [AddMonoidAlgebra.prod_single]
      simp only [Finset.prod_const_one]
      congr 1
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hl]
    refine Subalgebra.prod_mem _ fun i _ => ?_
    rcases le_or_gt 0 (l i) with h | h
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le h
      have : monomial (Pi.single i (l i) : Fin n → ℤ) = monomial (Pi.single i 1) ^ k := by
        rw [AddMonoidAlgebra.single_pow, one_pow, hk, ← Pi.single_smul]
        simp
      rw [this]
      exact Subalgebra.pow_mem _ (h₁ i) k
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 h.le)
      have : monomial (Pi.single i (l i) : Fin n → ℤ) = monomial (Pi.single i (-1)) ^ k := by
        rw [AddMonoidAlgebra.single_pow, one_pow, ← Pi.single_smul]
        congr 2
        simp only [nsmul_eq_mul, mul_neg, mul_one]
        omega
      rw [this]
      exact Subalgebra.pow_mem _ (h₂ i) k
  refine ⟨fun p => ?_⟩
  have : p ∈ S := by
    rw [← AddMonoidAlgebra.sum_coeff_single p]
    refine Subalgebra.sum_mem _ fun l _ => ?_
    have : (single l (p.coeff l) : LaurentRing n) = p.coeff l • monomial l := by
      rw [AddMonoidAlgebra.smul_single', mul_one]
    rw [this]
    exact Subalgebra.smul_mem _ (hmono l) _
  exact this

end Spherical

end GroundTheory.Automorphic
