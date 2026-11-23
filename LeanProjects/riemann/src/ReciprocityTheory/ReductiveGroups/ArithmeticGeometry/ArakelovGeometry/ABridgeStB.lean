import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsBergDensity
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Jacobson.Ring

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial TensorProduct

theorem isReduced_tensor_finite (Ω E : Type*) [Field Ω] [CharZero Ω] [Field E] [Algebra ℚ E]
    [FiniteDimensional ℚ E] : IsReduced (E ⊗[ℚ] Ω) := by
  haveI : Algebra.FormallyUnramified ℚ E := Algebra.FormallyUnramified.of_isSeparable ℚ E
  haveI : IsReduced (Ω ⊗[ℚ] E) := Algebra.FormallyUnramified.isReduced_of_field Ω (Ω ⊗[ℚ] E)
  exact isReduced_of_injective (Algebra.TensorProduct.comm ℚ E Ω).toRingHom
    (Algebra.TensorProduct.comm ℚ E Ω).injective

theorem eq_zero_of_sum_tmul {Ω E : Type*} [Field Ω] [CharZero Ω] [Field E] [Algebra ℚ E] {r : ℕ}
    {s : Fin r → Ω} (hs : LinearIndependent ℚ s) {e : Fin r → E}
    (h : ∑ k, e k ⊗ₜ[ℚ] s k = 0) : e = 0 := by
  classical
  let W := Submodule.span ℚ (Set.range s)
  let 𝒞 : Module.Basis (Fin r) ℚ W := Module.Basis.span hs
  have hinj : Function.Injective (LinearMap.lTensor E W.subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap W.subtype Subtype.val_injective
  have h0 : (∑ k, e k ⊗ₜ[ℚ] 𝒞 k : E ⊗[ℚ] W) = 0 := by
    apply hinj
    rw [map_sum, map_zero]
    have hc : ∀ k, ((𝒞 k : W) : Ω) = s k := fun k => by
      show ((Module.Basis.span hs k : W) : Ω) = s k
      rw [Module.Basis.span_apply]
    simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply, hc]
    exact h
  have hb := TensorProduct.sum_tmul_basis_right_eq_zero 𝒞 (Finsupp.equivFunOnFinite.symm e) (by
    rw [Finsupp.sum_fintype _ _ (by intros; simp)]
    simpa using h0)
  funext k
  have hk := congrArg (fun b => b k) hb
  simpa using hk

theorem nilp_coeff_eq_zero {Ω : Type} [Field Ω] [CharZero Ω] {r : ℕ} {s : Fin r → Ω}
    (hs : LinearIndependent ℚ s) {c : Fin r → ℂ}
    (h : IsNilpotent (∑ k, c k ⊗ₜ[ℚ] s k : ℂ ⊗[ℚ] Ω)) : c = 0 := by
  classical
  let A : Subalgebra ℚ ℂ := Algebra.adjoin ℚ ((Finset.univ.image c : Finset ℂ) : Set ℂ)
  haveI : Algebra.FiniteType ℚ A := (Subalgebra.fg_iff_finiteType A).1 (Subalgebra.fg_adjoin_finset _)
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℚ) (B := A)
  have hcA : ∀ k, c k ∈ A := fun k => Algebra.subset_adjoin (by simp)
  let cA : Fin r → A := fun k => ⟨c k, hcA k⟩
  let tA : A ⊗[ℚ] Ω := ∑ k, cA k ⊗ₜ[ℚ] s k
  let ι : A ⊗[ℚ] Ω →ₐ[ℚ] ℂ ⊗[ℚ] Ω := Algebra.TensorProduct.map A.val (AlgHom.id ℚ Ω)
  have hι : Function.Injective ι := by
    have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := Ω) (A.val.toLinearMap)
      Subtype.val_injective
    have heq : ∀ x, ι x = LinearMap.rTensor Ω A.val.toLinearMap x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [ι, Algebra.TensorProduct.map_tmul]
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    intro x y hxy
    apply hinj
    rw [← heq, ← heq, hxy]
  have hιt : ι tA = ∑ k, c k ⊗ₜ[ℚ] s k := by
    simp [tA, ι, map_sum, Algebra.TensorProduct.map_tmul, cA]
  have hnA : IsNilpotent tA := by
    obtain ⟨m, hm⟩ := h
    refine ⟨m, hι ?_⟩
    rw [map_pow, hιt, hm, map_zero]
  have key : ∀ (E : Type) [Field E] [Algebra ℚ E] [FiniteDimensional ℚ E] (φ : A →ₐ[ℚ] E),
      ∀ k, φ (cA k) = 0 := by
    intro E _ _ _ φ
    let π : A ⊗[ℚ] Ω →ₐ[ℚ] E ⊗[ℚ] Ω := Algebra.TensorProduct.map φ (AlgHom.id ℚ Ω)
    haveI : IsReduced (E ⊗[ℚ] Ω) := isReduced_tensor_finite Ω E
    have h0 : π tA = 0 := (hnA.map π).eq_zero
    have h1 : ∑ k, φ (cA k) ⊗ₜ[ℚ] s k = 0 := by
      rw [← h0]
      simp [tA, π, map_sum, Algebra.TensorProduct.map_tmul]
    exact congrFun (eq_zero_of_sum_tmul hs h1)
  have hmax : ∀ M : Ideal A, M.IsMaximal → ∀ k, cA k ∈ M := by
    intro M hM k
    letI hF : Field (A ⧸ M) := Ideal.Quotient.field M
    haveI : Algebra.FiniteType ℚ (A ⧸ M) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ M) Ideal.Quotient.mk_surjective
    haveI : Module.Finite ℚ (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing ℚ (A ⧸ M)
    exact Ideal.Quotient.eq_zero_iff_mem.1 (key (A ⧸ M) (Ideal.Quotient.mkₐ ℚ M) k)
  have hjac : (⊥ : Ideal A).jacobson = ⊥ := IsJacobsonRing.out inferInstance Ideal.bot_prime.isRadical
  funext k
  have hk : cA k ∈ (⊥ : Ideal A).jacobson := Ideal.mem_sInf.2 (fun J hJ => hmax J hJ.2 k)
  rw [hjac] at hk
  have h0 : cA k = 0 := (Submodule.mem_bot _).1 hk
  exact congrArg Subtype.val h0

section Poly

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

theorem aeval_eq_zero_of_mem_coordIdeal {x : J → Ω} {f : MvPolynomial J ℤ}
    (hf : f ∈ coordIdeal ℤ x) : aeval x f = 0 := by
  have h0 : (aeval fun i => Polynomial.C (x i) * Polynomial.X : MvPolynomial J ℤ →ₐ[ℤ] Polynomial Ω) f = 0 :=
    RingHom.mem_ker.1 hf
  have h1 := MvPolynomial.comp_aeval_apply (fun i => Polynomial.C (x i) * Polynomial.X)
    ((Polynomial.aeval (1 : Ω)).restrictScalars ℤ) f
  rw [h0, map_zero] at h1
  simpa using h1.symm

def evalT (x : J → Ω) : MvPolynomial J ℂ →ₐ[ℂ] ℂ ⊗[ℚ] Ω :=
  aeval fun j => (1 : ℂ) ⊗ₜ[ℚ] x j

theorem evalT_map_rat (x : J → Ω) (b : MvPolynomial J ℚ) :
    evalT x (map (algebraMap ℚ ℂ) b) = (1 : ℂ) ⊗ₜ[ℚ] aeval x b := by
  unfold evalT
  rw [MvPolynomial.aeval_map_algebraMap]
  have h := MvPolynomial.comp_aeval_apply x (Algebra.TensorProduct.includeRight : Ω →ₐ[ℚ] ℂ ⊗[ℚ] Ω) b
  simpa [Algebra.TensorProduct.includeRight_apply] using h.symm

theorem evalT_map_int (x : J → Ω) (f : MvPolynomial J ℤ) :
    evalT x (map (Int.castRingHom ℂ) f) = (1 : ℂ) ⊗ₜ[ℚ] aeval x f := by
  unfold evalT
  rw [← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap]
  have h := MvPolynomial.comp_aeval_apply x
    ((Algebra.TensorProduct.includeRight : Ω →ₐ[ℚ] ℂ ⊗[ℚ] Ω).restrictScalars ℤ) f
  simpa [Algebra.TensorProduct.includeRight_apply] using h.symm

theorem coeff_eq_zero_of_vanish {x : J → Ω} {r : ℕ} {b : Fin r → MvPolynomial J ℚ}
    (hs : LinearIndependent ℚ fun k => aeval x (b k)) {c : Fin r → ℂ}
    (h : ∀ z : J → ℂ, (∀ f ∈ coordIdeal ℤ x, eval z (map (Int.castRingHom ℂ) f) = 0) →
      ∑ k, c k * secFun (b k) z = 0) : c = 0 := by
  classical
  set I : Ideal (MvPolynomial J ℂ) := Ideal.map (MvPolynomial.map (Int.castRingHom ℂ)) (coordIdeal ℤ x) with hI
  set P : MvPolynomial J ℂ := ∑ k, MvPolynomial.C (c k) * MvPolynomial.map (algebraMap ℚ ℂ) (b k) with hP
  have hPmem : P ∈ MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ I) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro z hz
    rw [MvPolynomial.mem_zeroLocus_iff] at hz
    have hz' : ∀ f ∈ coordIdeal ℤ x, eval z (map (Int.castRingHom ℂ) f) = 0 := by
      intro f hf
      have hf' := hz _ (Ideal.mem_map_of_mem _ hf)
      exact hf'
    have hsum := h z hz'
    change eval z P = 0
    rw [hP, map_sum]
    simpa [secFun] using hsum
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hPmem
  obtain ⟨n, hn⟩ := hPmem
  have hker : I ≤ RingHom.ker (evalT x : MvPolynomial J ℂ →+* ℂ ⊗[ℚ] Ω) := by
    rw [hI, Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change evalT x (map (Int.castRingHom ℂ) f) = 0
    rw [evalT_map_int, aeval_eq_zero_of_mem_coordIdeal hf, TensorProduct.tmul_zero]
  have hnil : IsNilpotent (evalT x P) := ⟨n, by
    rw [← map_pow]
    exact hker hn⟩
  have hev : evalT x P = ∑ k, c k ⊗ₜ[ℚ] aeval x (b k) := by
    rw [hP, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, evalT_map_rat, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    simp
  rw [hev] at hnil
  exact nilp_coeff_eq_zero hs hnil

end Poly

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
