import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamGApply
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VariableMatrixDetPolyPowMulMemDualWeylStatement
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameRead.ExPhi

theorem res_eq {ι : Type} {n : ℕ} {lam : ι → DomWeight n} {lamW : ι → ℕ → ℕ} {c : ι → ℤ} (h : Shift lam lamW c) (τ : ι) :
    res n (lamW τ) = fun a => (lam τ).natW a + lamW τ (n - 1) := by
  funext a
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) a.2
  have h1 := h τ a
  have h2 := h τ ⟨n - 1, by omega⟩
  have h3 : (lam τ).w ⟨n - 1, by omega⟩ ≤ (lam τ).w a := (lam τ).anti (by
    rw [Fin.le_def]; have := a.2; simp only; omega)
  simp only [res, DomWeight.natW, DomWeight.detShift, dif_pos hn] at h2 ⊢
  omega

theorem liftPol_mem {K C : Type} [Field K] [Field C] (e0 : K →+* C) {ι : Type} {n : ℕ} {lam : ι → DomWeight n}
    {lamW : ι → ℕ → ℕ} {c : ι → ℤ} (h : Shift lam lamW c) (τ : ι) (x : MvPolynomial (Fin n × Fin n) K)
    (hx : x ∈ nablaSq K n (lam τ)) : liftPol e0 (lamW τ (n - 1)) x ∈ dualWeyl C n n (res n (lamW τ)) := by
  rw [res_eq h τ]
  exact GlobalTheory.T.variableMatrixDetPoly_pow_mul_mem_dualWeyl C n _ _ _ (dualWeylMap K C e0 n n _ x hx)

theorem ssB_span (K : Type) [Field K] {n : ℕ} (ν : Fin n → ℕ) :
    Submodule.span K (Set.range (ssB K ν)) = dualWeyl K n n ν :=
  (Formalism.GradedWeylDivisibility.sSBasis K n n ν).choose_spec.1.2.1

theorem ssB_mem (K : Type) [Field K] {n : ℕ} (l : DomWeight n) (j : ssIdx n n l.natW) : ssB K l.natW j ∈ nablaSq K n l := by
  unfold nablaSq
  rw [← ssB_span]
  exact Submodule.subset_span ⟨j, rfl⟩

theorem detPol_ne_zero (R : Type) [CommRing R] [Nontrivial R] (n : ℕ) : detPol R n ≠ 0 := by
  intro h
  have h1 := congrArg (MvPolynomial.eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) R) v.1 v.2) h
  rw [detPol, RingHom.map_det, map_zero] at h1
  have h2 : (MvPolynomial.eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) R) v.1 v.2).mapMatrix
      (Matrix.of fun a s => X (a, s)) = (1 : Matrix (Fin n) (Fin n) R) := by
    ext a s; simp
  rw [h2, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem linInd_map {F K σ ι : Type} [Field F] [Field K] (e : F →+* K) {v : ι → MvPolynomial σ F}
    (hv : LinearIndependent F v) : LinearIndependent K (fun i => MvPolynomial.map e (v i)) := by
  classical
  letI : Algebra F K := e.toAlgebra
  rw [linearIndependent_iff'] at hv ⊢
  intro s c hsum i hi
  let B := Module.Free.chooseBasis F K
  apply B.ext_elem
  intro j
  have key : ∑ i ∈ s, (B.repr (c i) j) • v i = 0 := by
    ext m
    have h1 := congrArg (coeff m) hsum
    simp only [coeff_sum, coeff_smul, coeff_map, smul_eq_mul, coeff_zero] at h1 ⊢
    have h2 := congrArg (fun x => B.repr x j) h1
    simp only [map_sum, map_zero, Finsupp.finset_sum_apply, Finsupp.coe_zero, Pi.zero_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h3 : c i * e (coeff m (v i)) = coeff m (v i) • c i := by
      rw [Algebra.smul_def, mul_comm]; rfl
    rw [h3, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  have := hv s (fun i => B.repr (c i) j) key i hi
  simpa using this

def semiConstr {K C V M I : Type} [Field K] [Field C] [AddCommGroup V] [Module K V] [AddCommGroup M] [Module C M] [Fintype I]
    (e : K →+* C) (b : Module.Basis I K V) (t : I → M) : V →ₛₗ[e] M where
  toFun v := ∑ i, e (b.repr v i) • t i
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a v := by simp [Finset.smul_sum, mul_smul]

theorem semiConstr_basis {K C V M I : Type} [Field K] [Field C] [AddCommGroup V] [Module K V] [AddCommGroup M] [Module C M]
    [Fintype I] (e : K →+* C) (b : Module.Basis I K V) (t : I → M) (i : I) : semiConstr e b t (b i) = t i := by
  classical
  change ∑ j, e (b.repr (b i) j) • t j = t i
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Finsupp.single_apply, hj.symm]
  · simp

def mulMap (C : Type) [Field C] {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ) :
    NablaT C n lamW →ₗ[C] Pol C ι n :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra C ι (Pol C ι n)).compLinearMap fun τ =>
    (blockEmb C τ).toLinearMap ∘ₗ (dualWeyl C n n (res n (lamW τ))).subtype)

theorem mulMap_tprod (C : Type) [Field C] {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ)
    (y : ∀ τ, dualWeyl C n n (res n (lamW τ))) :
    mulMap C n lamW (PiTensorProduct.tprod C y) = ten fun τ => (y τ : MvPolynomial (Fin n × Fin n) C) := by
  simp [mulMap, ten]

theorem ten_liftPol {K C : Type} [Field K] [Field C] (e0 : K →+* C) {ι : Type} [Fintype ι] {n : ℕ} (k : ι → ℕ)
    (x : ι → MvPolynomial (Fin n × Fin n) K) :
    (ten fun τ => liftPol e0 (k τ) (x τ)) = (ten fun τ => detPol C n ^ k τ) * MvPolynomial.map e0 (ten x) := by
  simp only [ten, liftPol, map_mul, map_prod, Finset.prod_mul_distrib, blockEmb, map_rename]

theorem ten_det_ne_zero (C : Type) [Field C] {ι : Type} [Fintype ι] {n : ℕ} (k : ι → ℕ) :
    (ten fun τ => detPol C n ^ k τ) ≠ 0 := by
  unfold ten
  refine Finset.prod_ne_zero_iff.2 fun τ _ => ?_
  intro h
  have hinj : Function.Injective (blockEmb C (k := n) (n := n) τ) :=
    rename_injective _ fun a b hab => (Prod.mk.inj hab).2
  exact pow_ne_zero _ (detPol_ne_zero C n) (hinj (h.trans (map_zero _).symm))

theorem exists_phi (K C : Type) [Field K] [Field C] (e0 : K →+* C) (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ)
    (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (h : Shift lam lamW c) :
    ∃ Φ : VV K lam →ₛₗ[e0] NablaT C n lamW, IsPhi e0 lam lamW Φ ∧ LinearIndependent C fun i => Φ (bVV K lam i) := by
  classical
  let u : ∀ τ, ssIdx n n (lam τ).natW → dualWeyl C n n (res n (lamW τ)) := fun τ j =>
    ⟨liftPol e0 (lamW τ (n - 1)) (ssB K (lam τ).natW j), liftPol_mem e0 h τ _ (ssB_mem K _ j)⟩
  let t : VVIdx lam → NablaT C n lamW := fun i => PiTensorProduct.tprod C fun τ => u τ (i τ)
  refine ⟨semiConstr e0 (bVV K lam) t, ?_, ?_⟩
  · intro x v hx hv
    haveI : ∀ τ, Fintype (ssIdx n n (lam τ).natW) := fun τ => (Formalism.GradedWeylDivisibility.sSIdxFinite n n _).fintype
    have hex : ∀ τ, ∃ a : ssIdx n n (lam τ).natW → K, ∑ j, a j • ssB K (lam τ).natW j = x τ := fun τ => by
      have h1 := hx τ
      unfold nablaSq at h1
      rw [← ssB_span] at h1
      exact (Submodule.mem_span_range_iff_exists_fun K).1 h1
    choose a ha using hex
    have hv' : v = ∑ i : VVIdx lam, (∏ τ, a τ (i τ)) • bVV K lam i := by
      apply Subtype.ext
      rw [hv]
      simp only [Submodule.coe_sum, Submodule.coe_smul, bVV_coe, bVVfun, ten, ← ha, map_sum, map_smul]
      rw [Finset.prod_univ_sum]
      simp only [Finset.prod_smul]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext i; simp
    refine ⟨fun τ => ∑ j, e0 (a τ j) • u τ j, fun τ => ?_, ?_⟩
    · simp only [Submodule.coe_sum, Submodule.coe_smul, u, liftPol, ← ha, map_sum, Finset.mul_sum, smul_eq_C_mul, map_mul, map_C]
      refine Finset.sum_congr rfl fun j _ => by ring
    · rw [MultilinearMap.map_sum, hv', map_sum]
      simp only [LinearMap.map_smulₛₗ, semiConstr_basis, MultilinearMap.map_smul_univ, map_prod]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext i; simp
  · simp only [semiConstr_basis]
    refine LinearIndependent.of_comp (mulMap C n lamW) ?_
    have h1 := linInd_map e0 (bVVfun_spec K lam).1
    have h2 := h1.map' (LinearMap.mulLeft C (ten fun τ => detPol C n ^ lamW τ (n - 1)))
      (LinearMap.ker_eq_bot.2 (mul_right_injective₀ (ten_det_ne_zero C _)))
    have h3 : (mulMap C n lamW ∘ t) = (LinearMap.mulLeft C (ten fun τ => detPol C n ^ lamW τ (n - 1))) ∘
        fun i => MvPolynomial.map e0 (bVVfun K lam i) := by
      funext i
      simp only [Function.comp, t, mulMap_tprod, u, ten_liftPol, LinearMap.mulLeft_apply, bVVfun]
    exact h3 ▸ h2

end GlobalTheory.FrameRead.ExPhi
