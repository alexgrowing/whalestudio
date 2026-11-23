import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import ReciprocityTheory.DualLattices.FischerSelfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe

noncomputable section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

namespace GlobalTheory.CompactHowe.PolyTensor

open MvPolynomial

variable {ι σ : Type} [Fintype ι]

def prodRename [DecidableEq ι] :
    MultilinearMap ℂ (fun _ : ι => MvPolynomial σ ℂ) (MvPolynomial (ι × σ) ℂ) :=
  (MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial (ι × σ) ℂ)).compLinearMap
    fun i => (rename (Prod.mk i) : MvPolynomial σ ℂ →ₐ[ℂ] _).toLinearMap

theorem prodRename_apply [DecidableEq ι] (P : ι → MvPolynomial σ ℂ) :
    prodRename P = ∏ i, rename (Prod.mk i) (P i) := by
  simp [prodRename]

theorem sum_mapDomain_apply (a : ι → σ →₀ ℕ) (j : ι) (s : σ) :
    (∑ i, Finsupp.mapDomain (Prod.mk i) (a i)) (j, s) = a j s := by
  classical
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single j]
  · exact Finsupp.mapDomain_apply (Prod.mk_right_injective j) _ _
  · intro i _ hi
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨t, ht⟩
    exact hi (congrArg Prod.fst ht)
  · simp

theorem prod_rename_monomial (a : ι → σ →₀ ℕ) :
    (∏ i, rename (Prod.mk i) (monomial (a i) (1 : ℂ)) : MvPolynomial (ι × σ) ℂ)
      = monomial (∑ i, Finsupp.mapDomain (Prod.mk i) (a i)) 1 := by
  simp only [rename_monomial]
  rw [monomial_sum_one]

def res (α : ι × σ →₀ ℕ) (i : ι) : σ →₀ ℕ :=
  Finsupp.comapDomain (Prod.mk i) α (Prod.mk_right_injective i).injOn

theorem res_sum (a : ι → σ →₀ ℕ) : res (∑ i, Finsupp.mapDomain (Prod.mk i) (a i)) = a := by
  funext j
  ext s
  exact sum_mapDomain_apply a j s

theorem sum_res (α : ι × σ →₀ ℕ) : ∑ i, Finsupp.mapDomain (Prod.mk i) (res α i) = α := by
  ext ⟨j, s⟩
  exact sum_mapDomain_apply (res α) j s

variable {A B : ι → Type} [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
  [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)]

def tens (I : ∀ i, MvPolynomial σ ℂ →ₗ[ℂ] A i →ₗ[ℂ] B i) :
    MvPolynomial (ι × σ) ℂ →ₗ[ℂ] (⨂[ℂ] i, A i) →ₗ[ℂ] ⨂[ℂ] i, B i :=
  (basisMonomials (ι × σ) ℂ).constr ℂ fun α => PiTensorProduct.map fun i => I i (monomial (res α i) 1)

theorem tens_prod (I : ∀ i, MvPolynomial σ ℂ →ₗ[ℂ] A i →ₗ[ℂ] B i) (P : ι → MvPolynomial σ ℂ) :
    tens I (∏ i, rename (Prod.mk i) (P i)) = PiTensorProduct.map fun i => I i (P i) := by
  classical
  have key : (tens I).compMultilinearMap prodRename
      = (PiTensorProduct.mapMultilinear ℂ A B).compLinearMap I := by
    refine Module.Basis.ext_multilinear (fun _ => basisMonomials σ ℂ) fun a => ?_
    simp only [LinearMap.compMultilinearMap_apply, prodRename_apply, coe_basisMonomials,
      MultilinearMap.compLinearMap_apply, PiTensorProduct.mapMultilinear_apply]
    rw [prod_rename_monomial]
    have := (basisMonomials (ι × σ) ℂ).constr_basis ℂ
      (fun α => PiTensorProduct.map fun i => I i (monomial (res α i) 1))
      (∑ i, Finsupp.mapDomain (Prod.mk i) (a i))
    rw [res_sum, coe_basisMonomials] at this
    exact this
  have := congrArg (fun f => f P) key
  simpa [prodRename_apply] using this

omit [Fintype ι] in
theorem tprod_ne_zero [Finite ι] (v : ∀ i, B i) (hv : ∀ i, v i ≠ 0) :
    PiTensorProduct.tprod ℂ v ≠ 0 := by
  classical
  have := Fintype.ofFinite ι
  choose l hl using fun i => Module.Projective.exists_dual_eq_one ℂ (hv i)
  intro h0
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap l)) h0
  simp [hl] at this

omit [Fintype ι] in
theorem substF_rename {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (i : ι) (P : MvPolynomial (Fin N × Fin n) ℂ) :
    substF h g (rename (Prod.mk i) P) = rename (Prod.mk i) (subst2 (h i) (g i) P) := by
  have key : (substF h g).comp (rename (Prod.mk i)) = (rename (Prod.mk i)).comp (subst2 (h i) (g i)) := by
    refine algHom_ext fun p => ?_
    simp only [AlgHom.comp_apply, rename_X, substF_X, subst2_X, map_sum, map_mul, rename_C]
  exact congrArg (fun f => f P) key

theorem exists_tensor : ∀ (ι : Type) [Fintype ι] (N n : ℕ) (A B : ι → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)] (I : ∀ i, MvPolynomial (Fin N × Fin n) ℂ →ₗ[ℂ] A i →ₗ[ℂ] B i), (∀ i, I i ≠ 0) → ∃ It : MvPolynomial (ι × Fin N × Fin n) ℂ →ₗ[ℂ] (⨂[ℂ] i, A i) →ₗ[ℂ] ⨂[ℂ] i, B i, It ≠ 0 ∧ ∀ (c : ι → ℂ) (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ) (a : ∀ i, A i →ₗ[ℂ] A i) (b : ∀ i, B i →ₗ[ℂ] B i), (∀ i P v, I i (c i • subst2 (h i) (g i) P) (a i v) = b i (I i P v)) → ∀ P x, It ((∏ i, c i) • substF h g P) (PiTensorProduct.map a x) = PiTensorProduct.map b (It P x) := by
  intro ι _ N n A B _ _ _ _ I hI
  classical
  refine ⟨tens I, ?_, ?_⟩
  · have hex : ∀ i, ∃ P v, I i P v ≠ 0 := by
      intro i
      by_contra hc
      push Not at hc
      exact hI i (LinearMap.ext fun P => LinearMap.ext fun v => hc P v)
    choose P v hPv using hex
    intro h0
    have h1 := tens_prod I P
    rw [h0] at h1
    have h2 := congrArg (fun f => f (PiTensorProduct.tprod ℂ v)) h1
    simp only [LinearMap.zero_apply, PiTensorProduct.map_tprod] at h2
    exact tprod_ne_zero _ hPv h2.symm
  · intro c h g a b hab
    have key : ∀ Q : ι → MvPolynomial (Fin N × Fin n) ℂ,
        (tens I ((∏ i, c i) • substF h g (∏ i, rename (Prod.mk i) (Q i)))) ∘ₗ PiTensorProduct.map a
          = PiTensorProduct.map b ∘ₗ tens I (∏ i, rename (Prod.mk i) (Q i)) := by
      intro Q
      have e : (∏ i, c i) • substF h g (∏ i, rename (Prod.mk i) (Q i))
          = ∏ i, rename (Prod.mk i) (c i • subst2 (h i) (g i) (Q i)) := by
        simp only [map_prod, substF_rename, map_smul, Finset.prod_smul]
      rw [e, tens_prod, tens_prod, ← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
      congr 1
      funext i
      exact LinearMap.ext fun v => hab i (Q i) v
    intro P x
    induction P using MvPolynomial.induction_on' with
    | monomial α r =>
      have e : (monomial α r : MvPolynomial (ι × Fin N × Fin n) ℂ)
          = r • ∏ i, rename (Prod.mk i) (monomial (res α i) (1 : ℂ)) := by
        rw [prod_rename_monomial, sum_res, smul_monomial, smul_eq_mul, mul_one]
      have := congrArg (fun f => f x) (key fun i => monomial (res α i) 1)
      simp only [LinearMap.comp_apply] at this
      rw [e, map_smul (substF h g), smul_comm, map_smul (tens I), LinearMap.smul_apply, this, map_smul (tens I),
        LinearMap.smul_apply, map_smul]
    | add p q hp hq =>
      rw [map_add, smul_add, map_add, LinearMap.add_apply, hp, hq, map_add (tens I),
        LinearMap.add_apply, map_add]

end GlobalTheory.CompactHowe.PolyTensor

end
