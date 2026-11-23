import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsObj
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CapZcMemOfE

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem UpperTheory.ConvolutionTheory.Dp.infZc_prod {n : ℕ} {m : Multiset ℂ} (hm : m.card = n) (u : ℂ) :
    (m.map fun x => u + x).prod = u ^ n + ∑ i : Fin n, u ^ (n - (i + 1)) * m.esymm (i + 1) := by
  have h := congrArg (Polynomial.eval u) (Multiset.prod_X_add_C_eq_sum_esymm m)
  rw [Polynomial.eval_multiset_prod, Multiset.map_map] at h
  simp only [Function.comp_def, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow, hm] at h
  rw [h, Finset.sum_range_succ', add_comm, ← Fin.sum_univ_eq_sum_range
    (fun i => m.esymm (i + 1) * u ^ (n - (i + 1))) n]
  congr 1
  · simp [Multiset.esymm]
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem UpperTheory.ConvolutionTheory.Dp.infZc_coeff {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ} (v : Fin n → M)
    (h : ∀ u : ℂ, ∑ i : Fin n, u ^ (n - (i + 1)) • v i = 0) (i : Fin n) : v i = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro f
  have hp : (∑ j : Fin n, Polynomial.monomial (n - (j + 1)) (f (v j)) : Polynomial ℂ) = 0 := by
    apply Polynomial.funext
    intro u
    have := congrArg f (h u)
    simp only [map_sum, map_smul, map_zero, smul_eq_mul] at this
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.eval_zero]
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have := congrArg (fun p => Polynomial.coeff p (n - (i + 1))) hp
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at this
  rw [Finset.sum_eq_single i] at this
  · simpa using this
  · intro j _ hj
    rw [if_neg]
    intro e
    apply hj
    have := j.2
    have := i.2
    exact Fin.ext (by omega)
  · simp

theorem UpperTheory.ConvolutionTheory.Dp.infZc :
    UpperTheory.ConvolutionTheory.Dp.InfZc := by
  intro E _ _ _ n π τ m
  have hc := (UpperTheory.ConvolutionTheory.Dp.capZc E n τ).2
  have key : ∀ (u : ℂ) (φ : GlobalTheory.CuspRep.Sm E n), GlobalTheory.CuspRep.cap τ u φ =
      u ^ n • φ + ∑ i : Fin n, u ^ (n - (i + 1)) • Cm.uC E n (UpperTheory.ConvolutionTheory.zc τ i) φ := fun u φ => by
    rw [← Cm.uC_capC, hc]
    simp only [map_add, map_smul, map_one, map_sum, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.sum_apply, Module.End.one_apply]
  change (m.card = n ∧ ∀ u : ℂ, ∀ φ ∈ π.V, GlobalTheory.CuspRep.cap τ u φ = (m.map fun x => u + x).prod • φ) ↔ _
  refine and_congr_right fun hm => ⟨fun h i φ hφ => ?_, fun h u φ hφ => ?_⟩
  · rw [← sub_eq_zero]
    refine infZc_coeff (fun i : Fin n => Cm.uC E n (UpperTheory.ConvolutionTheory.zc τ i) φ - m.esymm (i + 1) • φ) (fun u => ?_) i
    have := h u φ hφ
    rw [key, infZc_prod hm, add_smul, add_right_inj, Finset.sum_smul] at this
    simp only [smul_sub, Finset.sum_sub_distrib, this, smul_smul, sub_self]
  · rw [key, infZc_prod hm, add_smul, Finset.sum_smul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [h i φ hφ, smul_smul]
