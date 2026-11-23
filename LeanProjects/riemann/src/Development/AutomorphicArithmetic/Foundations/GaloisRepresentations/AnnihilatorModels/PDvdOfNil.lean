import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PhiKOfNil

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.dvdOfNil_of :
    DvdOfNil := by
  classical
  intro K W _ _ _ _ _ M s u hu hnil
  obtain ⟨n, hn⟩ := hnil
  have hroot : ∀ r ∈ (LinearMap.charpoly M).roots, r ∈ s := by
    intro r hr
    have hev : M.HasEigenvalue r := (Module.End.hasEigenvalue_iff_isRoot_charpoly M r).2
      ((Polynomial.mem_roots (LinearMap.charpoly_monic M).ne_zero).1 hr)
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have h1 := Module.End.aeval_apply_of_hasEigenvector
      (p := (Polynomial.C u * rootPol s) ^ n) hv
    rw [map_pow, hn, LinearMap.zero_apply] at h1
    have h2 : ((Polynomial.C u * rootPol s) ^ n).eval r = 0 :=
      (smul_eq_zero.1 h1.symm).resolve_right hv.2
    rw [Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_C] at h2
    have h3 : (rootPol s).eval r = 0 :=
      (mul_eq_zero.1 (pow_eq_zero_iff'.1 h2).1).resolve_left hu
    unfold rootPol at h3
    rw [Polynomial.eval_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.map_map] at h3
    obtain ⟨a, ha, hra⟩ := Multiset.mem_map.1 h3
    simp only [Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at hra
    rw [sub_eq_zero.1 hra]
    exact ha
  set m := (LinearMap.charpoly M).roots.card with hm
  refine ⟨m, ?_⟩
  have hcp : ((LinearMap.charpoly M).roots.map fun a => Polynomial.X - Polynomial.C a).prod
      = LinearMap.charpoly M :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (LinearMap.charpoly_monic M)
      IsAlgClosed.card_roots_eq_natDegree
  have hpow : rootPol s ^ m = ((m • s).map fun a => Polynomial.X - Polynomial.C a).prod := by
    unfold rootPol
    rw [Multiset.map_nsmul, Multiset.prod_nsmul]
  rw [← hcp, hpow]
  apply Multiset.prod_dvd_prod_of_le
  apply Multiset.map_le_map
  rw [Multiset.le_iff_count]
  intro a
  rw [Multiset.count_nsmul]
  by_cases ha : a ∈ (LinearMap.charpoly M).roots
  · have hs : 1 ≤ s.count a := Multiset.one_le_count_iff_mem.2 (hroot a ha)
    calc (LinearMap.charpoly M).roots.count a ≤ m := Multiset.count_le_card _ _
      _ = m * 1 := (mul_one m).symm
      _ ≤ m * s.count a := Nat.mul_le_mul_left m hs
  · rw [Multiset.count_eq_zero.2 ha]
    exact Nat.zero_le _
