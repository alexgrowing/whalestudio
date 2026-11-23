import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch

open GlobalTheory.UnitLemma Matrix MeasureTheory

namespace GlobalTheory.UnitLemma

open Polynomial

open Matrix MeasureTheory in
open Polynomial in

theorem _root_.GlobalTheory.UnitLemma.charpoly_dvd_minpoly_of_separable {E V : Type} [Field E] [AddCommGroup V] [Module E V]
    [Module.Finite E V] (f : Module.End E V) (h : (LinearMap.charpoly f).Separable) :
    LinearMap.charpoly f ∣ minpoly E f := by
  set L := AlgebraicClosure E
  have hinj : Function.Injective (algebraMap E L) := (algebraMap E L).injective
  rw [← map_dvd_map (algebraMap E L) hinj (LinearMap.charpoly_monic f)]
  have hm0 : (minpoly E f).map (algebraMap E L) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero (Algebra.IsIntegral.isIntegral f))
  have hroot : ∀ r ∈ ((LinearMap.charpoly f).map (algebraMap E L)).roots,
      r ∈ ((minpoly E f).map (algebraMap E L)).roots := by
    intro r hr
    rw [mem_roots hm0]
    rw [mem_roots (Polynomial.map_ne_zero (LinearMap.charpoly_monic f).ne_zero),
      ← LinearMap.charpoly_baseChange, ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hr
    obtain ⟨v, hv⟩ := hr.exists_hasEigenvector
    have hzero : aeval (f.baseChange L) ((minpoly E f).map (algebraMap E L)) = 0 := by
      rw [aeval_map_algebraMap]
      have hφ := Polynomial.aeval_algHom_apply (Module.End.baseChangeHom E L V) f (minpoly E f)
      rw [minpoly.aeval, map_zero] at hφ
      exact hφ
    have hv' :=
      Module.End.aeval_apply_of_hasEigenvector (p := (minpoly E f).map (algebraMap E L)) hv
    rw [hzero, LinearMap.zero_apply, eq_comm, smul_eq_zero] at hv'
    exact hv'.resolve_right hv.2
  have hsplit := IsAlgClosed.splits ((LinearMap.charpoly f).map (algebraMap E L))
  rw [hsplit.eq_prod_roots_of_monic ((LinearMap.charpoly_monic f).map _),
    Multiset.prod_X_sub_C_dvd_iff_le_roots hm0, Multiset.le_iff_subset (nodup_roots h.map)]
  exact hroot

open Matrix MeasureTheory in
open Polynomial in

theorem _root_.GlobalTheory.UnitLemma.exists_basis_pow_of_separable : ∀ (K : _root_.GlobalTheory.UnitLemma.UQ)
    (B : _root_.GlobalTheory.UnitLemma.InvAlg K), B.P.Separable →
    ∃ e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E
      B.A, ∀ i, e i = B.g ^ (i : ℕ) := by
  intro K B hsep
  set g := B.g
  have hmin : minpoly K.E (LinearMap.mulLeft K.E g) = minpoly K.E g :=
    minpoly.algHom_eq (Algebra.lmul K.E B.A)
      (fun x y hxy => by simpa using congrArg (fun φ => φ 1) hxy) g
  have hdvd := _root_.GlobalTheory.UnitLemma.charpoly_dvd_minpoly_of_separable _ hsep
  rw [hmin] at hdvd
  have hdeg : (minpoly K.E g).natDegree =
      Module.finrank K.E B.A := by
    apply le_antisymm (minpoly.natDegree_le g)
    rw [← LinearMap.charpoly_natDegree (LinearMap.mulLeft K.E g)]
    exact natDegree_le_of_dvd hdvd (minpoly.ne_zero (Algebra.IsIntegral.isIntegral g))
  have hli : LinearIndependent K.E
      (fun i : Fin (Module.finrank K.E B.A) => g ^ (i : ℕ)) :=
    (linearIndependent_pow g).comp (Fin.cast hdeg.symm) (Fin.cast_injective _)
  exact ⟨basisOfLinearIndependentOfCardEqFinrank' _ hli (Fintype.card_fin _),
    fun i => by rw [coe_basisOfLinearIndependentOfCardEqFinrank']⟩

end GlobalTheory.UnitLemma
