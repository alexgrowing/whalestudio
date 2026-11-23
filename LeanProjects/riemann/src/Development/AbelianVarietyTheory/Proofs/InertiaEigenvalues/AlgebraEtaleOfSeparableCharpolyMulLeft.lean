import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerBasisOfCharpolySeparable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEquivalenceFiniteEtaleBaseChangeResidueField

open Polynomial

namespace GlobalTheory

theorem etale_of_separable_charpoly_mulLeft (E A : Type) [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] (g : A) (h : (LinearMap.mulLeft E g).charpoly.Separable) :
    Algebra.Etale E A := by
  have hd := GlobalTheory.UnitLemma.charpoly_dvd_minpoly_of_separable (LinearMap.mulLeft E g) h
  have h2 : minpoly E (LinearMap.mulLeft E g) = minpoly E g :=
    minpoly.algHom_eq (Algebra.lmul E A) (Algebra.lmul_injective) g
  have hint : IsIntegral E g := Algebra.IsIntegral.isIntegral g
  have hm : (minpoly E g).Monic := minpoly.monic hint
  have hd' : minpoly E g ∣ (LinearMap.mulLeft E g).charpoly := by
    rw [← h2]; exact LinearMap.minpoly_dvd_charpoly _
  rw [h2] at hd
  have heq : minpoly E g = (LinearMap.mulLeft E g).charpoly :=
    eq_of_monic_of_associated hm (LinearMap.charpoly_monic _) (associated_of_dvd_dvd hd' hd)
  have hsep : (minpoly E g).Separable := heq ▸ h
  have hdeg : (minpoly E g).natDegree = Module.finrank E A := by
    rw [heq, LinearMap.charpoly_natDegree]
  haveI : Module.Finite E (AdjoinRoot (minpoly E g)) := hm.finite_adjoinRoot
  let φ : AdjoinRoot (minpoly E g) →ₐ[E] A := AdjoinRoot.liftAlgHom (minpoly E g) (Algebra.ofId E A) g (minpoly.aeval E g)
  have hli : LinearIndependent E fun i : Fin (minpoly E g).natDegree => g ^ (i : ℕ) :=
    linearIndependent_pow g
  let b := basisOfLinearIndependentOfCardEqFinrank' _ hli (by simp [hdeg])
  have hsurj : Function.Surjective φ.toLinearMap := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨AdjoinRoot.root (minpoly E g) ^ (i : ℕ), ?_⟩
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank', AlgHom.toLinearMap_apply, map_pow]
    congr 1
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  have hfr : Module.finrank E (AdjoinRoot (minpoly E g)) = Module.finrank E A := by
    rw [(AdjoinRoot.powerBasis' hm).finrank]; simpa using hdeg
  have hinj : Function.Injective φ.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).2 hsurj
  let e : AdjoinRoot (minpoly E g) ≃ₐ[E] A := AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have hu : IsUnit (AdjoinRoot.mk (minpoly E g) (minpoly E g).derivative) := by
    obtain ⟨a, c, hac⟩ := hsep
    have := congrArg (AdjoinRoot.mk (minpoly E g)) hac
    rw [map_add, map_mul, map_mul, AdjoinRoot.mk_self, mul_zero, zero_add, map_one] at this
    exact isUnit_iff_exists_inv.2 ⟨_, by rw [mul_comm]; exact this⟩
  have := GlobalTheory.etale_adjoinRoot_of_isUnit_derivative hm hu
  exact Algebra.Etale.of_equiv e

end GlobalTheory
