import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitFiniteResidueCharZeroAvoidingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfMemAdjoinInv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEven

theorem dvd_of_forall_fintrait : ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A] [Algebra.FiniteType ℤ A] (a f : A), f ≠ 0 → (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) → ∀ t : A →+* V, t f ≠ 0 → t f ∣ t a) → f ∣ a := by
  intro A _ _ _ _ _ a f hf H
  rcases eq_or_ne a 0 with rfl | ha
  · exact dvd_zero f
  let K := FractionRing A
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have haK : algebraMap A K a ≠ 0 := (map_ne_zero_iff _ hinj).2 ha
  have hfK : algebraMap A K f ≠ 0 := (map_ne_zero_iff _ hinj).2 hf
  let y : K := algebraMap A K f / algebraMap A K a
  have hy : y ≠ 0 := div_ne_zero hfK haK
  let S := Algebra.adjoin A {y}
  let z : S := ⟨y, Algebra.self_mem_adjoin_singleton A y⟩
  by_cases hz : IsUnit z
  · obtain ⟨w, hw⟩ := hz.exists_right_inv
    have hw' : (w : K) = y⁻¹ := eq_inv_of_mul_eq_one_right (congrArg Subtype.val hw)
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
      (GlobalTheory.ValCrit.isIntegral_of_mem_adjoin_inv y hy (hw' ▸ w.2))
    refine ⟨r, hinj ?_⟩
    rw [map_mul, hr, inv_div, mul_div_cancel₀ _ hfK]
  · exfalso
    have hft : Algebra.FiniteType A S := Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton y)
    haveI hftZ : @Algebra.FiniteType ℤ S _ _ (Ring.toIntAlgebra S) := by
      have h2 := Algebra.FiniteType.trans (R := ℤ) (S := A) (A := S) inferInstance hft
      convert h2 using 1 <;> first | rfl | exact Subsingleton.elim _ _
    have hinjS : Function.Injective (algebraMap A S) := fun b c h => hinj (congrArg Subtype.val h)
    have : CharZero S := charZero_of_injective_algebraMap hinjS
    obtain ⟨n, hn, hzn⟩ := exists_max_ideal_of_mem_nonunits hz
    have hfS : algebraMap A S f ≠ 0 := (map_ne_zero_iff _ hinjS).2 hf
    obtain ⟨V, _, _, _, _, t, hc, hfin, htf, hcomap⟩ := GlobalTheory.T.exists_trait_finiteResidue_charZero_avoiding S n (algebraMap A S f) hn hfS
    have hdiv := H V hc hfin (t.comp (algebraMap A S)) htf
    simp only [RingHom.comp_apply] at hdiv
    have hfa : algebraMap A S f = z * algebraMap A S a := by
      apply Subtype.ext
      show algebraMap A K f = (algebraMap A K f / algebraMap A K a) * algebraMap A K a
      rw [div_mul_cancel₀ _ haK]
    have htz : t z ∈ IsLocalRing.maximalIdeal V := by
      rw [← Ideal.mem_comap, hcomap]; exact hzn
    rw [hfa, map_mul] at hdiv htf
    obtain ⟨c, hc'⟩ := hdiv
    have hta : t (algebraMap A S a) ≠ 0 := right_ne_zero_of_mul htf
    have h1 : t z * c = 1 := by
      apply mul_left_cancel₀ hta
      calc t (algebraMap A S a) * (t z * c) = t z * t (algebraMap A S a) * c := by ring
        _ = t (algebraMap A S a) := hc'.symm
        _ = t (algebraMap A S a) * 1 := (_root_.mul_one _).symm
    exact (IsLocalRing.mem_maximalIdeal _).1 htz ⟨⟨t z, c, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

end GlobalTheory.KeyEven
