import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntCastSmulIsogenyDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveIffPtMapSurjectiveStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem pt_comp_id_pow {K : Type} [Field K] (A : AbVar K) (x : A.Pt) (n : ℕ) :
    x ≫ (𝟙 A.X) ^ n = x ^ n := by
  induction n with
  | zero => simp [MonObj.comp_one]
  | succ k ih => rw [pow_succ, MonObj.comp_mul, ih, Category.comp_id, pow_succ]

theorem pt_divisible : ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ), n ≠ 0 → ∀ x : A.Pt, ∃ y : A.Pt, y ^ n = x := by
  intro K _ A n hn x
  have hz : ((n : ℤ)) ≠ 0 := by exact_mod_cast hn
  have hiso := (GlobalTheory.T.abelianVariety_intCast_smul_isogeny_degree K A (n : ℤ) hz).1
  have hs : Function.Surjective (ptMap ((n : ℤ) • 𝟙 A)) := (GlobalTheory.T.abVar_surjective_iff_ptMap_surjective K A A _).1 hiso.2
  obtain ⟨y, hy⟩ := hs x
  refine ⟨y, ?_⟩
  rw [← hy, ptMap_apply, natCast_zsmul, nsmul_hom, id_hom, pt_comp_id_pow]

end GlobalTheory.AV.AbVar
