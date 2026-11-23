import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IrrelevantLeMapScaleGraded
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EqOfIsLieComb
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeSchemeOver

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw GlobalTheory.WeightScale GlobalTheory.QuadraticAction

noncomputable section

namespace GlobalTheory.CMCurve

variable {R : Type} [CommRing R]

variable (R) in

def gaussianCurve : WeierstrassCurve R := ⟨0, 0, 0, -1, 0⟩

theorem gaussianCurve_Δ : (gaussianCurve R).Δ = 2 ^ 6 := by
  simp [gaussianCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num

theorem isElliptic_gaussianCurve (h2 : IsUnit (2 : R)) : (gaussianCurve R).IsElliptic :=
  ⟨gaussianCurve_Δ (R := R) ▸ h2.pow 6⟩

section Gaussian

variable {i : R} (hi : i ^ 2 = -1)
include hi

theorem neg_mul_self_eq_one : -i * i = 1 := by linear_combination -hi

theorem curve_gaussianCurve : curve (-i) (gaussianCurve R) = gaussianCurve R := by
  ext <;> simp only [curve, gaussianCurve, mul_zero]
  linear_combination (1 - i ^ 2) * hi

def gaussianAut : schemeOver (gaussianCurve R) ⟶ schemeOver (gaussianCurve R) :=
  scaleOver _ (IsUnit.of_mul_eq_one _ (neg_mul_self_eq_one hi)) (curve_gaussianCurve hi)

variable [(gaussianCurve R).IsElliptic]

instance isMonHom_gaussianAut : IsMonHom (gaussianAut hi) := isMonHom_scaleOver ..

theorem gaussianAut_sq : gaussianAut hi ≫ gaussianAut hi = ι[schemeOver (gaussianCurve R)] := by
  refine over_hom_ext_ptOver _ fun A _ _ P hP => ?_
  rw [← Hom.inv_def, ptOver_inv, gaussianAut, ← Category.assoc, ptOver_scaleOver]
  refine (ptOver_scaleOver _ _ _ _ _).trans (ptOver_congr _ ?_)
  rw [triple_triple, ← map_mul, show -i * -i = -1 by linear_combination hi]
  ext j
  fin_cases j <;> simp [triple, WeierstrassCurve.Projective.neg, WeierstrassCurve.Projective.negY,
    gaussianCurve, WeierstrassCurve.baseChange]
  ring

def gaussianAct : OAct GaussianInt (schemeOver (gaussianCurve R)) :=
  zsqrtdAct (gaussianAut hi) (by
    rw [gaussianAut_sq, comb, zpow_zero, _root_.mul_one, zpow_neg_one, Hom.inv_def,
      Category.id_comp])

end Gaussian

abbrev EisensteinInt : Type := QuadraticAlgebra ℤ (-1) (-1)

variable (R) in

def eisensteinCurve : WeierstrassCurve R := ⟨0, 0, 1, 0, 0⟩

theorem eisensteinCurve_Δ : (eisensteinCurve R).Δ = -3 ^ 3 := by
  simp [eisensteinCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num

theorem isElliptic_eisensteinCurve (h3 : IsUnit (3 : R)) : (eisensteinCurve R).IsElliptic :=
  ⟨eisensteinCurve_Δ (R := R) ▸ (h3.pow 3).neg⟩

section Eisenstein

variable {w : R} (hw : w ^ 2 + w + 1 = 0)
include hw

theorem sq_mul_self_eq_one : w ^ 2 * w = 1 := by linear_combination (w - 1) * hw

theorem curve_eisensteinCurve : curve (w ^ 2) (eisensteinCurve R) = eisensteinCurve R := by
  ext <;> simp only [curve, eisensteinCurve, mul_zero]
  linear_combination (w ^ 3 + 1) * sq_mul_self_eq_one hw

theorem triple_sq {A : Type} [CommRing A] (ρ : R →+* A) (P : Fin 3 → A) :
    triple (ρ (w ^ 2)) P = ![ρ w * P 0, P 1, P 2] := by
  have h : ρ w ^ 2 * ρ w = 1 := by rw [← map_pow, ← map_mul, sq_mul_self_eq_one hw, map_one]
  rw [triple, map_pow]
  congr 1
  · linear_combination (ρ w * P 0) * h
  · congr 1
    linear_combination ((ρ w ^ 3 + 1) * P 1) * h

def eisensteinAut : schemeOver (eisensteinCurve R) ⟶ schemeOver (eisensteinCurve R) :=
  scaleOver _ (IsUnit.of_mul_eq_one _ (sq_mul_self_eq_one hw)) (curve_eisensteinCurve hw)

variable [(eisensteinCurve R).IsElliptic]

instance isMonHom_eisensteinAut : IsMonHom (eisensteinAut hw) := isMonHom_scaleOver ..

theorem eisensteinAut_sq :
    (eisensteinAut hw ≫ eisensteinAut hw) * eisensteinAut hw * 𝟙 _ = 1 := by
  rw [_root_.mul_assoc, mul_eq_one_iff_inv_eq, _root_.mul_comm]
  refine over_hom_ext_ptOver _ fun A _ _ P hP => ?_
  rw [GrpObj.comp_inv, MonObj.comp_mul, Category.comp_id, eisensteinAut, ← Category.assoc,
    ptOver_scaleOver]
  refine ((congrArg (·⁻¹) (ptOver_scaleOver _ _ _ _ _)).trans (ptOver_inv _ _)).trans
    (ptOver_mul_ptOver _ _ _ _ ?_).symm
  have e : (eisensteinCurve R).baseChange A = ⟨0, 0, 1, 0, 0⟩ := by
    ext <;> simp [eisensteinCurve, WeierstrassCurve.baseChange]
  have hA : algebraMap R A w ^ 2 + algebraMap R A w + 1 = 0 := by
    simpa using congrArg (algebraMap R A) hw
  have hE := hP.equation
  rw [e, ← WeierstrassCurve.Projective.fin3_def P] at hE
  have := isSumTriple_cubeRoot hA hE
  rw [WeierstrassCurve.Projective.fin3_def] at this
  rw [e, triple_sq hw, triple_sq hw]
  convert this using 1
  ext j
  fin_cases j <;> simp [WeierstrassCurve.Projective.neg, WeierstrassCurve.Projective.negY]
  ring

def eisensteinAct : OAct EisensteinInt (schemeOver (eisensteinCurve R)) :=
  quadAct (eisensteinAut hw) (by
    rw [comb, zpow_neg_one, zpow_neg_one, ← mul_inv_rev, eq_inv_iff_mul_eq_one,
      ← _root_.mul_assoc, eisensteinAut_sq])

end Eisenstein

example : ∃ i : Localization.Away (2 : GaussianInt), i ^ 2 = -1 ∧
    IsUnit (2 : Localization.Away (2 : GaussianInt)) ∧
    CharZero (Localization.Away (2 : GaussianInt)) := by
  refine ⟨algebraMap GaussianInt _ ⟨0, 1⟩, ?_, ?_, ?_⟩
  · rw [← map_pow, show (⟨0, 1⟩ : GaussianInt) ^ 2 = -1 by decide, map_neg, map_one]
  · simpa only [map_ofNat] using IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away (2 : GaussianInt)) (2 : GaussianInt)
  · exact charZero_of_injective_algebraMap (R := GaussianInt) (IsLocalization.injective _
      (powers_le_nonZeroDivisors_of_noZeroDivisors (two_ne_zero (α := GaussianInt))))

end GlobalTheory.CMCurve
