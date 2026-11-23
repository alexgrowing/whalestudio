import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldMirabolic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaSeriesUnfoldMirabolic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

noncomputable section

namespace GlobalTheory.UnfoldRows

open Matrix

variable {E : Type} [Field E] [NumberField E]

omit [NumberField E] in
theorem single_last_vecMul {m : ℕ} {R : Type} [CommRing R] (M : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    (Pi.single (Fin.last m) 1 : Fin (m + 1) → R) ᵥ* M = M (Fin.last m) := by
  funext j
  simp [Matrix.vecMul, dotProduct, Pi.single_apply]

theorem algebraMap_comp_single {m : ℕ} :
    (algebraMap E (Ad E) ∘ (Pi.single (Fin.last m) 1 : Fin (m + 1) → E)) = Pi.single (Fin.last m) 1 := by
  funext j
  by_cases h : j = Fin.last m
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem lastRow_eq {m : ℕ} (g : GA E (m + 1)) :
    GlobalTheory.ZEul.lastRow g = Matrix.vecMul (algebraMap E (Ad E) ∘ (Pi.single (Fin.last m) 1 : Fin (m + 1) → E)) g.val := by
  rw [algebraMap_comp_single, single_last_vecMul]
  rfl

theorem det_posM_eq_one {R : Type} [CommRing R] {a : ℕ} {ι : Type} [Fintype ι] {p : ι → Fin a × Fin a}
    (hp : ∀ t, (p t).1 < (p t).2) (x : ι → R) : (1 + posM p x).det = 1 := by
  have hz : ∀ i j : Fin a, j ≤ i → posM p x i j = 0 := by
    intro i j hij
    simp only [posM, Matrix.sum_apply, Matrix.single_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg]
    rintro ⟨rfl, rfl, -⟩
    exact absurd (hp t) (not_lt.2 hij)
  have hT : (1 + posM p x).IsUpperTriangular := by
    intro i j hij
    have hne : i ≠ j := ne_of_gt hij
    rw [Matrix.add_apply, Matrix.one_apply_ne hne, hz i j (le_of_lt hij), add_zero]
  rw [Matrix.det_of_isUpperTriangular hT]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Matrix.add_apply, Matrix.one_apply_eq, hz i i le_rfl, add_zero]

theorem detAbs_of_det_one {a : ℕ} (u : GA E a) (hu : (u : Matrix (Fin a) (Fin a) (Ad E)).det = 1) :
    GlobalTheory.RSnm.detAbs u = 1 := by
  have h : GeneralLinearGroup.det u = 1 := Units.ext (by rw [GeneralLinearGroup.val_det_apply, hu, Units.val_one])
  simp [GlobalTheory.RSnm.detAbs, h]

theorem rows_main : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ),
    (∀ (γ : GL (Fin (m + 1)) E) (g : GA E (m + 1)), GlobalTheory.ZEul.lastRow (ratGL E (m + 1) γ * g) =
      Matrix.vecMul (algebraMap E (Ad E) ∘ Matrix.vecMul (Pi.single (Fin.last m) 1 : Fin (m + 1) → E) γ.val) g.val) ∧
    (∀ g : GA E (m + 1), GlobalTheory.ZEul.lastRow g = Matrix.vecMul (algebraMap E (Ad E) ∘ (Pi.single (Fin.last m) 1 : Fin (m + 1) → E)) g.val) ∧
    (∀ γ : GL (Fin (m + 1)) E, IsMir m γ → Matrix.vecMul (Pi.single (Fin.last m) 1 : Fin (m + 1) → E) γ.val = Pi.single (Fin.last m) 1) ∧
    (∀ (r l : ℕ) (y : UnipotentBlockColumnIndex (m + 1) r l → Ad E) (g : GA E (m + 1)), GlobalTheory.ZEul.lastRow (blkU y * g) = GlobalTheory.ZEul.lastRow g ∧
      GlobalTheory.RSnm.detAbs (blkU y * g) = GlobalTheory.RSnm.detAbs g) ∧
    (∀ (X : GroundTheory.Automorphic.FourierWhittaker.Pos (m + 1) → Ad E) (g : GA E (m + 1)),
      GlobalTheory.RSnm.detAbs (uGL X * g) = GlobalTheory.RSnm.detAbs g) := by
  intro E _ _ _ m
  refine ⟨?_, lastRow_eq, ?_, ?_, ?_⟩
  · intro γ g
    rw [lastRow_eq, GlobalTheory.ThetaUnfold.vecMul_ratGL_mul]
  · intro γ hγ
    rw [single_last_vecMul]
    funext k
    have := hγ (Fin.last m) k (Or.inl (by simp))
    rw [this]
    by_cases h : k = Fin.last m
    · subst h; simp
    · simp [Matrix.one_apply, Pi.single_apply, h, Ne.symm h]
  · intro r l y g
    have hp : ∀ t : UnipotentBlockColumnIndex (m + 1) r l, t.1.1 < t.1.2 := fun t => by
      have := t.2; exact Fin.lt_def.2 (by omega)
    refine ⟨?_, ?_⟩
    · funext j
      change ((blkU y).val * g.val) (Fin.last m) j = g.val (Fin.last m) j
      rw [blkU, posU_val, add_mul, one_mul, Matrix.add_apply, add_eq_left]
      simp only [posM, Finset.sum_mul, Matrix.sum_apply]
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [Matrix.single_mul_apply_of_ne]
      intro h
      have h1 := t.2.1
      have h2 := t.1.2.isLt
      have h3 := t.2.2.1
      rw [← h] at h1
      simp only [Fin.val_last] at h1
      omega
    · rw [GlobalTheory.RSnm.detAbs_mul, detAbs_of_det_one, one_mul]
      rw [blkU, posU_val]
      exact det_posM_eq_one (p := Subtype.val) hp y
  · intro X g
    rw [GlobalTheory.RSnm.detAbs_mul, detAbs_of_det_one, one_mul]
    rw [GroundTheory.Automorphic.FourierWhittaker.coe_uGL, GroundTheory.Automorphic.FourierWhittaker.det_uMat]

end GlobalTheory.UnfoldRows
