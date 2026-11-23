import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LogCardLevelGroupLeScalePowMulLengthStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LogHostClassNumberLeScalePowFamilyStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem mul_rpow_self_le {x c C : ℝ} (hx : 1 ≤ x) (hc : c ≤ C) (hC : 0 ≤ C) :
    c * x ^ c ≤ C * x ^ C := by
  have h0 : 0 ≤ x ^ c := Real.rpow_nonneg (by linarith) _
  calc c * x ^ c ≤ C * x ^ c := mul_le_mul_of_nonneg_right hc h0
    _ ≤ C * x ^ C := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx hc) hC

theorem admissible_parameters_design_family : ∀ {eps : ℝ} (Fm : FamP eps), ∃ C x0 : ℝ, 1 ≤ C ∧ ∀ x ≥ x0, ∀ (hx : Fm.x1 < x)
    (i : Fm.Ix x), TwistedPlaces.ParametersPolynomiallyBounded (Fm.L x i) C (Fm.params x hx i) := by
  intro eps Fm
  obtain ⟨C1, y1, h1⟩ := GlobalTheory.T.log_hostClassNumber_le_scale_pow_family Fm
  obtain ⟨C2, y2, h2⟩ := GlobalTheory.T.exists_log_card_restRows_le_pow_mul_length Fm
  set C : ℝ := max 1 (max (Fm.PK.getD 7 0) (max (Fm.PK.getD 19 0) (max (9 / 2 + 10 * eps + eps / 100)
    (max (2 + 8 * eps + eps / 100) (max (Fm.Ct + eps / 100) (max C1 C2)))))) with hCdef
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC0 : 0 ≤ C := by linarith
  have hCLw : Fm.PK.getD 7 0 ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCYL : Fm.PK.getD 19 0 ≤ C :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hrest : max (9 / 2 + 10 * eps + eps / 100)
      (max (2 + 8 * eps + eps / 100) (max (Fm.Ct + eps / 100) (max C1 C2))) ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hK : 9 / 2 + 10 * eps + eps / 100 ≤ C := le_trans (le_max_left _ _) hrest
  have hN : 2 + 8 * eps + eps / 100 ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hrest
  have hT : Fm.Ct + eps / 100 ≤ C :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hrest
  have hc12 : max C1 C2 ≤ C :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hrest
  have hCC1 : C1 ≤ C := le_trans (le_max_left _ _) hc12
  have hCC2 : C2 ≤ C := le_trans (le_max_right _ _) hc12
  refine ⟨C, max y1 y2, hC1, fun x hxy hx i => ?_⟩
  have hx1 : 1 ≤ x := le_of_lt (lt_trans Fm.one_lt_family_threshold hx)
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have heps : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hPK := Fm.params_K x hx i
  obtain ⟨sN, -, sK, -, sT, -, -, -, -, -, -, sDe2, -⟩ := Fm.sizes x hx i
  unfold SizeN szTh at sN
  unfold SizeK szTh at sK
  unfold SizeT szTh at sT
  unfold SizeDe2 at sDe2
  rw [hsx, heps] at sN sK
  rw [hsx, heps, Fm.Ct_eq x i] at sT
  have hmono : ∀ a : ℝ, a ≤ C → x ^ a ≤ x ^ C := fun a ha => Real.rpow_le_rpow_of_exponent_le hx1 ha
  have hLg : 0 ≤ (Fm.L x i).sc.L := by
    unfold Scale.L
    exact Real.rpow_nonneg (le_trans zero_le_one (le_of_lt (Fm.L x i).sc.one_lt_alt)) _
  unfold TwistedPlaces.ParametersPolynomiallyBounded
  refine ⟨?_, ?_, ?_, ?_, ?_, sDe2, ?_, ?_⟩
  · have e : (Fm.params x hx i).CLw = Fm.PK.getD 7 0 := by rw [← hPK]; rfl
    rw [e]; exact hCLw
  · have e : (Fm.params x hx i).CYL = Fm.PK.getD 19 0 := by rw [← hPK]; rfl
    rw [e]; exact hCYL
  · rw [hsx]; exact le_trans sK.2 (hmono _ hK)
  · rw [hsx]; exact le_trans sN.2 (hmono _ hN)
  · rw [hsx]; exact le_trans sT.2 (hmono _ hT)
  · rw [hsx]
    exact le_trans (h1 x (le_trans (le_max_left _ _) hxy) hx i) (mul_rpow_self_le hx1 hCC1 hC0)
  · rw [hsx]
    refine le_trans (h2 x (le_trans (le_max_right _ _) hxy) hx i) ?_
    exact mul_le_mul_of_nonneg_right (mul_rpow_self_le hx1 hCC2 hC0) hLg

end GlobalTheory.NLink
