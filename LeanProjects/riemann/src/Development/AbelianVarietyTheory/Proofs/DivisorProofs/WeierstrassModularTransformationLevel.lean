import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyIffValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassPTorsionIsModularFamilyStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem wB_smul_transform : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ), wB N x (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ 2 * wB N (vact N x γ) τ - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) / (2 * Real.pi * Complex.I) := by
  intro N _ x γ τ
  have h := congrFun (EisensteinSeries.G2_slash_action γ) τ
  rw [ModularForm.SL_slash_apply, Pi.sub_apply, EisensteinSeries.D2] at h
  have hj : UpperHalfPlane.denom γ τ ≠ 0 := UpperHalfPlane.denom_ne_zero _ _
  have hd : UpperHalfPlane.denom γ τ = ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
    simp [ModularGroup.denom_apply]
  have hG : EisensteinSeries.G2 (γ • τ) = UpperHalfPlane.denom γ τ ^ 2 * EisensteinSeries.G2 τ
      - 2 * Real.pi * Complex.I * ((γ 1 0 : ℤ) : ℂ) * UpperHalfPlane.denom γ τ := by
    rw [zpow_neg, zpow_ofNat] at h
    field_simp at h
    linear_combination h
  have hwp := ((GlobalTheory.QFam.isFam_iff_values _ _ _ _).1 (GlobalTheory.T.weierstrassP_torsion_isModularFamily N).1) x γ τ
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [zpow_ofNat] at hwp
  rw [wB, wB, gN, gN, hwp, hG, hd]
  field_simp
  ring
