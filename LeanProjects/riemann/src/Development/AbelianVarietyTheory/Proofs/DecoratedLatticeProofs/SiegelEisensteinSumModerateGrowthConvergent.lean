import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermsAbsTsumLeHeightPoly
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.EisConvGrowth

theorem eis_modGrowth : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → ∀ (μ : (AE D)ˣ →* Circle) (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ → (V.rank : ℝ) / 2 < s₁.re → GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V φ) := by
  intro D V a ha hI μ s₁ φ hφ h
  haveI := t2Space_adeleRing' (F := D.host.F)
  obtain ⟨C₁, hC₁⟩ : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C * (hgt V a g : ℝ) ^ (s₁.re + (V.rank : ℝ) / 2) :=
    hI.exists_norm_le continuous_absE (isCompact_Khat V a) hφ
  obtain ⟨C₂, hC₂, h₂⟩ := GlobalTheory.SWAbsGrowth.hgt_mul_le V a ha
  set τ : ℝ := s₁.re + (V.rank : ℝ) / 2 with hτ
  have hτ0 : 0 ≤ τ := by
    have : (0 : ℝ) ≤ (V.rank : ℝ) / 2 := by positivity
    linarith
  have hs := GlobalTheory.Eis.sphConv D V a hI s₁.re h
  set S := ∑' q : GlobalTheory.Eis.SiegelCosets V, (hgt V a (q.out : GQ (dblSp V)) : ℝ) ^ τ with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => by positivity
  set M : ℕ := ⌈τ⌉₊ with hM
  refine ⟨max C₁ 0 * (max C₂ 1) ^ M * S, 2 * V.rank * M, fun y => ?_⟩
  set H := GlobalTheory.Grow.height (dblSp V) y with hH
  have hH1 : 1 ≤ H := GlobalTheory.Grow.one_le_height _ y
  set K := max C₂ 1 * H ^ (2 * V.rank) with hK
  have hone : 1 ≤ K := one_le_mul_of_one_le_of_one_le (le_max_right _ _) (one_le_pow₀ hH1)
  set c := max C₁ 0 * K ^ M with hc
  have hq : ∀ x : GA D (dblSp V), ‖φ (x * y)‖ ≤ c * (hgt V a x : ℝ) ^ τ := by
    intro x
    refine (hC₁ _).trans ?_
    refine (mul_le_mul_of_nonneg_right (le_max_left C₁ 0) (by positivity)).trans ?_
    rw [hc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
    have h3 : (hgt V a (x * y) : ℝ) ≤ hgt V a x * K :=
      (h₂ x y).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (NNReal.coe_nonneg _))
    refine (Real.rpow_le_rpow (NNReal.coe_nonneg _) h3 hτ0).trans ?_
    rw [Real.mul_rpow (NNReal.coe_nonneg _) (by positivity), mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [← Real.rpow_natCast _ M]
    exact Real.rpow_le_rpow_of_exponent_le hone (Nat.le_ceil τ)
  have hsum : HasSum (fun q : GlobalTheory.Eis.SiegelCosets V => c * (hgt V a (q.out : GQ (dblSp V)) : ℝ) ^ τ) (c * S) :=
    hs.hasSum.mul_left c
  have hb : ‖GlobalTheory.Eis.eis V φ y‖ ≤ c * S := tsum_of_norm_bounded hsum fun q => hq _
  refine hb.trans (le_of_eq ?_)
  rw [hc, hK, mul_pow, ← pow_mul]
  ring

end GlobalTheory.EisConvGrowth

end
