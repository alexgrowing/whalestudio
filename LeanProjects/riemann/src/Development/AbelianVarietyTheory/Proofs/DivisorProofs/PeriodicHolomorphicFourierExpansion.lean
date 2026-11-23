import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChSingle
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsFourierExpansionHolomorphicTube
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.FourierCoeffUnitCubeTranslateOfEntirePeriodic
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.FamilyFourier
open scoped Real ContDiff

namespace GlobalTheory.FamilyFourier

theorem hasSum_coef_mul_ch {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Set E} (h : Pt E g → ℂ) (hU : IsOpen U)
    (hh : DifferentiableOn ℂ h (cov U g))
    (hper : ∀ P ∈ cov U g, ∀ i : Fin g, h (P.1, P.2 + Pi.single i 1) = h P) :
    ∀ P ∈ cov U g, HasSum (fun n : Fin g → ℤ => coef h n P.1 * ch n P.2) (h P) := by
  rintro ⟨b, z⟩ hP
  have hb : b ∈ U := hP.1
  have hopen : IsOpen (cov U g) := hU.prod isOpen_univ
  set f : (Fin g → ℂ) → ℂ := fun w => h (b, w) with hfdef
  have hfd : Differentiable ℂ f := by
    intro w
    have hw : (b, w) ∈ cov U g := ⟨hb, Set.mem_univ _⟩
    have h1 : DifferentiableAt ℂ h (b, w) := hh.differentiableAt (hopen.mem_nhds hw)
    have h2 : DifferentiableAt ℂ (fun w' : Fin g → ℂ => ((b, w') : Pt E g)) w := by fun_prop
    exact h1.comp w h2
  have hunit : ∀ (i : Fin g) (w : Fin g → ℂ), f (w + Pi.single i 1) = f w := fun i w =>
    hper (b, w) ⟨hb, Set.mem_univ _⟩ i
  obtain ⟨a, hsum, hcoef⟩ := GlobalTheory.exists_fourier_expansion_tube (Fin g) Set.univ f isOpen_univ
    convex_univ hfd.differentiableOn
    (fun w _ m => GlobalTheory.apply_add_intCast_vec_of_unit_periods hunit m w)
  have ha : ∀ ν, a ν = coef h ν b := by
    intro ν
    rw [hcoef 0 (Set.mem_univ _) ν, coef]
    have hs : (Set.univ.pi fun _ : Fin g => Set.Ico (0:ℝ) 1) =ᵐ[(volume : Measure (Fin g → ℝ))]
        Set.Icc (0 : Fin g → ℝ) 1 := by
      rw [volume_pi]; exact Measure.univ_pi_Ico_ae_eq_Icc
    rw [setIntegral_congr_set hs]
    · refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
      simp only [hfdef, Pi.zero_apply, Complex.ofReal_zero, mul_zero, add_zero]
      congr 2
      ring
  have := hsum z (Set.mem_univ _)
  simpa [ha, ch] using this

end GlobalTheory.FamilyFourier
