import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.ThetaPer

theorem thetaD_aDp_pow_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    ∀ (n : ℕ), ((Per.θD l).comp (aDp l)) (τ ^ n) ≠ 0 := by
  intro l _ K bk τ hτ n
  obtain ⟨-, ε, η, hε, hφ⟩ := hτ
  have hinj : Function.Injective (WittVector.frobenius : Ainf l → Ainf l) := by
    intro x y h
    rw [WittVector.frobenius_eq_map_frobenius] at h
    exact WittVector.map_injective _ (frobeniusEquiv (OCb l) l).injective h
  have hpi : WittVector.frobenius (GlobalTheory.MemLoc.TiedUnif.piOne ε) = WittVector.teichmuller l ε - 1 := by
    rw [GlobalTheory.MemLoc.TiedUnif.piOne, map_sub, map_one, WittVector.frobenius_eq_map_frobenius]
    change WittVector.map (frobenius (OCb l) l) (WittVector.teichmuller l ((frobeniusEquiv (OCb l) l).symm ε)) - 1 = _
    rw [WittVector.map_teichmuller, frobenius_apply_frobeniusEquiv_symm]
  have hsurj : Function.Surjective (WittVector.frobenius : Ainf l → Ainf l) := by
    intro y
    obtain ⟨x, hx⟩ := WittVector.map_surjective _ (frobeniusEquiv (OCb l) l).surjective y
    exact ⟨x, by rw [WittVector.frobenius_eq_map_frobenius]; exact hx⟩
  obtain ⟨η₀, hη₀⟩ := hsurj (η : Ainf l)
  obtain ⟨η₁, hη₁⟩ := hsurj ((η⁻¹ : (Ainf l)ˣ) : Ainf l)
  have hu : η₀ * η₁ = 1 := hinj (by rw [map_mul, map_one, hη₀, hη₁, Units.mul_inv])
  have hτe : τ = η₀ * GlobalTheory.MemLoc.TiedUnif.piOne ε := hinj (by rw [hφ, map_mul, hη₀, hpi])
  set f := (Per.θD l).comp (aDp l)
  have hf0 : f η₀ ≠ 0 := by
    intro h
    have := congrArg f hu
    rw [map_mul, h, zero_mul, map_one] at this
    exact zero_ne_one this
  have hf1 : f (GlobalTheory.MemLoc.TiedUnif.piOne ε) ≠ 0 := GlobalTheory.MemLoc.TiedUnif.theta_piOne hε
  rw [map_pow, hτe, map_mul]
  exact pow_ne_zero _ (mul_ne_zero hf0 hf1)

end GlobalTheory.ThetaPer
