import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockValAe
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_block_val_at_and_exists_inv_eq : ∀ {E : Type} [Field E] [NumberField E] {K : Type} [Field K] (ε : K →+* ℂ) (μ η : HChar E), AlmostIn ε μ → η.ValuesIn (1 / 2) ε → ∀ {r : ℕ}, Odd r → ∀ (μH ηH : Formalism.L2.NC.HC E), μH.χ = (μ : Ideles E →* ℂˣ) → ηH.χ = (η : Ideles E →* ℂˣ) → ∀ᶠ v in Filter.cofinite, (μH * ηH⁻¹).At v ((((block μ η r).val v : ℂˣ) : ℂ) * (Real.sqrt (normV v) : ℂ) ^ (-(r : ℤ))) ∧ ∃ y : K, ε y = (((block μ η r).val v : ℂˣ) : ℂ)⁻¹ := by
  first | exact @GlobalTheory.BlockVal.block_val_ae | exact GlobalTheory.BlockVal.block_val_ae | (intros; apply GlobalTheory.BlockVal.block_val_ae <;> assumption)
