import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.ThK.EvAt0.PolD GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open Classical

namespace GlobalTheory.ThK.EvAt0.PolD

theorem schrF_dOp_conj (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (w : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (a b : κ → mixedEmbedding.mixedSpace F) :
    ∃ t : ℂ, ∀ f g g' : SInf F κ, ⇑g = schrF (trP F κ) w ⇑f → ⇑g' = schrF (trP F κ) w ⇑(dOp a b f) →
      g' = dOp a b g + t • g := by
  refine ⟨2 * Real.pi * Complex.I * ((trP F κ a w.2 - trP F κ w.1 b : ℝ) : ℂ), ?_⟩
  intro f g g' hg hg'
  ext y
  have hlin : ∀ x c : κ → mixedEmbedding.mixedSpace F, lin c x = ((trP F κ x c : ℝ) : ℂ) := fun x c => rfl
  have hL : ∀ x c : κ → mixedEmbedding.mixedSpace F, linL c x = trP F κ x c := fun x c => by
    rw [linL_apply]; rfl
  have hadd : trP F κ (y + w.1) b = trP F κ y b + trP F κ w.1 b := by
    simp [trP, add_mul, Finset.sum_add_distrib, map_add]
  set φ : (κ → mixedEmbedding.mixedSpace F) → ℂ := fun z =>
    Complex.exp (-(2 * Real.pi * Complex.I) * ((trP F κ z w.2 + trP F κ w.1 w.2 / 2 : ℝ) : ℂ)) with hφdef
  have hS : ∀ h : (κ → mixedEmbedding.mixedSpace F) → ℂ, schrF (trP F κ) w h = fun z => φ z * h (z + w.1) :=
    fun h => rfl
  have h1 : HasFDerivAt (fun z => ((trP F κ z w.2 + trP F κ w.1 w.2 / 2 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (linL w.2)) y := by
    have := Complex.ofRealCLM.hasFDerivAt.comp y ((linL w.2).hasFDerivAt.add_const (trP F κ w.1 w.2 / 2))
    exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => by simp [hL])
  have hφ : HasFDerivAt φ (Complex.exp (-(2 * Real.pi * Complex.I) * ((trP F κ y w.2 + trP F κ w.1 w.2 / 2 : ℝ) : ℂ)) •
      ((-(2 * Real.pi * Complex.I)) • Complex.ofRealCLM.comp (linL w.2))) y :=
    (h1.const_mul (-(2 * Real.pi * Complex.I))).cexp
  have hf : HasFDerivAt (fun z => f (z + w.1)) (fderiv ℝ f (y + w.1)) y := by
    have := (f.differentiableAt (x := y + w.1)).hasFDerivAt.comp y ((hasFDerivAt_id y).add_const w.1)
    exact this
  have hgd : fderiv ℝ g y a = φ y * fderiv ℝ f (y + w.1) a
      + f (y + w.1) * (φ y * (-(2 * Real.pi * Complex.I) * ((trP F κ a w.2 : ℝ) : ℂ))) := by
    have hm : HasFDerivAt (fun z => φ z * f (z + w.1)) _ y := hφ.mul hf
    rw [hg, hS, hm.fderiv]
    simp [hL, hφdef]
  have hgy : g y = φ y * f (y + w.1) := by rw [hg, hS]
  have hg'y : g' y = φ y * dOp a b f (y + w.1) := by rw [hg', hS]
  rw [hg'y, SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul, dOp_apply, dOp_apply, hgd, hgy,
    hlin, hlin, hadd]
  push_cast
  ring

end GlobalTheory.ThK.EvAt0.PolD
