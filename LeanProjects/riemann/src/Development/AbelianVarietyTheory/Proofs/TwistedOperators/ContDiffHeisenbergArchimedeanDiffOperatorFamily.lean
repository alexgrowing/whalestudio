import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DOpDef

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
open GlobalTheory.HeisOrbit

theorem GlobalTheory.HeisOrbit.dOp_contDiff_family {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (G : ℝ → SInf F κ) (Pv Qv : ℝ → (κ → mixedEmbedding.mixedSpace F)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => G p.1 p.2) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Pv → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Qv →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => GlobalTheory.HeisOrbit.dOp (Pv p.1) (Qv p.1) (G p.1) p.2) := by
  intro hG hP hQ
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : (ℝ × (κ → mixedEmbedding.mixedSpace F)) × (κ → mixedEmbedding.mixedSpace F) => (G x.1.1 : (κ → mixedEmbedding.mixedSpace F) → ℂ) x.2) :=
    hG.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => fderiv ℝ (fun y : (κ → mixedEmbedding.mixedSpace F) => (G p.1 : (κ → mixedEmbedding.mixedSpace F) → ℂ) y) p.2) :=
    ContDiff.fderiv (f := fun (p : ℝ × (κ → mixedEmbedding.mixedSpace F)) (y : (κ → mixedEmbedding.mixedSpace F)) => (G p.1 : (κ → mixedEmbedding.mixedSpace F) → ℂ) y) hf contDiff_snd
      (le_of_eq (by simp))
  have hD' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => fderiv ℝ (fun y : (κ → mixedEmbedding.mixedSpace F) => (G p.1 : (κ → mixedEmbedding.mixedSpace F) → ℂ) y) p.2 (Pv p.1)) :=
    hD.clm_apply (hP.comp contDiff_fst)
  have hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => ∑ i, p.2 i * Qv p.1 i) := by
    refine ContDiff.sum (fun i _ => ?_)
    exact ((contDiff_apply ℝ _ i).comp contDiff_snd).mul
      ((contDiff_apply ℝ _ i).comp (hQ.comp contDiff_fst))
  have hT : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, p.2 i * Qv p.1 i) : ℝ) : ℂ)) := by
    have hl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : mixedEmbedding.mixedSpace F => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) z) :=
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).toContinuousLinearMap.contDiff
    exact Complex.ofRealCLM.contDiff.comp (hl.comp hS)
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => (G p.1 : (κ → mixedEmbedding.mixedSpace F) → ℂ) p.2) := hG
  unfold GlobalTheory.HeisOrbit.dOp
  exact hD'.sub ((contDiff_const.mul hT).mul hg)
