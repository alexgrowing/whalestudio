import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddCharCompletionOfResidueAddChar
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_addChar_completion_of_residue_addChar : ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (p : ℕ) [Fact p.Prime]
    (red : v.adicCompletionIntegers K →+* ZMod p) (ψ' : AddChar (ZMod p) ℂ), ψ' ≠ 1 →
    ∃ ψ₀ : AddChar (v.adicCompletion K) ℂ, (∀ x, Valued.v x < 1 → ψ₀ x = 1) ∧ (∃ x, Valued.v x ≤ 1 ∧ ψ₀ x ≠ 1) ∧
      ∀ y : v.adicCompletionIntegers K, ψ₀ (y : v.adicCompletion K) = ψ' (red y) := by
  first | exact @GlobalTheory.ResidueChar.exists_addChar_completion_lift_residue | exact GlobalTheory.ResidueChar.exists_addChar_completion_lift_residue | (intros; apply GlobalTheory.ResidueChar.exists_addChar_completion_lift_residue <;> assumption)
