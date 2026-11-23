import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisCharacterAntiRamifiedExactly
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
theorem _root_.GlobalTheory.T.galois_character_anti_ramified_exactly : PrN → ∀ (D : D7) (l : ℕ) (Q : Finset (PlE D.host)) (χ : HChar D.host.E) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ), l.Prime → IsPsi (H := D.host) l Q χ → GalOf D χ ψ₀ → AntiHom D.ntw.cc ψ₀ ∧ RamExactly ψ₀ (↑Q : Set (PlE D.host)) ∧ BlochKatoReduction.Gen.TrivAbove ψ₀ l := by
  first | exact @GlobalTheory.GalTwist.galOf_twist_props | exact GlobalTheory.GalTwist.galOf_twist_props | (intros; apply GlobalTheory.GalTwist.galOf_twist_props <;> assumption)
