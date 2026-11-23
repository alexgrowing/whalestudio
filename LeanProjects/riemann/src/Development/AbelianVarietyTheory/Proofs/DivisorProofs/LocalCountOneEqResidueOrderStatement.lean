import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCountOneEqResidueOrder
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_count_one_eq_residue_order : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), 2 ≤ r → Unr E → SelfDualLat G Λ → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), locCount (IsCMField.complexConj E).toAlgHom Gᵀ Λ v 1 = resOrder E r v := by
  first | exact @GlobalTheory.TamOne.locCount_one_eq_resOrder | exact GlobalTheory.TamOne.locCount_one_eq_resOrder | (intros; apply GlobalTheory.TamOne.locCount_one_eq_resOrder <;> assumption)
