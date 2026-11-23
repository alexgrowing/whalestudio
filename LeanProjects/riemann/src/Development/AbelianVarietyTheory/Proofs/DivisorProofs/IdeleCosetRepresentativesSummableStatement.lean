import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleCosetRepresentativesSummable
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DecayNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsInfEqOne

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idele_coset_representatives_summable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (s m : ℕ), 2 ≤ s → 0 < m →
    ∃ b : ℕ → (AE F E)ˣ, (∀ j w, GlobalTheory.Doubling.unitInf F E w (b j) = 1) ∧
      (∀ l : (AE F E)ˣ, (∀ i v, evFin F v ((m : AF F) * GlobalTheory.IdeleDecay.coord F E l.1 i) ∈ v.adicCompletionIntegers F) →
        ∃ j, (b j)⁻¹ * l ∈ GlobalTheory.IdeleTate.stab F E) ∧
      Summable (fun j => (GlobalTheory.IdeleTate.absFin F E (b j) : ℝ) ^ s) := by
  first | exact @GlobalTheory.IdeleTate.Count.exists_representatives | exact GlobalTheory.IdeleTate.Count.exists_representatives | (intros; apply GlobalTheory.IdeleTate.Count.exists_representatives <;> assumption)
