import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreGeneratedByGelfand
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centre_generated_by_gelfand : RelativeCentre → ∀ (A : Type) [Ring A] [Algebra ℂ A] (ι : Type) [Finite ι] (n : ℕ) (X : ι → Fin n → Fin n → A),
    (∀ i, Formalism.REAL.GlRel (X i)) → (∀ i j, i ≠ j → ∀ a b c d, X i a b * X j c d = X j c d * X i a b) →
    ∀ z ∈ Algebra.adjoin ℂ (Set.range fun p : ι × Fin n × Fin n => X p.1 p.2.1 p.2.2),
      (∀ i a b, X i a b * z = z * X i a b) →
      z ∈ Algebra.adjoin ℂ (Set.range fun p : ι × ℕ => GlobalTheory.SmoothForms.gelfA (X p.1) p.2) := by
  first | exact @GlobalTheory.LeviHC.MultiCentre.centre_multi | exact GlobalTheory.LeviHC.MultiCentre.centre_multi | (intros; apply GlobalTheory.LeviHC.MultiCentre.centre_multi <;> assumption)
