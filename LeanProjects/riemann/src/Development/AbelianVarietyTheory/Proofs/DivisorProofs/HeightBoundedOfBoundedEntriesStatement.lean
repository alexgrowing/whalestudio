import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightBoundedOfBoundedEntries
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_bounded_of_bounded_entries : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (ι : Type) (g : ι → GL (Fin n) (AE F E)),
    (∀ i j, (fun t => (g t : Matrix (Fin n) (Fin n) (AE F E)) i j) ∈ Bdd F E ι) →
    (∀ i j, (fun t => (((g t)⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) i j) ∈ Bdd F E ι) →
    ∃ K : ℝ≥0, ∀ t, heightGL F (g t) ≤ K := by
  first | exact @GlobalTheory.QhtUnip.HeightBound.heightGL_bdd | exact GlobalTheory.QhtUnip.HeightBound.heightGL_bdd | (intros; apply GlobalTheory.QhtUnip.HeightBound.heightGL_bdd <;> assumption)
