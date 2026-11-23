import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ

noncomputable section

open MeasureTheory

namespace PI.CdHaarScale

abbrev umat {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

def CdTieAt (cd : Formalism.BasicNotions.CDHaar) (n : ℕ) (ε : Fin n → Bool) (c : NNReal) : Prop :=
  ∀ (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
    (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
    ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
      ((c : ENNReal) • Formalism.REAL.muG ε) A =
        cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)}

end PI.CdHaarScale

namespace PI

def CdHaarScale : Prop :=
  ∀ (cd : Formalism.BasicNotions.CDHaar) (n : ℕ) (ε : Fin n → Bool), ∃ c : NNReal, 0 < c ∧ PI.CdHaarScale.CdTieAt cd n ε c

end PI
