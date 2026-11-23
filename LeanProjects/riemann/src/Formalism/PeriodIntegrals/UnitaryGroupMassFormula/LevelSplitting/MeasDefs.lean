import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.LevelSAllOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.MulVecSpanStable

noncomputable section

namespace PI.LevelKSplit.W.Meas

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct

def PlacesCountable : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], Countable (HeightOneSpectrum (𝓞 F))

def ContPlace : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)),
    Continuous (fun g : HA (Af F) σ J =>
      ((compV v (incAf σ J g) : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)))

def LatBorel : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E)),
    MeasurableSet[borel (Fin n → Fv F v ⊗[F] E)] (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E))

end PI.LevelKSplit.W.Meas
