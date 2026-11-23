import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HermCoord

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
open GlobalTheory.SWC

noncomputable section

namespace GlobalTheory.HermSD

def coordPair {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (n : ℕ) (x y : (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E)) : R :=
  ∑ a, x.1 a * y.1 a + ∑ p, Algebra.trace R (R ⊗[F] E) (sigR R σ (x.2 p) * y.2 p)

end GlobalTheory.HermSD
