import Mathlib

open scoped ContDiff Topology

noncomputable section

namespace PI.BesselDerivW

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]

def liftA (a : E →L[ℝ] E) : ℝ × E →L[ℝ] ℝ × E :=
  (ContinuousLinearMap.inr ℝ ℝ E).comp (a.comp (ContinuousLinearMap.snd ℝ ℝ E))

theorem liftA_apply (a : E →L[ℝ] E) (p : ℝ × E) : liftA a p = (0, a p.2) := rfl

def rX (a : E →L[ℝ] E) (Φ : ℝ × E → V) (p : ℝ × E) : V := fderiv ℝ Φ p (liftA a p)

def dT (Φ : ℝ × E → V) (p : ℝ × E) : V := fderiv ℝ Φ p ((1 : ℝ), (0 : E))

variable {W : Set (ℝ × E)} {Φ : ℝ × E → V}

end PI.BesselDerivW
