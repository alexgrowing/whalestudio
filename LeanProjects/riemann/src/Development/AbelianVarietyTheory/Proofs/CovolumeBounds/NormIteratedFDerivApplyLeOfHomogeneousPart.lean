import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open Metric Set
open scoped Nat ContDiff

namespace GlobalTheory.SCV

section Polarisation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {𝕜 E V : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

end Polarisation

section OpNorm

variable {ι 𝕜 E V : Type*} [Fintype ι] [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

end OpNorm

section Homogeneous

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

noncomputable def homogeneousPart (c : ℕ) (F : E → V) (a : E) (v : E) : V :=
  (c ! : ℂ)⁻¹ • iteratedFDeriv ℂ c F a (fun _ => v)

@[simp] theorem homogeneousPart_zero (F : E → V) (a v : E) : homogeneousPart 0 F a v = F a := by
  simp [homogeneousPart]

variable [FiniteDimensional ℂ E] [CompleteSpace V]

end Homogeneous

end GlobalTheory.SCV
