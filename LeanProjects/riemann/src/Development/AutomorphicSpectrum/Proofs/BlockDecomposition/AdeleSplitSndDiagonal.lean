import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import CompanionTheory.AutomorphicTheory.SiegelWeilFiniteness.Bridge
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.OfUnfolding

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT bc UJ)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.ClassFin

section Reduction

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem projFin_ratEmb_val (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (γ : GRat σ J) :
    (GlobalTheory.AdelicU.projFin σ J (ratEmb σ J γ)).1 = bc (inclR (Af F)) γ.1 := by
  refine Units.ext (Matrix.ext fun r s => ?_)
  change Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] (γ.1.1 r s)) =
    (1 : Af F) ⊗ₜ[F] (γ.1.1 r s)
  simp

end Reduction

section Lattices

open GroundTheory.Automorphic GroundTheory.Heights₂.Heights.FiniteCovolume Module
open scoped Pointwise

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

end Lattices

end GlobalTheory.CompanionTheory.ClassFin
