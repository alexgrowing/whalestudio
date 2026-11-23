import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

def RelBaseChange.Statement : Prop :=
  ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] (σ τ : Type) (g : σ → MvPolynomial τ F),
    (RingHom.ker (aeval g : MvPolynomial σ F →ₐ[F] MvPolynomial τ F)).map
        (MvPolynomial.map (algebraMap F F')) =
      RingHom.ker (aeval (fun s => MvPolynomial.map (algebraMap F F') (g s)) :
        MvPolynomial σ F' →ₐ[F'] MvPolynomial τ F')

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
