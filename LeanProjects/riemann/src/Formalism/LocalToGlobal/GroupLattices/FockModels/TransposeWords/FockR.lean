import Formalism.GradedWeylDivisibility.StatementE

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model.TS

open Formalism.GradedWeylDivisibility

def fockR {σ R : Type*} [CommRing R] (f g : MvPolynomial σ R) : R :=
  ∑ m ∈ f.support, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R)

def toK (O K : Type*) [CommRing O] [CommRing K] [Algebra O K] {σ : Type*} : MvPolynomial σ O →ₗ[O] MvPolynomial σ K :=
  (mapAlgHom (Algebra.ofId O K)).toLinearMap

end Formalism.L2.G.Model.TS
