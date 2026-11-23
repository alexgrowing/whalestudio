import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerAbs

variable {G : Type} [Group G] [TopologicalSpace G]

def twTerm (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (y : G) : ℂ :=
  (((twCent θ δ ⊓ K.map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent θ δ)) : ℕ) : ℂ) *
    avg fun k : K => f ((y * k)⁻¹ * δ * θ (y * k))

theorem twOrb_eq_finsum_twTerm (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) :
    twOrb θ K δ f = ∑ᶠ q : DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G), twTerm θ K δ f (Quotient.out q) :=
  rfl

end GlobalTheory.EulerAbs
