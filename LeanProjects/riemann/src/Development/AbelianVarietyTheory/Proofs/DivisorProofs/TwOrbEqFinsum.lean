import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw

def twSum {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (g : G) : ℂ :=
  (((twCent θ δ ⊓ K.map (MulAut.conj g).toMonoidHom).relIndex (cptPart (twCent θ δ)) : ℕ) : ℂ) *
    avg fun k : K => f ((g * k)⁻¹ * δ * θ (g * k))

def pairTw {G₁ G₂ : Type} [Group G₁] [Group G₂] (θ₁ : G₂ →* G₁) (θ₂ : G₁ →* G₂) : G₁ × G₂ →* G₁ × G₂ :=
  (θ₁.comp (MonoidHom.snd G₁ G₂)).prod (θ₂.comp (MonoidHom.fst G₁ G₂))

@[simp] theorem pairTw_apply {G₁ G₂ : Type} [Group G₁] [Group G₂] (θ₁ : G₂ →* G₁) (θ₂ : G₁ →* G₂) (y : G₁ × G₂) :
    pairTw θ₁ θ₂ y = (θ₁ y.2, θ₂ y.1) := rfl

variable (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)

def rho (u : Pl E) : Gam E n u →* GLw n u × GLw n (cPl E u) :=
  ((GeneralLinearGroup.map (pLoc E u)).comp (Gam E n u).subtype).prod
    ((GeneralLinearGroup.map (pLoc E (cPl E u))).comp (Gam E n u).subtype)

end GlobalTheory.EulerTw
