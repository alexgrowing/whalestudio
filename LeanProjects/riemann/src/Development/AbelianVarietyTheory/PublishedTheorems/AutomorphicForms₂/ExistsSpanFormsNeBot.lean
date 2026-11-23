import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd

noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.Published

namespace AutFinGL

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def forms (L : Subgroup (GL (Fin a) (Af E))) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E a) W) (c : (E →+* ℂ) → ℂ → ℂ) : Set (Sm E a) :=
  {φ | IsAutForm φ ∧ (∀ k ∈ L, finRep E a k φ = φ) ∧
    (∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k φ).1 g) ∈ AutFin.coeffSpan ρ) ∧
    ∀ τ u, cap τ u φ = c τ u • φ}

end AutFinGL

def AutomorphicFormsFiniteGL : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))),
    IsOpen (L : Set (GL (Fin a) (Af E))) →
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W),
    AutFin.IsContRep ρ →
  ∀ c : (E →+* ℂ) → ℂ → ℂ, FiniteDimensional ℂ (Submodule.span ℂ (AutFinGL.forms L ρ c))

namespace AutFinGL

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem type_of_map {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W)
    (T : W →ₗ[ℂ] Sm E a) (hT : ∀ k w, T (ρ k w) = cptRep E a k (T w)) (w : W) (g : GA E a) :
    (fun k : Kinf E a => (cptRep E a k (T w)).1 g) ∈ AutFin.coeffSpan ρ :=
  Submodule.subset_span ⟨(LinearMap.proj g).comp ((Sm E a).subtype.comp T), w,
    funext fun k => (congrFun (congrArg Subtype.val (hT k w)) g).symm⟩

end AutFinGL

end GlobalTheory.Published

end
