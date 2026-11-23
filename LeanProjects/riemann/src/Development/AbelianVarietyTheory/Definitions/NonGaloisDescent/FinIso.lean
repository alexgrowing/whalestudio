import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAutLoc
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open scoped TensorProduct

namespace GlobalTheory.FormDict

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

structure FinIso where
  κ : AL L ≃+* FiniteAdeleRing (𝓞 L) L
  left : ∀ x : L, κ (x ⊗ₜ 1) = algebraMap L _ x
  right : ∀ (w : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))), NG.OverPl w v →
    ∃ i : v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L, Continuous i ∧
      ∀ a : FiniteAdeleRing (𝓞 (maximalRealSubfield L)) (maximalRealSubfield L), κ (1 ⊗ₜ a) w = i (a v)
  j : GAf L n →* UA L n
  fin : ∀ x, j x ∈ finU L n
  loc : ∀ (x : GAf L n) (w : HeightOneSpectrum (𝓞 L)) (s t : Fin n),
    (cLoc w (j x) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) s t =
      κ (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) s t) w
  onto : ∀ y ∈ finU L n, ∃ x, j x = y

variable {L n}

def Dict (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)) : Prop :=
  IsAutRepU U ∧ U.map (LinearMap.funLeft ℂ ℂ F.j) =
    Submodule.span ℂ {φ | ∃ f ∈ π.S, ∃ lam : Module.Dual ℂ π.W, φ = fun x => lam (f x)}

end GlobalTheory.FormDict

end
