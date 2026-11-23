import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CoreFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerpEmb

noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut

namespace GlobalTheory.LeviGL

section Group

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {a : ℕ}

def lev (ι : GlobalTheory.CuspRep.GA E a →* GAd σ J) (U : Subgroup (GAd σ J)) (g : GAd σ J) :
    Subgroup (GL (Fin a) (GlobalTheory.CuspRep.Af E)) :=
  U.comap ((MulAut.conj g⁻¹).toMonoidHom.comp (ι.comp (GlobalTheory.CuspRep.finGL E a)))

variable [IsTotallyComplex E]

def types {K : Subgroup (GAd σ J)} (W : Submodule ℂ (K → ℂ)) (ι : GlobalTheory.CuspRep.GA E a →* GAd σ J) (g : GAd σ J)
    (hK : ∀ κ : GlobalTheory.CuspRep.Kinf E a, g⁻¹ * ι (GlobalTheory.CuspRep.infGL E a (Unitary.toUnits κ)) * g ∈ K) :
    Submodule ℂ (GlobalTheory.CuspRep.Kinf E a → ℂ) :=
  W.map (LinearMap.funLeft ℂ ℂ fun κ => ⟨g⁻¹ * ι (GlobalTheory.CuspRep.infGL E a (Unitary.toUnits κ)) * g, hK κ⟩)

end Group

section Good

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def Good (L : Subgroup (GL (Fin a) (GlobalTheory.CuspRep.Af E))) (W₁ : Submodule ℂ (GlobalTheory.CuspRep.Kinf E a → ℂ))
    (ψ : GlobalTheory.CuspRep.Sm E a) : Prop :=
  GlobalTheory.CuspRep.IsAutForm ψ ∧ (∀ l ∈ L, GlobalTheory.CuspRep.finRep E a l ψ = ψ) ∧
    ∀ x, (fun κ : GlobalTheory.CuspRep.Kinf E a => (GlobalTheory.CuspRep.cptRep E a κ ψ).1 x) ∈ W₁

end Good

end GlobalTheory.LeviGL

end
