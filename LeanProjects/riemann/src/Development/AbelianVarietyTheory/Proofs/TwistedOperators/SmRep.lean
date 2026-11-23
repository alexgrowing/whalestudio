import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.SmGL

structure SmRep (G : Type) [Group G] [TopologicalSpace G] : Type 1 where

  V : Type
  [acg : AddCommGroup V]
  [mod : Module ℂ V]

  ρ : Representation ℂ G V
  smooth : IsSmooth ρ

attribute [instance] SmRep.acg SmRep.mod

def SmRep.ofIrr {G : Type} [Group G] [TopologicalSpace G] (σ : IrrRep G) : SmRep G :=
  ⟨σ.V, σ.ρ, σ.smooth⟩

@[simp] theorem SmRep.ofIrr_ρ {G : Type} [Group G] [TopologicalSpace G] (σ : IrrRep G) :
    (SmRep.ofIrr σ).ρ = σ.ρ := rfl

section Inhabitant

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

example : Nontrivial (SmRep.ofIrr (IrrRep.ofChar (1 : GL (Fin 1) k →* ℂˣ) isSmoothChar_one)).V :=
  inferInstanceAs (Nontrivial ℂ)

end Inhabitant

end GlobalTheory.SmGL
