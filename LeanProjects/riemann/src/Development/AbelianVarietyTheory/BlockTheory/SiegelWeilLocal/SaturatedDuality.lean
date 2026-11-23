import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

open NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SaturatedLatticeDuality

open Formalism.MainNotions.S GlobalTheory.Count

def SatIn (I : AutInst) (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Prop :=
  Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) S

def StepDuality : Prop :=
  ∀ (I : AutInst) (x : I.GA),
    Formalism.HN.ht (bas I) (frm I x) (lamX I x) = 1 ∧
    (1 ≤ I.n → Formalism.HN.largestSize (bas I) (frm I x) (lamX I x) * least I x = 1) ∧
    (∀ t : ℝ, 0 < t →
      perpIn I x (stepLe I x t) = stepLt I x (1 / t) ∧
      perpIn I x (stepLt I x t) = stepLe I x (1 / t)) ∧
    (∀ S : Submodule (𝓞 I.E) (Fin I.n → I.E), SatIn I x S →
      SatIn I x (perpIn I x S) ∧
      Formalism.HN.rkK (perpIn I x S) + Formalism.HN.rkK S = I.n ∧
      perpIn I x (perpIn I x S) = S) ∧
    ∀ S S' : Submodule (𝓞 I.E) (Fin I.n → I.E), SatIn I x S → SatIn I x S' → S ≤ S' →
      Formalism.HN.htQ (bas I) (frm I x) (perpIn I x S) (perpIn I x S') *
        Formalism.HN.htQ (bas I) (frm I x) S' S = 1

example (I : AutInst) (x : I.GA) : perpIn I x ⊥ = lamX I x := by
  apply le_antisymm
  · exact Submodule.span_le.2 fun y hy => hy.1
  · intro y hy
    refine Submodule.subset_span ⟨hy, fun s hs => ?_⟩
    rw [(Submodule.mem_bot _).1 hs]
    simp [Formalism.UG.hform]

example (I : AutInst) (x : I.GA) (S S' : Submodule (𝓞 I.E) (Fin I.n → I.E)) (h : S ≤ S') :
    perpIn I x S' ≤ perpIn I x S :=
  Submodule.span_mono fun _ hy => ⟨hy.1, fun s hs => hy.2 s (h hs)⟩

end GlobalTheory.IndefiniteRowSideFullHecke.SaturatedLatticeDuality
