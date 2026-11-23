import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

namespace GlobalTheory.JR.WeilProd

def tensorRep {G H X Y : Type} (W₁ : G → (X → ℂ) → X → ℂ) (W₂ : H → (Y → ℂ) → Y → ℂ) :
    G × H → (X × Y → ℂ) → X × Y → ℂ :=
  fun g f p => W₁ g.1 (fun u => W₂ g.2 (fun v => f (u, v)) p.2) p.1

theorem tensorRep_apply {G H X Y : Type} (W₁ : G → (X → ℂ) → X → ℂ) (W₂ : H → (Y → ℂ) → Y → ℂ) (g : G × H)
    (f : X × Y → ℂ) (p : X × Y) :
    tensorRep W₁ W₂ g f p = W₁ g.1 (fun u => W₂ g.2 (fun v => f (u, v)) p.2) p.1 := rfl

end GlobalTheory.JR.WeilProd
