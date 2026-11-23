import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PerIntOnAmb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HtPsiLeIffExists

noncomputable section

namespace GlobalTheory.Core.Int

open Formalism.BasicNotions NumberField IsDedekindDomain

variable (D : D7) (u : D.what₂.Word)

def PsiGeOn (N : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (w : D.what₂.places.Pl) (s : ℝ) : Prop :=
  ∀ φ ∈ N, ∃ (a : D.what₂.LL) (z : (D.fm u).ptLat.V), z ∈ locW D.what₂.places w (D.fm u).ptLat.L ∧
    (D.fm u).ptEmb (a • z) = GlobalTheory.Core.Rk.PsiC (D.mem u).C (D.mem u).A (D.mem u).P (D.eMu u (D.jN u φ)) ∧
    (a = 0 ∨ s ≤ (vAdd (D.plEq w) a : ℝ))

end GlobalTheory.Core.Int
