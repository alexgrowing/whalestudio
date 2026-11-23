import Formalism.YangianSpanCharacter.StatementY

namespace Formalism.YangianSpanCharacter.Y

open Matrix Formalism.YangianSpanCharacter.T

def GaussDecomp : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ Y : 𝕜, Y ∈ S → Y + 1 ∈ S →
      t Y = !![1, mf t τinv (Y + 1); 0, 1] * !![q Y • τinv (Y + 1), 0; 0, t Y 1 1] *
        !![1, 0; lf t τinv Y, 1]

def tE (u : ℚ) : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℚ) :=
  !![!![u + 1, 0; 0, u], !![0, 1; 0, 0]; !![0, 0; 1, 0], !![u, 0; 0, u + 1]]

def τE (u : ℚ) : Matrix (Fin 2) (Fin 2) ℚ := !![u⁻¹, 0; 0, (u + 1)⁻¹]

def qE (Y : ℚ) : ℚ := Y * (Y + 2)

def SE : Set ℚ := {u | u ≠ 0 ∧ u + 1 ≠ 0}

def ModHypYangian : Prop :=
  ModHyp tE τE qE SE ∧ tE 0 1 1 ≠ tE 1 1 1 ∧
    tE 0 0 1 * tE 0 1 0 - tE 0 1 0 * tE 0 0 1 ≠ 0 ∧ (1 : ℚ) ∈ SE

end Formalism.YangianSpanCharacter.Y
