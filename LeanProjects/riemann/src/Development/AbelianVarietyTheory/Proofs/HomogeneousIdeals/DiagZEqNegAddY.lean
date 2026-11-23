import Mathlib

open WeierstrassCurve WeierstrassCurve.Projective

namespace GlobalTheory.AddLaw

variable {R S : Type*} [CommRing R] [CommRing S]

def diagX (W : Projective R) (P Q : Fin 3 → R) : R :=
  -W.a₁ * W.a₂ * P 0 ^ 2 * Q 0 ^ 2 + W.a₁ ^ 2 * P 0 * P 1 * Q 0 ^ 2
    - W.a₂ * P 0 * P 1 * Q 0 ^ 2 + W.a₁ * P 1 ^ 2 * Q 0 ^ 2 - W.a₂ * W.a₃ * P 0 * P 2 * Q 0 ^ 2
    - W.a₁ * W.a₄ * P 0 * P 2 * Q 0 ^ 2 + W.a₁ * W.a₃ * P 1 * P 2 * Q 0 ^ 2
    - W.a₄ * P 1 * P 2 * Q 0 ^ 2 - W.a₃ * W.a₄ * P 2 ^ 2 * Q 0 ^ 2 - W.a₂ * P 0 ^ 2 * Q 0 * Q 1
    + 2 * W.a₁ * P 0 * P 1 * Q 0 * Q 1 + P 1 ^ 2 * Q 0 * Q 1 - 2 * W.a₄ * P 0 * P 2 * Q 0 * Q 1
    + 2 * W.a₃ * P 1 * P 2 * Q 0 * Q 1 - 3 * W.a₆ * P 2 ^ 2 * Q 0 * Q 1 + P 0 * P 1 * Q 1 ^ 2
    - W.a₁ ^ 2 * W.a₃ * P 0 ^ 2 * Q 0 * Q 2 - 2 * W.a₁ * W.a₄ * P 0 ^ 2 * Q 0 * Q 2
    - 2 * W.a₄ * P 0 * P 1 * Q 0 * Q 2 + W.a₃ * P 1 ^ 2 * Q 0 * Q 2
    - 2 * W.a₁ * W.a₃ ^ 2 * P 0 * P 2 * Q 0 * Q 2 - 2 * W.a₃ * W.a₄ * P 0 * P 2 * Q 0 * Q 2
    - 6 * W.a₁ * W.a₆ * P 0 * P 2 * Q 0 * Q 2 - 6 * W.a₆ * P 1 * P 2 * Q 0 * Q 2
    - W.a₃ ^ 3 * P 2 ^ 2 * Q 0 * Q 2 - 6 * W.a₃ * W.a₆ * P 2 ^ 2 * Q 0 * Q 2
    - W.a₁ * W.a₃ * P 0 ^ 2 * Q 1 * Q 2 - W.a₄ * P 0 ^ 2 * Q 1 * Q 2
    - 2 * W.a₃ ^ 2 * P 0 * P 2 * Q 1 * Q 2 - 6 * W.a₆ * P 0 * P 2 * Q 1 * Q 2
    - W.a₂ * W.a₃ ^ 2 * P 2 ^ 2 * Q 1 * Q 2 + W.a₁ * W.a₃ * W.a₄ * P 2 ^ 2 * Q 1 * Q 2
    + W.a₄ ^ 2 * P 2 ^ 2 * Q 1 * Q 2 - W.a₁ ^ 2 * W.a₆ * P 2 ^ 2 * Q 1 * Q 2
    - 4 * W.a₂ * W.a₆ * P 2 ^ 2 * Q 1 * Q 2 - W.a₁ * W.a₃ ^ 2 * P 0 ^ 2 * Q 2 ^ 2
    - 3 * W.a₁ * W.a₆ * P 0 ^ 2 * Q 2 ^ 2 - W.a₃ ^ 2 * P 0 * P 1 * Q 2 ^ 2
    - 3 * W.a₆ * P 0 * P 1 * Q 2 ^ 2 - W.a₁ * W.a₂ * W.a₃ ^ 2 * P 0 * P 2 * Q 2 ^ 2
    - W.a₃ ^ 3 * P 0 * P 2 * Q 2 ^ 2 + W.a₁ ^ 2 * W.a₃ * W.a₄ * P 0 * P 2 * Q 2 ^ 2
    + W.a₁ * W.a₄ ^ 2 * P 0 * P 2 * Q 2 ^ 2 - W.a₁ ^ 3 * W.a₆ * P 0 * P 2 * Q 2 ^ 2
    - 4 * W.a₁ * W.a₂ * W.a₆ * P 0 * P 2 * Q 2 ^ 2 - 3 * W.a₃ * W.a₆ * P 0 * P 2 * Q 2 ^ 2
    - W.a₂ * W.a₃ ^ 2 * P 1 * P 2 * Q 2 ^ 2 + W.a₁ * W.a₃ * W.a₄ * P 1 * P 2 * Q 2 ^ 2
    + W.a₄ ^ 2 * P 1 * P 2 * Q 2 ^ 2 - W.a₁ ^ 2 * W.a₆ * P 1 * P 2 * Q 2 ^ 2
    - 4 * W.a₂ * W.a₆ * P 1 * P 2 * Q 2 ^ 2 - W.a₂ * W.a₃ ^ 3 * P 2 ^ 2 * Q 2 ^ 2
    + W.a₁ * W.a₃ ^ 2 * W.a₄ * P 2 ^ 2 * Q 2 ^ 2 + W.a₃ * W.a₄ ^ 2 * P 2 ^ 2 * Q 2 ^ 2
    - W.a₁ ^ 2 * W.a₃ * W.a₆ * P 2 ^ 2 * Q 2 ^ 2 - 4 * W.a₂ * W.a₃ * W.a₆ * P 2 ^ 2 * Q 2 ^ 2

def negDiagY (W : Projective R) (P Q : Fin 3 → R) : R :=
  W.a₁ ^ 2 * W.a₂ * P 0 ^ 2 * Q 0 ^ 2 + W.a₂ ^ 2 * P 0 ^ 2 * Q 0 ^ 2
    - 3 * W.a₁ * W.a₃ * P 0 ^ 2 * Q 0 ^ 2 - 3 * W.a₄ * P 0 ^ 2 * Q 0 ^ 2
    - W.a₁ ^ 3 * P 0 * P 1 * Q 0 ^ 2 - W.a₁ ^ 2 * P 1 ^ 2 * Q 0 ^ 2
    - 3 * W.a₃ ^ 2 * P 0 * P 2 * Q 0 ^ 2 + W.a₁ ^ 2 * W.a₄ * P 0 * P 2 * Q 0 ^ 2
    + W.a₂ * W.a₄ * P 0 * P 2 * Q 0 ^ 2 - 9 * W.a₆ * P 0 * P 2 * Q 0 ^ 2
    - W.a₁ ^ 2 * W.a₃ * P 1 * P 2 * Q 0 ^ 2 - W.a₂ * W.a₃ ^ 2 * P 2 ^ 2 * Q 0 ^ 2
    + W.a₁ * W.a₃ * W.a₄ * P 2 ^ 2 * Q 0 ^ 2 + W.a₄ ^ 2 * P 2 ^ 2 * Q 0 ^ 2
    - 3 * W.a₂ * W.a₆ * P 2 ^ 2 * Q 0 ^ 2 + W.a₁ * W.a₂ * P 0 ^ 2 * Q 0 * Q 1
    - 3 * W.a₃ * P 0 ^ 2 * Q 0 * Q 1 - 2 * W.a₁ ^ 2 * P 0 * P 1 * Q 0 * Q 1
    - 2 * W.a₁ * P 1 ^ 2 * Q 0 * Q 1 - 2 * W.a₂ * W.a₃ * P 0 * P 2 * Q 0 * Q 1
    + 2 * W.a₁ * W.a₄ * P 0 * P 2 * Q 0 * Q 1 - 2 * W.a₁ * W.a₃ * P 1 * P 2 * Q 0 * Q 1
    - W.a₃ * W.a₄ * P 2 ^ 2 * Q 0 * Q 1 + 3 * W.a₁ * W.a₆ * P 2 ^ 2 * Q 0 * Q 1
    - W.a₁ * P 0 * P 1 * Q 1 ^ 2 - P 1 ^ 2 * Q 1 ^ 2 - W.a₃ * P 1 * P 2 * Q 1 ^ 2
    - 3 * W.a₃ ^ 2 * P 0 ^ 2 * Q 0 * Q 2 + W.a₁ ^ 2 * W.a₄ * P 0 ^ 2 * Q 0 * Q 2
    + W.a₂ * W.a₄ * P 0 ^ 2 * Q 0 * Q 2 - 9 * W.a₆ * P 0 ^ 2 * Q 0 * Q 2
    - 2 * W.a₁ ^ 2 * W.a₃ * P 0 * P 1 * Q 0 * Q 2 - 2 * W.a₁ * W.a₃ * P 1 ^ 2 * Q 0 * Q 2
    - 4 * W.a₂ * W.a₃ ^ 2 * P 0 * P 2 * Q 0 * Q 2
    + 4 * W.a₁ * W.a₃ * W.a₄ * P 0 * P 2 * Q 0 * Q 2 + 4 * W.a₄ ^ 2 * P 0 * P 2 * Q 0 * Q 2
    - 12 * W.a₂ * W.a₆ * P 0 * P 2 * Q 0 * Q 2 - 2 * W.a₁ * W.a₃ ^ 2 * P 1 * P 2 * Q 0 * Q 2
    - W.a₂ ^ 2 * W.a₃ ^ 2 * P 2 ^ 2 * Q 0 * Q 2
    + W.a₁ * W.a₂ * W.a₃ * W.a₄ * P 2 ^ 2 * Q 0 * Q 2 + W.a₂ * W.a₄ ^ 2 * P 2 ^ 2 * Q 0 * Q 2
    - W.a₁ ^ 2 * W.a₂ * W.a₆ * P 2 ^ 2 * Q 0 * Q 2 - 4 * W.a₂ ^ 2 * W.a₆ * P 2 ^ 2 * Q 0 * Q 2
    + 3 * W.a₁ * W.a₃ * W.a₆ * P 2 ^ 2 * Q 0 * Q 2 + 3 * W.a₄ * W.a₆ * P 2 ^ 2 * Q 0 * Q 2
    - W.a₂ * W.a₃ * P 0 ^ 2 * Q 1 * Q 2 + W.a₁ * W.a₄ * P 0 ^ 2 * Q 1 * Q 2
    - 2 * W.a₁ * W.a₃ * P 0 * P 1 * Q 1 * Q 2 - 2 * W.a₃ * P 1 ^ 2 * Q 1 * Q 2
    - 2 * W.a₃ * W.a₄ * P 0 * P 2 * Q 1 * Q 2 + 6 * W.a₁ * W.a₆ * P 0 * P 2 * Q 1 * Q 2
    - 2 * W.a₃ ^ 2 * P 1 * P 2 * Q 1 * Q 2 + W.a₁ * W.a₂ * W.a₃ ^ 2 * P 2 ^ 2 * Q 1 * Q 2
    - W.a₃ ^ 3 * P 2 ^ 2 * Q 1 * Q 2 - W.a₁ ^ 2 * W.a₃ * W.a₄ * P 2 ^ 2 * Q 1 * Q 2
    - W.a₁ * W.a₄ ^ 2 * P 2 ^ 2 * Q 1 * Q 2 + W.a₁ ^ 3 * W.a₆ * P 2 ^ 2 * Q 1 * Q 2
    + 4 * W.a₁ * W.a₂ * W.a₆ * P 2 ^ 2 * Q 1 * Q 2 - 3 * W.a₃ * W.a₆ * P 2 ^ 2 * Q 1 * Q 2
    - W.a₂ * W.a₃ ^ 2 * P 0 ^ 2 * Q 2 ^ 2 + W.a₁ * W.a₃ * W.a₄ * P 0 ^ 2 * Q 2 ^ 2
    + W.a₄ ^ 2 * P 0 ^ 2 * Q 2 ^ 2 - 3 * W.a₂ * W.a₆ * P 0 ^ 2 * Q 2 ^ 2
    - W.a₁ * W.a₃ ^ 2 * P 0 * P 1 * Q 2 ^ 2 - W.a₃ ^ 2 * P 1 ^ 2 * Q 2 ^ 2
    - W.a₂ ^ 2 * W.a₃ ^ 2 * P 0 * P 2 * Q 2 ^ 2
    + W.a₁ * W.a₂ * W.a₃ * W.a₄ * P 0 * P 2 * Q 2 ^ 2 + W.a₂ * W.a₄ ^ 2 * P 0 * P 2 * Q 2 ^ 2
    - W.a₁ ^ 2 * W.a₂ * W.a₆ * P 0 * P 2 * Q 2 ^ 2 - 4 * W.a₂ ^ 2 * W.a₆ * P 0 * P 2 * Q 2 ^ 2
    + 3 * W.a₁ * W.a₃ * W.a₆ * P 0 * P 2 * Q 2 ^ 2 + 3 * W.a₄ * W.a₆ * P 0 * P 2 * Q 2 ^ 2
    - W.a₃ ^ 3 * P 1 * P 2 * Q 2 ^ 2 - W.a₂ * W.a₃ ^ 2 * W.a₄ * P 2 ^ 2 * Q 2 ^ 2
    + W.a₁ * W.a₃ * W.a₄ ^ 2 * P 2 ^ 2 * Q 2 ^ 2 + W.a₄ ^ 3 * P 2 ^ 2 * Q 2 ^ 2
    + 3 * W.a₃ ^ 2 * W.a₆ * P 2 ^ 2 * Q 2 ^ 2 - W.a₁ ^ 2 * W.a₄ * W.a₆ * P 2 ^ 2 * Q 2 ^ 2
    - 4 * W.a₂ * W.a₄ * W.a₆ * P 2 ^ 2 * Q 2 ^ 2 + 9 * W.a₆ ^ 2 * P 2 ^ 2 * Q 2 ^ 2

def diagZ (W : Projective R) (P Q : Fin 3 → R) : R :=
  3 * W.a₁ * P 0 ^ 2 * Q 0 ^ 2 + 3 * P 0 * P 1 * Q 0 ^ 2 + W.a₁ * W.a₂ * P 0 * P 2 * Q 0 ^ 2
    + 3 * W.a₃ * P 0 * P 2 * Q 0 ^ 2 + W.a₂ * P 1 * P 2 * Q 0 ^ 2
    + W.a₂ * W.a₃ * P 2 ^ 2 * Q 0 ^ 2 + 3 * P 0 ^ 2 * Q 0 * Q 1
    + 2 * W.a₂ * P 0 * P 2 * Q 0 * Q 1 + W.a₄ * P 2 ^ 2 * Q 0 * Q 1 + P 1 * P 2 * Q 1 ^ 2
    + W.a₁ ^ 3 * P 0 ^ 2 * Q 0 * Q 2 + 2 * W.a₁ * W.a₂ * P 0 ^ 2 * Q 0 * Q 2
    + 2 * W.a₁ ^ 2 * P 0 * P 1 * Q 0 * Q 2 + 2 * W.a₂ * P 0 * P 1 * Q 0 * Q 2
    + W.a₁ * P 1 ^ 2 * Q 0 * Q 2 + 2 * W.a₁ ^ 2 * W.a₃ * P 0 * P 2 * Q 0 * Q 2
    + 2 * W.a₂ * W.a₃ * P 0 * P 2 * Q 0 * Q 2 + 2 * W.a₁ * W.a₄ * P 0 * P 2 * Q 0 * Q 2
    + 2 * W.a₁ * W.a₃ * P 1 * P 2 * Q 0 * Q 2 + 2 * W.a₄ * P 1 * P 2 * Q 0 * Q 2
    + W.a₁ * W.a₃ ^ 2 * P 2 ^ 2 * Q 0 * Q 2 + 2 * W.a₃ * W.a₄ * P 2 ^ 2 * Q 0 * Q 2
    + W.a₁ ^ 2 * P 0 ^ 2 * Q 1 * Q 2 + W.a₂ * P 0 ^ 2 * Q 1 * Q 2
    + 2 * W.a₁ * P 0 * P 1 * Q 1 * Q 2 + P 1 ^ 2 * Q 1 * Q 2
    + 2 * W.a₁ * W.a₃ * P 0 * P 2 * Q 1 * Q 2 + 2 * W.a₄ * P 0 * P 2 * Q 1 * Q 2
    + 2 * W.a₃ * P 1 * P 2 * Q 1 * Q 2 + W.a₃ ^ 2 * P 2 ^ 2 * Q 1 * Q 2
    + 3 * W.a₆ * P 2 ^ 2 * Q 1 * Q 2 + W.a₁ ^ 2 * W.a₃ * P 0 ^ 2 * Q 2 ^ 2
    + W.a₁ * W.a₄ * P 0 ^ 2 * Q 2 ^ 2 + 2 * W.a₁ * W.a₃ * P 0 * P 1 * Q 2 ^ 2
    + W.a₄ * P 0 * P 1 * Q 2 ^ 2 + W.a₃ * P 1 ^ 2 * Q 2 ^ 2
    + 2 * W.a₁ * W.a₃ ^ 2 * P 0 * P 2 * Q 2 ^ 2 + W.a₃ * W.a₄ * P 0 * P 2 * Q 2 ^ 2
    + 3 * W.a₁ * W.a₆ * P 0 * P 2 * Q 2 ^ 2 + 2 * W.a₃ ^ 2 * P 1 * P 2 * Q 2 ^ 2
    + 3 * W.a₆ * P 1 * P 2 * Q 2 ^ 2 + W.a₃ ^ 3 * P 2 ^ 2 * Q 2 ^ 2
    + 3 * W.a₃ * W.a₆ * P 2 ^ 2 * Q 2 ^ 2

def diagY (W : Projective R) (P Q : Fin 3 → R) : R :=
  W.negY ![diagX W P Q, negDiagY W P Q, diagZ W P Q]

def diagXYZ (W : Projective R) (P Q : Fin 3 → R) : Fin 3 → R :=
  ![diagX W P Q, diagY W P Q, diagZ W P Q]

variable {W : Projective R}

lemma diagX_self {P : Fin 3 → R} (hP : W.Equation P) : diagX W P P = W.dblX P := by
  linear_combination (norm := (simp only [diagX, dblX]; ring1))
    (W.a₁ ^ 3 * P 0 + 4 * W.a₁ * W.a₂ * P 0 + 9 * W.a₃ * P 0 + 2 * W.a₁ ^ 2 * P 1
      + 8 * W.a₂ * P 1 + W.a₁ ^ 2 * W.a₃ * P 2 + 4 * W.a₂ * W.a₃ * P 2) * (sub_eq_zero.mpr <| (equation_iff _).mp hP)

lemma negDiagY_self {P : Fin 3 → R} (hP : W.Equation P) : negDiagY W P P = W.negDblY P := by
  linear_combination (norm := (simp only [negDiagY, negDblY]; ring1))
    (2 * W.a₁ ^ 2 * W.a₂ * P 0 + 8 * W.a₂ ^ 2 * P 0 - 6 * W.a₁ * W.a₃ * P 0 + 3 * W.a₄ * P 0
      - W.a₁ ^ 3 * P 1 - 4 * W.a₁ * W.a₂ * P 1 - 6 * W.a₃ * P 1 - 3 * W.a₃ ^ 2 * P 2
      + W.a₁ ^ 2 * W.a₄ * P 2 + 4 * W.a₂ * W.a₄ * P 2 - 9 * W.a₆ * P 2) * (sub_eq_zero.mpr <| (equation_iff _).mp hP)

lemma diagZ_self {P : Fin 3 → R} (hP : W.Equation P) : diagZ W P P = W.dblZ P := by
  linear_combination (norm := (simp only [diagZ, dblZ, negY]; ring1))
    (-3 * W.a₁ * P 0 - 6 * P 1 - 3 * W.a₃ * P 2) * (sub_eq_zero.mpr <| (equation_iff _).mp hP)

lemma diagX_mul_addZ {P Q : Fin 3 → R} (hP : W.Equation P) (hQ : W.Equation Q) :
    diagX W P Q * W.addZ P Q = diagZ W P Q * W.addX P Q := by
  linear_combination (norm := (simp only [diagX, diagZ, addZ, addX]; ring1))
    (-3 * W.a₁ * P 2 * Q 0 ^ 2 * Q 1 ^ 2 - 3 * P 2 * Q 0 * Q 1 ^ 3
      + 3 * W.a₁ ^ 2 * P 1 * Q 0 ^ 3 * Q 2 - W.a₁ ^ 3 * W.a₂ * P 2 * Q 0 ^ 3 * Q 2
      - W.a₁ * W.a₂ ^ 2 * P 2 * Q 0 ^ 3 * Q 2 + 3 * W.a₁ ^ 2 * W.a₃ * P 2 * Q 0 ^ 3 * Q 2
      + 3 * W.a₁ * W.a₄ * P 2 * Q 0 ^ 3 * Q 2 - 3 * W.a₁ ^ 2 * P 0 * Q 0 ^ 2 * Q 1 * Q 2
      - 3 * W.a₁ * P 1 * Q 0 ^ 2 * Q 1 * Q 2 + W.a₁ ^ 2 * W.a₂ * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      + W.a₂ ^ 2 * P 2 * Q 0 ^ 2 * Q 1 * Q 2 - 6 * W.a₁ * W.a₃ * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      - 3 * W.a₄ * P 2 * Q 0 ^ 2 * Q 1 * Q 2 - 3 * W.a₁ * P 0 * Q 0 * Q 1 ^ 2 * Q 2
      - 3 * P 1 * Q 0 * Q 1 ^ 2 * Q 2 - W.a₁ ^ 3 * P 2 * Q 0 * Q 1 ^ 2 * Q 2
      - W.a₁ * W.a₂ * P 2 * Q 0 * Q 1 ^ 2 * Q 2 - 6 * W.a₃ * P 2 * Q 0 * Q 1 ^ 2 * Q 2
      - W.a₁ ^ 2 * P 2 * Q 1 ^ 3 * Q 2 - W.a₂ * P 2 * Q 1 ^ 3 * Q 2
      + W.a₁ ^ 3 * W.a₂ * P 0 * Q 0 ^ 2 * Q 2 ^ 2 + W.a₁ * W.a₂ ^ 2 * P 0 * Q 0 ^ 2 * Q 2 ^ 2
      - 3 * W.a₁ ^ 2 * W.a₃ * P 0 * Q 0 ^ 2 * Q 2 ^ 2 - 3 * W.a₁ * W.a₄ * P 0 * Q 0 ^ 2 * Q 2 ^ 2
      + 4 * W.a₁ ^ 2 * W.a₂ * P 1 * Q 0 ^ 2 * Q 2 ^ 2 + W.a₂ ^ 2 * P 1 * Q 0 ^ 2 * Q 2 ^ 2
      - 3 * W.a₁ * W.a₃ * P 1 * Q 0 ^ 2 * Q 2 ^ 2 - 3 * W.a₄ * P 1 * Q 0 ^ 2 * Q 2 ^ 2
      - W.a₁ ^ 3 * W.a₂ ^ 2 * P 2 * Q 0 ^ 2 * Q 2 ^ 2 - W.a₁ * W.a₂ ^ 3 * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      + 4 * W.a₁ ^ 2 * W.a₂ * W.a₃ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      + W.a₂ ^ 2 * W.a₃ * P 2 * Q 0 ^ 2 * Q 2 ^ 2 - 3 * W.a₁ * W.a₃ ^ 2 * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      + 3 * W.a₁ * W.a₂ * W.a₄ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      - 3 * W.a₃ * W.a₄ * P 2 * Q 0 ^ 2 * Q 2 ^ 2 - W.a₁ ^ 4 * P 0 * Q 0 * Q 1 * Q 2 ^ 2
      - W.a₁ ^ 2 * W.a₂ * P 0 * Q 0 * Q 1 * Q 2 ^ 2 - 3 * W.a₁ * W.a₃ * P 0 * Q 0 * Q 1 * Q 2 ^ 2
      - 4 * W.a₁ ^ 3 * P 1 * Q 0 * Q 1 * Q 2 ^ 2 - W.a₁ * W.a₂ * P 1 * Q 0 * Q 1 * Q 2 ^ 2
      - 3 * W.a₃ * P 1 * Q 0 * Q 1 * Q 2 ^ 2 + W.a₁ ^ 4 * W.a₂ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      + W.a₁ ^ 2 * W.a₂ ^ 2 * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 4 * W.a₁ ^ 3 * W.a₃ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - W.a₁ * W.a₂ * W.a₃ * P 2 * Q 0 * Q 1 * Q 2 ^ 2 - 6 * W.a₃ ^ 2 * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 2 * W.a₁ ^ 2 * W.a₄ * P 2 * Q 0 * Q 1 * Q 2 ^ 2 + W.a₂ * W.a₄ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 9 * W.a₆ * P 2 * Q 0 * Q 1 * Q 2 ^ 2 - W.a₁ ^ 3 * P 0 * Q 1 ^ 2 * Q 2 ^ 2
      - W.a₁ * W.a₂ * P 0 * Q 1 ^ 2 * Q 2 ^ 2 - 4 * W.a₁ ^ 2 * P 1 * Q 1 ^ 2 * Q 2 ^ 2
      - W.a₂ * P 1 * Q 1 ^ 2 * Q 2 ^ 2 + W.a₁ ^ 3 * W.a₂ * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      + W.a₁ * W.a₂ ^ 2 * P 2 * Q 1 ^ 2 * Q 2 ^ 2 - 5 * W.a₁ ^ 2 * W.a₃ * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      - 2 * W.a₂ * W.a₃ * P 2 * Q 1 ^ 2 * Q 2 ^ 2 - 3 * W.a₁ * W.a₄ * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      - 3 * W.a₁ * W.a₃ ^ 2 * P 0 * Q 0 * Q 2 ^ 3 + W.a₁ ^ 3 * W.a₄ * P 0 * Q 0 * Q 2 ^ 3
      + W.a₁ * W.a₂ * W.a₄ * P 0 * Q 0 * Q 2 ^ 3 - 9 * W.a₁ * W.a₆ * P 0 * Q 0 * Q 2 ^ 3
      - 3 * W.a₃ ^ 2 * P 1 * Q 0 * Q 2 ^ 3 + 4 * W.a₁ ^ 2 * W.a₄ * P 1 * Q 0 * Q 2 ^ 3
      + W.a₂ * W.a₄ * P 1 * Q 0 * Q 2 ^ 3 - 9 * W.a₆ * P 1 * Q 0 * Q 2 ^ 3
      - 3 * W.a₃ ^ 3 * P 2 * Q 0 * Q 2 ^ 3 - W.a₁ ^ 3 * W.a₂ * W.a₄ * P 2 * Q 0 * Q 2 ^ 3
      - W.a₁ * W.a₂ ^ 2 * W.a₄ * P 2 * Q 0 * Q 2 ^ 3
      + 4 * W.a₁ ^ 2 * W.a₃ * W.a₄ * P 2 * Q 0 * Q 2 ^ 3
      + W.a₂ * W.a₃ * W.a₄ * P 2 * Q 0 * Q 2 ^ 3 + 3 * W.a₁ * W.a₄ ^ 2 * P 2 * Q 0 * Q 2 ^ 3
      - 9 * W.a₃ * W.a₆ * P 2 * Q 0 * Q 2 ^ 3 - W.a₁ ^ 3 * W.a₃ * P 0 * Q 1 * Q 2 ^ 3
      - W.a₁ * W.a₂ * W.a₃ * P 0 * Q 1 * Q 2 ^ 3 - 4 * W.a₁ ^ 2 * W.a₃ * P 1 * Q 1 * Q 2 ^ 3
      - W.a₂ * W.a₃ * P 1 * Q 1 * Q 2 ^ 3 + W.a₁ ^ 3 * W.a₂ * W.a₃ * P 2 * Q 1 * Q 2 ^ 3
      + W.a₁ * W.a₂ ^ 2 * W.a₃ * P 2 * Q 1 * Q 2 ^ 3
      - 4 * W.a₁ ^ 2 * W.a₃ ^ 2 * P 2 * Q 1 * Q 2 ^ 3 - 2 * W.a₂ * W.a₃ ^ 2 * P 2 * Q 1 * Q 2 ^ 3
      - 2 * W.a₁ * W.a₃ * W.a₄ * P 2 * Q 1 * Q 2 ^ 3 + W.a₄ ^ 2 * P 2 * Q 1 * Q 2 ^ 3
      - 3 * W.a₂ * W.a₆ * P 2 * Q 1 * Q 2 ^ 3 - W.a₁ * W.a₂ * W.a₃ ^ 2 * P 0 * Q 2 ^ 4
      + W.a₁ ^ 2 * W.a₃ * W.a₄ * P 0 * Q 2 ^ 4 + W.a₁ * W.a₄ ^ 2 * P 0 * Q 2 ^ 4
      - 3 * W.a₁ * W.a₂ * W.a₆ * P 0 * Q 2 ^ 4 - W.a₂ * W.a₃ ^ 2 * P 1 * Q 2 ^ 4
      + W.a₁ * W.a₃ * W.a₄ * P 1 * Q 2 ^ 4 + W.a₄ ^ 2 * P 1 * Q 2 ^ 4
      + 3 * W.a₁ ^ 2 * W.a₆ * P 1 * Q 2 ^ 4 - 3 * W.a₂ * W.a₆ * P 1 * Q 2 ^ 4
      - W.a₂ * W.a₃ ^ 3 * P 2 * Q 2 ^ 4 + W.a₁ * W.a₃ ^ 2 * W.a₄ * P 2 * Q 2 ^ 4
      + W.a₃ * W.a₄ ^ 2 * P 2 * Q 2 ^ 4 - W.a₁ ^ 3 * W.a₂ * W.a₆ * P 2 * Q 2 ^ 4
      - W.a₁ * W.a₂ ^ 2 * W.a₆ * P 2 * Q 2 ^ 4 + 3 * W.a₁ ^ 2 * W.a₃ * W.a₆ * P 2 * Q 2 ^ 4
      - 3 * W.a₂ * W.a₃ * W.a₆ * P 2 * Q 2 ^ 4 + 3 * W.a₁ * W.a₄ * W.a₆ * P 2 * Q 2 ^ 4) * (sub_eq_zero.mpr <| (equation_iff _).mp hP)
    + (3 * W.a₁ * P 0 ^ 2 * P 1 * P 2 * Q 1 + 3 * P 0 * P 1 ^ 2 * P 2 * Q 1
      - W.a₁ ^ 2 * W.a₂ * P 0 ^ 2 * P 2 ^ 2 * Q 1 - W.a₂ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 1
      + 3 * W.a₁ * W.a₃ * P 0 ^ 2 * P 2 ^ 2 * Q 1 + 3 * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 1
      + W.a₁ ^ 3 * P 0 * P 1 * P 2 ^ 2 * Q 1 + W.a₁ * W.a₂ * P 0 * P 1 * P 2 ^ 2 * Q 1
      + 3 * W.a₃ * P 0 * P 1 * P 2 ^ 2 * Q 1 + W.a₁ ^ 2 * P 1 ^ 2 * P 2 ^ 2 * Q 1
      + W.a₂ * P 1 ^ 2 * P 2 ^ 2 * Q 1 + 3 * W.a₃ ^ 2 * P 0 * P 2 ^ 3 * Q 1
      - W.a₁ ^ 2 * W.a₄ * P 0 * P 2 ^ 3 * Q 1 - W.a₂ * W.a₄ * P 0 * P 2 ^ 3 * Q 1
      + 9 * W.a₆ * P 0 * P 2 ^ 3 * Q 1 + W.a₁ ^ 2 * W.a₃ * P 1 * P 2 ^ 3 * Q 1
      + W.a₂ * W.a₃ * P 1 * P 2 ^ 3 * Q 1 + W.a₂ * W.a₃ ^ 2 * P 2 ^ 4 * Q 1
      - W.a₁ * W.a₃ * W.a₄ * P 2 ^ 4 * Q 1 - W.a₄ ^ 2 * P 2 ^ 4 * Q 1
      + 3 * W.a₂ * W.a₆ * P 2 ^ 4 * Q 1 + 6 * W.a₁ * P 0 ^ 2 * P 1 ^ 2 * Q 2
      + 3 * P 0 * P 1 ^ 3 * Q 2 + W.a₁ ^ 4 * P 0 ^ 2 * P 1 * P 2 * Q 2
      - 3 * W.a₁ ^ 2 * W.a₂ * P 0 ^ 2 * P 1 * P 2 * Q 2 - W.a₂ ^ 2 * P 0 ^ 2 * P 1 * P 2 * Q 2
      + 9 * W.a₁ * W.a₃ * P 0 ^ 2 * P 1 * P 2 * Q 2 + 3 * W.a₄ * P 0 ^ 2 * P 1 * P 2 * Q 2
      + 5 * W.a₁ ^ 3 * P 0 * P 1 ^ 2 * P 2 * Q 2 + 2 * W.a₁ * W.a₂ * P 0 * P 1 ^ 2 * P 2 * Q 2
      + 6 * W.a₃ * P 0 * P 1 ^ 2 * P 2 * Q 2 + 4 * W.a₁ ^ 2 * P 1 ^ 3 * P 2 * Q 2
      + W.a₂ * P 1 ^ 3 * P 2 * Q 2 + W.a₁ ^ 3 * W.a₂ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 2
      + W.a₁ * W.a₂ ^ 3 * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - 4 * W.a₁ ^ 2 * W.a₂ * W.a₃ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - W.a₂ ^ 2 * W.a₃ * P 0 ^ 2 * P 2 ^ 2 * Q 2 + 6 * W.a₁ * W.a₃ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - W.a₁ ^ 3 * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - 4 * W.a₁ * W.a₂ * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      + 3 * W.a₃ * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 2 + 9 * W.a₁ * W.a₆ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - W.a₁ ^ 4 * W.a₂ * P 0 * P 1 * P 2 ^ 2 * Q 2
      - W.a₁ ^ 2 * W.a₂ ^ 2 * P 0 * P 1 * P 2 ^ 2 * Q 2
      + 5 * W.a₁ ^ 3 * W.a₃ * P 0 * P 1 * P 2 ^ 2 * Q 2
      + 2 * W.a₁ * W.a₂ * W.a₃ * P 0 * P 1 * P 2 ^ 2 * Q 2
      + 6 * W.a₃ ^ 2 * P 0 * P 1 * P 2 ^ 2 * Q 2 - W.a₁ ^ 2 * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 2
      - W.a₂ * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 2 + 9 * W.a₆ * P 0 * P 1 * P 2 ^ 2 * Q 2
      - W.a₁ ^ 3 * W.a₂ * P 1 ^ 2 * P 2 ^ 2 * Q 2 - W.a₁ * W.a₂ ^ 2 * P 1 ^ 2 * P 2 ^ 2 * Q 2
      + 8 * W.a₁ ^ 2 * W.a₃ * P 1 ^ 2 * P 2 ^ 2 * Q 2 + 2 * W.a₂ * W.a₃ * P 1 ^ 2 * P 2 ^ 2 * Q 2
      + 3 * W.a₁ * W.a₄ * P 1 ^ 2 * P 2 ^ 2 * Q 2 + W.a₁ * W.a₂ * W.a₃ ^ 2 * P 0 * P 2 ^ 3 * Q 2
      + 3 * W.a₃ ^ 3 * P 0 * P 2 ^ 3 * Q 2 + W.a₁ ^ 3 * W.a₂ * W.a₄ * P 0 * P 2 ^ 3 * Q 2
      + W.a₁ * W.a₂ ^ 2 * W.a₄ * P 0 * P 2 ^ 3 * Q 2
      - 5 * W.a₁ ^ 2 * W.a₃ * W.a₄ * P 0 * P 2 ^ 3 * Q 2
      - W.a₂ * W.a₃ * W.a₄ * P 0 * P 2 ^ 3 * Q 2 - 4 * W.a₁ * W.a₄ ^ 2 * P 0 * P 2 ^ 3 * Q 2
      + 3 * W.a₁ * W.a₂ * W.a₆ * P 0 * P 2 ^ 3 * Q 2 + 9 * W.a₃ * W.a₆ * P 0 * P 2 ^ 3 * Q 2
      - W.a₁ ^ 3 * W.a₂ * W.a₃ * P 1 * P 2 ^ 3 * Q 2
      - W.a₁ * W.a₂ ^ 2 * W.a₃ * P 1 * P 2 ^ 3 * Q 2
      + 4 * W.a₁ ^ 2 * W.a₃ ^ 2 * P 1 * P 2 ^ 3 * Q 2 + 2 * W.a₂ * W.a₃ ^ 2 * P 1 * P 2 ^ 3 * Q 2
      + 2 * W.a₁ * W.a₃ * W.a₄ * P 1 * P 2 ^ 3 * Q 2 - W.a₄ ^ 2 * P 1 * P 2 ^ 3 * Q 2
      - 3 * W.a₁ ^ 2 * W.a₆ * P 1 * P 2 ^ 3 * Q 2 + 3 * W.a₂ * W.a₆ * P 1 * P 2 ^ 3 * Q 2
      + W.a₂ * W.a₃ ^ 3 * P 2 ^ 4 * Q 2 - W.a₁ * W.a₃ ^ 2 * W.a₄ * P 2 ^ 4 * Q 2
      - W.a₃ * W.a₄ ^ 2 * P 2 ^ 4 * Q 2 + W.a₁ ^ 3 * W.a₂ * W.a₆ * P 2 ^ 4 * Q 2
      + W.a₁ * W.a₂ ^ 2 * W.a₆ * P 2 ^ 4 * Q 2 - 3 * W.a₁ ^ 2 * W.a₃ * W.a₆ * P 2 ^ 4 * Q 2
      + 3 * W.a₂ * W.a₃ * W.a₆ * P 2 ^ 4 * Q 2 - 3 * W.a₁ * W.a₄ * W.a₆ * P 2 ^ 4 * Q 2) * (sub_eq_zero.mpr <| (equation_iff _).mp hQ)

lemma negDiagY_mul_addZ {P Q : Fin 3 → R} (hP : W.Equation P) (hQ : W.Equation Q) :
    negDiagY W P Q * W.addZ P Q = diagZ W P Q * W.negAddY P Q := by
  linear_combination (norm := (simp only [negDiagY, diagZ, addZ, negAddY]; ring1))
    (9 * W.a₁ * P 1 * Q 0 ^ 4 - 3 * W.a₁ ^ 2 * W.a₂ * P 2 * Q 0 ^ 4
      - 3 * W.a₂ ^ 2 * P 2 * Q 0 ^ 4 + 9 * W.a₁ * W.a₃ * P 2 * Q 0 ^ 4 + 9 * W.a₄ * P 2 * Q 0 ^ 4
      - 9 * W.a₁ * P 0 * Q 0 ^ 3 * Q 1 - 3 * W.a₁ * W.a₂ * P 2 * Q 0 ^ 3 * Q 1
      - 9 * P 0 * Q 0 ^ 2 * Q 1 ^ 2 + 3 * W.a₁ ^ 2 * P 2 * Q 0 ^ 2 * Q 1 ^ 2
      - 3 * W.a₂ * P 2 * Q 0 ^ 2 * Q 1 ^ 2 + 3 * W.a₁ * P 2 * Q 0 * Q 1 ^ 3
      + 3 * W.a₁ ^ 2 * W.a₂ * P 0 * Q 0 ^ 3 * Q 2 + 3 * W.a₂ ^ 2 * P 0 * Q 0 ^ 3 * Q 2
      - 9 * W.a₁ * W.a₃ * P 0 * Q 0 ^ 3 * Q 2 - 9 * W.a₄ * P 0 * Q 0 ^ 3 * Q 2
      + 12 * W.a₁ * W.a₂ * P 1 * Q 0 ^ 3 * Q 2 - 3 * W.a₁ ^ 2 * W.a₂ ^ 2 * P 2 * Q 0 ^ 3 * Q 2
      - 3 * W.a₂ ^ 3 * P 2 * Q 0 ^ 3 * Q 2 + 9 * W.a₁ * W.a₂ * W.a₃ * P 2 * Q 0 ^ 3 * Q 2
      + 9 * W.a₂ * W.a₄ * P 2 * Q 0 ^ 3 * Q 2 - 3 * W.a₁ ^ 3 * P 0 * Q 0 ^ 2 * Q 1 * Q 2
      - 6 * W.a₁ * W.a₂ * P 0 * Q 0 ^ 2 * Q 1 * Q 2 - 9 * W.a₃ * P 0 * Q 0 ^ 2 * Q 1 * Q 2
      - 9 * W.a₁ ^ 2 * P 1 * Q 0 ^ 2 * Q 1 * Q 2 + W.a₁ ^ 3 * W.a₂ * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      + W.a₁ * W.a₂ ^ 2 * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      - 6 * W.a₁ ^ 2 * W.a₃ * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      - 3 * W.a₂ * W.a₃ * P 2 * Q 0 ^ 2 * Q 1 * Q 2 - 9 * W.a₁ * W.a₄ * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      - 3 * W.a₁ ^ 2 * P 0 * Q 0 * Q 1 ^ 2 * Q 2 - 6 * W.a₂ * P 0 * Q 0 * Q 1 ^ 2 * Q 2
      - 9 * W.a₁ * P 1 * Q 0 * Q 1 ^ 2 * Q 2 + W.a₁ ^ 4 * P 2 * Q 0 * Q 1 ^ 2 * Q 2
      + 3 * W.a₁ ^ 2 * W.a₂ * P 2 * Q 0 * Q 1 ^ 2 * Q 2 + 2 * W.a₂ ^ 2 * P 2 * Q 0 * Q 1 ^ 2 * Q 2
      - 6 * W.a₁ * W.a₃ * P 2 * Q 0 * Q 1 ^ 2 * Q 2 - 12 * W.a₄ * P 2 * Q 0 * Q 1 ^ 2 * Q 2
      + W.a₁ ^ 3 * P 2 * Q 1 ^ 3 * Q 2 + W.a₁ * W.a₂ * P 2 * Q 1 ^ 3 * Q 2
      + W.a₁ ^ 2 * W.a₂ ^ 2 * P 0 * Q 0 ^ 2 * Q 2 ^ 2 + W.a₂ ^ 3 * P 0 * Q 0 ^ 2 * Q 2 ^ 2
      - 3 * W.a₁ * W.a₂ * W.a₃ * P 0 * Q 0 ^ 2 * Q 2 ^ 2 - 9 * W.a₃ ^ 2 * P 0 * Q 0 ^ 2 * Q 2 ^ 2
      + 3 * W.a₁ ^ 2 * W.a₄ * P 0 * Q 0 ^ 2 * Q 2 ^ 2 - 27 * W.a₆ * P 0 * Q 0 ^ 2 * Q 2 ^ 2
      + 3 * W.a₁ * W.a₂ ^ 2 * P 1 * Q 0 ^ 2 * Q 2 ^ 2 + 9 * W.a₁ * W.a₄ * P 1 * Q 0 ^ 2 * Q 2 ^ 2
      - W.a₁ ^ 2 * W.a₂ ^ 3 * P 2 * Q 0 ^ 2 * Q 2 ^ 2 - W.a₂ ^ 4 * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      + 3 * W.a₁ * W.a₂ ^ 2 * W.a₃ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      - 3 * W.a₂ * W.a₃ ^ 2 * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      - W.a₁ ^ 2 * W.a₂ * W.a₄ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      + 2 * W.a₂ ^ 2 * W.a₄ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      + 6 * W.a₁ * W.a₃ * W.a₄ * P 2 * Q 0 ^ 2 * Q 2 ^ 2 + 6 * W.a₄ ^ 2 * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      - 9 * W.a₂ * W.a₆ * P 2 * Q 0 ^ 2 * Q 2 ^ 2 - W.a₁ ^ 3 * W.a₂ * P 0 * Q 0 * Q 1 * Q 2 ^ 2
      - W.a₁ * W.a₂ ^ 2 * P 0 * Q 0 * Q 1 * Q 2 ^ 2
      - 3 * W.a₁ ^ 2 * W.a₃ * P 0 * Q 0 * Q 1 * Q 2 ^ 2
      - 6 * W.a₂ * W.a₃ * P 0 * Q 0 * Q 1 * Q 2 ^ 2
      - 3 * W.a₁ ^ 2 * W.a₂ * P 1 * Q 0 * Q 1 * Q 2 ^ 2
      - 9 * W.a₁ * W.a₃ * P 1 * Q 0 * Q 1 * Q 2 ^ 2
      + W.a₁ ^ 3 * W.a₂ ^ 2 * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      + W.a₁ * W.a₂ ^ 3 * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - W.a₁ ^ 2 * W.a₂ * W.a₃ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      + 2 * W.a₂ ^ 2 * W.a₃ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 6 * W.a₁ * W.a₃ ^ 2 * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 2 * W.a₁ ^ 3 * W.a₄ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 5 * W.a₁ * W.a₂ * W.a₄ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 12 * W.a₃ * W.a₄ * P 2 * Q 0 * Q 1 * Q 2 ^ 2 + 9 * W.a₁ * W.a₆ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - W.a₁ ^ 2 * W.a₂ * P 0 * Q 1 ^ 2 * Q 2 ^ 2 - W.a₂ ^ 2 * P 0 * Q 1 ^ 2 * Q 2 ^ 2
      - 3 * W.a₁ * W.a₂ * P 1 * Q 1 ^ 2 * Q 2 ^ 2 + W.a₁ ^ 2 * W.a₂ ^ 2 * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      + W.a₂ ^ 3 * P 2 * Q 1 ^ 2 * Q 2 ^ 2 + W.a₁ ^ 3 * W.a₃ * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      - 2 * W.a₁ * W.a₂ * W.a₃ * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      - W.a₁ ^ 2 * W.a₄ * P 2 * Q 1 ^ 2 * Q 2 ^ 2 - 4 * W.a₂ * W.a₄ * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      - 6 * W.a₂ * W.a₃ ^ 2 * P 0 * Q 0 * Q 2 ^ 3 + W.a₁ ^ 2 * W.a₂ * W.a₄ * P 0 * Q 0 * Q 2 ^ 3
      + W.a₂ ^ 2 * W.a₄ * P 0 * Q 0 * Q 2 ^ 3 + 3 * W.a₁ * W.a₃ * W.a₄ * P 0 * Q 0 * Q 2 ^ 3
      + 3 * W.a₄ ^ 2 * P 0 * Q 0 * Q 2 ^ 3 - 18 * W.a₂ * W.a₆ * P 0 * Q 0 * Q 2 ^ 3
      + 3 * W.a₁ * W.a₂ * W.a₄ * P 1 * Q 0 * Q 2 ^ 3 + 9 * W.a₁ * W.a₆ * P 1 * Q 0 * Q 2 ^ 3
      - W.a₂ ^ 2 * W.a₃ ^ 2 * P 2 * Q 0 * Q 2 ^ 3
      - W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₄ * P 2 * Q 0 * Q 2 ^ 3 - W.a₂ ^ 3 * W.a₄ * P 2 * Q 0 * Q 2 ^ 3
      + 4 * W.a₁ * W.a₂ * W.a₃ * W.a₄ * P 2 * Q 0 * Q 2 ^ 3
      - 3 * W.a₃ ^ 2 * W.a₄ * P 2 * Q 0 * Q 2 ^ 3 + W.a₁ ^ 2 * W.a₄ ^ 2 * P 2 * Q 0 * Q 2 ^ 3
      + 5 * W.a₂ * W.a₄ ^ 2 * P 2 * Q 0 * Q 2 ^ 3
      - 3 * W.a₁ ^ 2 * W.a₂ * W.a₆ * P 2 * Q 0 * Q 2 ^ 3
      - 6 * W.a₂ ^ 2 * W.a₆ * P 2 * Q 0 * Q 2 ^ 3 + 9 * W.a₁ * W.a₃ * W.a₆ * P 2 * Q 0 * Q 2 ^ 3
      - W.a₁ ^ 2 * W.a₂ * W.a₃ * P 0 * Q 1 * Q 2 ^ 3 - W.a₂ ^ 2 * W.a₃ * P 0 * Q 1 * Q 2 ^ 3
      - 3 * W.a₁ * W.a₂ * W.a₃ * P 1 * Q 1 * Q 2 ^ 3
      + W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₃ * P 2 * Q 1 * Q 2 ^ 3 + W.a₂ ^ 3 * W.a₃ * P 2 * Q 1 * Q 2 ^ 3
      - 2 * W.a₁ * W.a₂ * W.a₃ ^ 2 * P 2 * Q 1 * Q 2 ^ 3
      - 2 * W.a₁ ^ 2 * W.a₃ * W.a₄ * P 2 * Q 1 * Q 2 ^ 3
      - 4 * W.a₂ * W.a₃ * W.a₄ * P 2 * Q 1 * Q 2 ^ 3 - W.a₁ * W.a₄ ^ 2 * P 2 * Q 1 * Q 2 ^ 3
      + 3 * W.a₁ * W.a₂ * W.a₆ * P 2 * Q 1 * Q 2 ^ 3 - W.a₂ ^ 2 * W.a₃ ^ 2 * P 0 * Q 2 ^ 4
      + W.a₁ * W.a₂ * W.a₃ * W.a₄ * P 0 * Q 2 ^ 4 + W.a₂ * W.a₄ ^ 2 * P 0 * Q 2 ^ 4
      - 3 * W.a₂ ^ 2 * W.a₆ * P 0 * Q 2 ^ 4 + 3 * W.a₁ * W.a₂ * W.a₆ * P 1 * Q 2 ^ 4
      - W.a₂ * W.a₃ ^ 2 * W.a₄ * P 2 * Q 2 ^ 4 + W.a₁ * W.a₃ * W.a₄ ^ 2 * P 2 * Q 2 ^ 4
      + W.a₄ ^ 3 * P 2 * Q 2 ^ 4 - W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₆ * P 2 * Q 2 ^ 4
      - W.a₂ ^ 3 * W.a₆ * P 2 * Q 2 ^ 4 + 3 * W.a₁ * W.a₂ * W.a₃ * W.a₆ * P 2 * Q 2 ^ 4) * (sub_eq_zero.mpr <| (equation_iff _).mp hP)
    + (9 * P 0 ^ 2 * P 1 ^ 2 * Q 0 + 3 * W.a₁ ^ 3 * P 0 ^ 2 * P 1 * P 2 * Q 0
      - 3 * W.a₁ * W.a₂ * P 0 ^ 2 * P 1 * P 2 * Q 0 + 9 * W.a₃ * P 0 ^ 2 * P 1 * P 2 * Q 0
      + 12 * W.a₁ ^ 2 * P 0 * P 1 ^ 2 * P 2 * Q 0 + 6 * W.a₂ * P 0 * P 1 ^ 2 * P 2 * Q 0
      + 9 * W.a₁ * P 1 ^ 3 * P 2 * Q 0 + 2 * W.a₁ ^ 2 * W.a₂ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 0
      + 2 * W.a₂ ^ 3 * P 0 ^ 2 * P 2 ^ 2 * Q 0 - 6 * W.a₁ * W.a₂ * W.a₃ * P 0 ^ 2 * P 2 ^ 2 * Q 0
      + 9 * W.a₃ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 0 - 3 * W.a₁ ^ 2 * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 0
      - 9 * W.a₂ * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 0 + 27 * W.a₆ * P 0 ^ 2 * P 2 ^ 2 * Q 0
      - 2 * W.a₁ ^ 3 * W.a₂ * P 0 * P 1 * P 2 ^ 2 * Q 0
      - 2 * W.a₁ * W.a₂ ^ 2 * P 0 * P 1 * P 2 ^ 2 * Q 0
      + 12 * W.a₁ ^ 2 * W.a₃ * P 0 * P 1 * P 2 ^ 2 * Q 0
      + 6 * W.a₂ * W.a₃ * P 0 * P 1 * P 2 ^ 2 * Q 0
      - 2 * W.a₁ ^ 2 * W.a₂ * P 1 ^ 2 * P 2 ^ 2 * Q 0 - 2 * W.a₂ ^ 2 * P 1 ^ 2 * P 2 ^ 2 * Q 0
      + 18 * W.a₁ * W.a₃ * P 1 ^ 2 * P 2 ^ 2 * Q 0 + 9 * W.a₄ * P 1 ^ 2 * P 2 ^ 2 * Q 0
      + 6 * W.a₂ * W.a₃ ^ 2 * P 0 * P 2 ^ 3 * Q 0
      + 2 * W.a₁ ^ 2 * W.a₂ * W.a₄ * P 0 * P 2 ^ 3 * Q 0
      + 2 * W.a₂ ^ 2 * W.a₄ * P 0 * P 2 ^ 3 * Q 0 - 12 * W.a₁ * W.a₃ * W.a₄ * P 0 * P 2 ^ 3 * Q 0
      - 12 * W.a₄ ^ 2 * P 0 * P 2 ^ 3 * Q 0 + 18 * W.a₂ * W.a₆ * P 0 * P 2 ^ 3 * Q 0
      - 2 * W.a₁ ^ 2 * W.a₂ * W.a₃ * P 1 * P 2 ^ 3 * Q 0
      - 2 * W.a₂ ^ 2 * W.a₃ * P 1 * P 2 ^ 3 * Q 0 + 9 * W.a₁ * W.a₃ ^ 2 * P 1 * P 2 ^ 3 * Q 0
      + 9 * W.a₃ * W.a₄ * P 1 * P 2 ^ 3 * Q 0 - 9 * W.a₁ * W.a₆ * P 1 * P 2 ^ 3 * Q 0
      + W.a₂ ^ 2 * W.a₃ ^ 2 * P 2 ^ 4 * Q 0 - W.a₁ * W.a₂ * W.a₃ * W.a₄ * P 2 ^ 4 * Q 0
      - W.a₂ * W.a₄ ^ 2 * P 2 ^ 4 * Q 0 + 3 * W.a₁ ^ 2 * W.a₂ * W.a₆ * P 2 ^ 4 * Q 0
      + 6 * W.a₂ ^ 2 * W.a₆ * P 2 ^ 4 * Q 0 - 9 * W.a₁ * W.a₃ * W.a₆ * P 2 ^ 4 * Q 0
      - 9 * W.a₄ * W.a₆ * P 2 ^ 4 * Q 0 - 3 * W.a₁ ^ 2 * P 0 ^ 2 * P 1 * P 2 * Q 1
      - 3 * W.a₁ * P 0 * P 1 ^ 2 * P 2 * Q 1 + W.a₁ ^ 3 * W.a₂ * P 0 ^ 2 * P 2 ^ 2 * Q 1
      + W.a₁ * W.a₂ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 1 - 3 * W.a₁ ^ 2 * W.a₃ * P 0 ^ 2 * P 2 ^ 2 * Q 1
      - 3 * W.a₁ * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 1 - W.a₁ ^ 4 * P 0 * P 1 * P 2 ^ 2 * Q 1
      - W.a₁ ^ 2 * W.a₂ * P 0 * P 1 * P 2 ^ 2 * Q 1 - 3 * W.a₁ * W.a₃ * P 0 * P 1 * P 2 ^ 2 * Q 1
      - W.a₁ ^ 3 * P 1 ^ 2 * P 2 ^ 2 * Q 1 - W.a₁ * W.a₂ * P 1 ^ 2 * P 2 ^ 2 * Q 1
      - 3 * W.a₁ * W.a₃ ^ 2 * P 0 * P 2 ^ 3 * Q 1 + W.a₁ ^ 3 * W.a₄ * P 0 * P 2 ^ 3 * Q 1
      + W.a₁ * W.a₂ * W.a₄ * P 0 * P 2 ^ 3 * Q 1 - 9 * W.a₁ * W.a₆ * P 0 * P 2 ^ 3 * Q 1
      - W.a₁ ^ 3 * W.a₃ * P 1 * P 2 ^ 3 * Q 1 - W.a₁ * W.a₂ * W.a₃ * P 1 * P 2 ^ 3 * Q 1
      - W.a₁ * W.a₂ * W.a₃ ^ 2 * P 2 ^ 4 * Q 1 + W.a₁ ^ 2 * W.a₃ * W.a₄ * P 2 ^ 4 * Q 1
      + W.a₁ * W.a₄ ^ 2 * P 2 ^ 4 * Q 1 - 3 * W.a₁ * W.a₂ * W.a₆ * P 2 ^ 4 * Q 1
      + 3 * W.a₂ * P 0 ^ 2 * P 1 ^ 2 * Q 2 + W.a₁ ^ 3 * W.a₂ * P 0 ^ 2 * P 1 * P 2 * Q 2
      - 2 * W.a₁ * W.a₂ ^ 2 * P 0 ^ 2 * P 1 * P 2 * Q 2
      + 3 * W.a₂ * W.a₃ * P 0 ^ 2 * P 1 * P 2 * Q 2 + 3 * W.a₁ * W.a₄ * P 0 ^ 2 * P 1 * P 2 * Q 2
      + 4 * W.a₁ ^ 2 * W.a₂ * P 0 * P 1 ^ 2 * P 2 * Q 2 + W.a₂ ^ 2 * P 0 * P 1 ^ 2 * P 2 * Q 2
      + 3 * W.a₄ * P 0 * P 1 ^ 2 * P 2 * Q 2 + 3 * W.a₁ * W.a₂ * P 1 ^ 3 * P 2 * Q 2
      + W.a₁ ^ 2 * W.a₂ ^ 3 * P 0 ^ 2 * P 2 ^ 2 * Q 2 + W.a₂ ^ 4 * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - 3 * W.a₁ * W.a₂ ^ 2 * W.a₃ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      + 3 * W.a₂ * W.a₃ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - 2 * W.a₁ ^ 2 * W.a₂ * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - 5 * W.a₂ ^ 2 * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      + 3 * W.a₁ * W.a₃ * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 2 + 3 * W.a₄ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 2
      + 9 * W.a₂ * W.a₆ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - W.a₁ ^ 3 * W.a₂ ^ 2 * P 0 * P 1 * P 2 ^ 2 * Q 2
      - W.a₁ * W.a₂ ^ 3 * P 0 * P 1 * P 2 ^ 2 * Q 2
      + 4 * W.a₁ ^ 2 * W.a₂ * W.a₃ * P 0 * P 1 * P 2 ^ 2 * Q 2
      + W.a₂ ^ 2 * W.a₃ * P 0 * P 1 * P 2 ^ 2 * Q 2 + W.a₁ ^ 3 * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 2
      + W.a₁ * W.a₂ * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 2
      + 3 * W.a₃ * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 2
      - W.a₁ ^ 2 * W.a₂ ^ 2 * P 1 ^ 2 * P 2 ^ 2 * Q 2 - W.a₂ ^ 3 * P 1 ^ 2 * P 2 ^ 2 * Q 2
      + 6 * W.a₁ * W.a₂ * W.a₃ * P 1 ^ 2 * P 2 ^ 2 * Q 2
      + W.a₁ ^ 2 * W.a₄ * P 1 ^ 2 * P 2 ^ 2 * Q 2 + 4 * W.a₂ * W.a₄ * P 1 ^ 2 * P 2 ^ 2 * Q 2
      + W.a₂ ^ 2 * W.a₃ ^ 2 * P 0 * P 2 ^ 3 * Q 2
      + W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₄ * P 0 * P 2 ^ 3 * Q 2 + W.a₂ ^ 3 * W.a₄ * P 0 * P 2 ^ 3 * Q 2
      - 4 * W.a₁ * W.a₂ * W.a₃ * W.a₄ * P 0 * P 2 ^ 3 * Q 2
      + 3 * W.a₃ ^ 2 * W.a₄ * P 0 * P 2 ^ 3 * Q 2 - W.a₁ ^ 2 * W.a₄ ^ 2 * P 0 * P 2 ^ 3 * Q 2
      - 5 * W.a₂ * W.a₄ ^ 2 * P 0 * P 2 ^ 3 * Q 2 + 3 * W.a₂ ^ 2 * W.a₆ * P 0 * P 2 ^ 3 * Q 2
      + 9 * W.a₄ * W.a₆ * P 0 * P 2 ^ 3 * Q 2 - W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₃ * P 1 * P 2 ^ 3 * Q 2
      - W.a₂ ^ 3 * W.a₃ * P 1 * P 2 ^ 3 * Q 2 + 3 * W.a₁ * W.a₂ * W.a₃ ^ 2 * P 1 * P 2 ^ 3 * Q 2
      + W.a₁ ^ 2 * W.a₃ * W.a₄ * P 1 * P 2 ^ 3 * Q 2
      + 4 * W.a₂ * W.a₃ * W.a₄ * P 1 * P 2 ^ 3 * Q 2
      - 3 * W.a₁ * W.a₂ * W.a₆ * P 1 * P 2 ^ 3 * Q 2 + W.a₂ * W.a₃ ^ 2 * W.a₄ * P 2 ^ 4 * Q 2
      - W.a₁ * W.a₃ * W.a₄ ^ 2 * P 2 ^ 4 * Q 2 - W.a₄ ^ 3 * P 2 ^ 4 * Q 2
      + W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₆ * P 2 ^ 4 * Q 2 + W.a₂ ^ 3 * W.a₆ * P 2 ^ 4 * Q 2
      - 3 * W.a₁ * W.a₂ * W.a₃ * W.a₆ * P 2 ^ 4 * Q 2) * (sub_eq_zero.mpr <| (equation_iff _).mp hQ)

lemma diagX_mul_negAddY {P Q : Fin 3 → R} (hP : W.Equation P) (hQ : W.Equation Q) :
    diagX W P Q * W.negAddY P Q = negDiagY W P Q * W.addX P Q := by
  linear_combination (norm := (simp only [diagX, negDiagY, negAddY, addX]; ring1))
    (3 * W.a₁ * W.a₂ * P 1 * Q 0 ^ 4 - W.a₁ ^ 2 * W.a₂ ^ 2 * P 2 * Q 0 ^ 4
      - W.a₂ ^ 3 * P 2 * Q 0 ^ 4 + 3 * W.a₁ * W.a₂ * W.a₃ * P 2 * Q 0 ^ 4
      + 3 * W.a₂ * W.a₄ * P 2 * Q 0 ^ 4 - 3 * W.a₁ * W.a₂ * P 0 * Q 0 ^ 3 * Q 1
      + 3 * W.a₁ ^ 2 * P 1 * Q 0 ^ 3 * Q 1 - 3 * W.a₁ * W.a₄ * P 2 * Q 0 ^ 3 * Q 1
      - 3 * W.a₂ * P 0 * Q 0 ^ 2 * Q 1 ^ 2 + 6 * W.a₁ * P 1 * Q 0 ^ 2 * Q 1 ^ 2
      + 3 * W.a₁ * W.a₃ * P 2 * Q 0 ^ 2 * Q 1 ^ 2 - 3 * W.a₄ * P 2 * Q 0 ^ 2 * Q 1 ^ 2
      + 3 * P 1 * Q 0 * Q 1 ^ 3 + 3 * W.a₃ * P 2 * Q 0 * Q 1 ^ 3
      + W.a₁ ^ 2 * W.a₂ ^ 2 * P 0 * Q 0 ^ 3 * Q 2 + W.a₂ ^ 3 * P 0 * Q 0 ^ 3 * Q 2
      - 3 * W.a₁ * W.a₂ * W.a₃ * P 0 * Q 0 ^ 3 * Q 2 - 3 * W.a₂ * W.a₄ * P 0 * Q 0 ^ 3 * Q 2
      - W.a₁ ^ 3 * W.a₂ * P 1 * Q 0 ^ 3 * Q 2 + 2 * W.a₁ * W.a₂ ^ 2 * P 1 * Q 0 ^ 3 * Q 2
      + 3 * W.a₁ ^ 2 * W.a₃ * P 1 * Q 0 ^ 3 * Q 2 + 6 * W.a₁ * W.a₄ * P 1 * Q 0 ^ 3 * Q 2
      - W.a₁ ^ 2 * W.a₂ ^ 3 * P 2 * Q 0 ^ 3 * Q 2 - W.a₂ ^ 4 * P 2 * Q 0 ^ 3 * Q 2
      + 3 * W.a₁ * W.a₂ ^ 2 * W.a₃ * P 2 * Q 0 ^ 3 * Q 2
      + 3 * W.a₂ ^ 2 * W.a₄ * P 2 * Q 0 ^ 3 * Q 2 - W.a₁ ^ 3 * W.a₂ * P 0 * Q 0 ^ 2 * Q 1 * Q 2
      - W.a₁ * W.a₂ ^ 2 * P 0 * Q 0 ^ 2 * Q 1 * Q 2 - 3 * W.a₂ * W.a₃ * P 0 * Q 0 ^ 2 * Q 1 * Q 2
      - 3 * W.a₁ * W.a₄ * P 0 * Q 0 ^ 2 * Q 1 * Q 2 + W.a₁ ^ 4 * P 1 * Q 0 ^ 2 * Q 1 * Q 2
      - 3 * W.a₁ ^ 2 * W.a₂ * P 1 * Q 0 ^ 2 * Q 1 * Q 2 - W.a₂ ^ 2 * P 1 * Q 0 ^ 2 * Q 1 * Q 2
      + 9 * W.a₁ * W.a₃ * P 1 * Q 0 ^ 2 * Q 1 * Q 2 + 3 * W.a₄ * P 1 * Q 0 ^ 2 * Q 1 * Q 2
      + W.a₁ ^ 3 * W.a₂ ^ 2 * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      + W.a₁ * W.a₂ ^ 3 * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      - 4 * W.a₁ ^ 2 * W.a₂ * W.a₃ * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      - W.a₂ ^ 2 * W.a₃ * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      + 3 * W.a₁ * W.a₃ ^ 2 * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      - W.a₁ ^ 3 * W.a₄ * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      - 4 * W.a₁ * W.a₂ * W.a₄ * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      - 9 * W.a₁ * W.a₆ * P 2 * Q 0 ^ 2 * Q 1 * Q 2 - W.a₁ ^ 2 * W.a₂ * P 0 * Q 0 * Q 1 ^ 2 * Q 2
      - W.a₂ ^ 2 * P 0 * Q 0 * Q 1 ^ 2 * Q 2 - 3 * W.a₄ * P 0 * Q 0 * Q 1 ^ 2 * Q 2
      + 2 * W.a₁ ^ 3 * P 1 * Q 0 * Q 1 ^ 2 * Q 2 - W.a₁ * W.a₂ * P 1 * Q 0 * Q 1 ^ 2 * Q 2
      + 6 * W.a₃ * P 1 * Q 0 * Q 1 ^ 2 * Q 2 + W.a₁ ^ 2 * W.a₂ ^ 2 * P 2 * Q 0 * Q 1 ^ 2 * Q 2
      + W.a₂ ^ 3 * P 2 * Q 0 * Q 1 ^ 2 * Q 2 + W.a₁ ^ 3 * W.a₃ * P 2 * Q 0 * Q 1 ^ 2 * Q 2
      - 2 * W.a₁ * W.a₂ * W.a₃ * P 2 * Q 0 * Q 1 ^ 2 * Q 2
      + 3 * W.a₃ ^ 2 * P 2 * Q 0 * Q 1 ^ 2 * Q 2 - W.a₁ ^ 2 * W.a₄ * P 2 * Q 0 * Q 1 ^ 2 * Q 2
      - 4 * W.a₂ * W.a₄ * P 2 * Q 0 * Q 1 ^ 2 * Q 2 - 9 * W.a₆ * P 2 * Q 0 * Q 1 ^ 2 * Q 2
      + W.a₁ ^ 2 * P 1 * Q 1 ^ 3 * Q 2 + W.a₂ * P 1 * Q 1 ^ 3 * Q 2
      + W.a₁ ^ 2 * W.a₃ * P 2 * Q 1 ^ 3 * Q 2 + W.a₂ * W.a₃ * P 2 * Q 1 ^ 3 * Q 2
      - 3 * W.a₂ * W.a₃ ^ 2 * P 0 * Q 0 ^ 2 * Q 2 ^ 2
      + 2 * W.a₁ ^ 2 * W.a₂ * W.a₄ * P 0 * Q 0 ^ 2 * Q 2 ^ 2
      + 2 * W.a₂ ^ 2 * W.a₄ * P 0 * Q 0 ^ 2 * Q 2 ^ 2
      - 3 * W.a₁ * W.a₃ * W.a₄ * P 0 * Q 0 ^ 2 * Q 2 ^ 2 - 3 * W.a₄ ^ 2 * P 0 * Q 0 ^ 2 * Q 2 ^ 2
      - 9 * W.a₂ * W.a₆ * P 0 * Q 0 ^ 2 * Q 2 ^ 2
      - W.a₁ ^ 2 * W.a₂ * W.a₃ * P 1 * Q 0 ^ 2 * Q 2 ^ 2
      - W.a₂ ^ 2 * W.a₃ * P 1 * Q 0 ^ 2 * Q 2 ^ 2 + 6 * W.a₁ * W.a₃ ^ 2 * P 1 * Q 0 ^ 2 * Q 2 ^ 2
      - W.a₁ ^ 3 * W.a₄ * P 1 * Q 0 ^ 2 * Q 2 ^ 2
      + 5 * W.a₁ * W.a₂ * W.a₄ * P 1 * Q 0 ^ 2 * Q 2 ^ 2
      + 3 * W.a₃ * W.a₄ * P 1 * Q 0 ^ 2 * Q 2 ^ 2 + 9 * W.a₁ * W.a₆ * P 1 * Q 0 ^ 2 * Q 2 ^ 2
      - 2 * W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₄ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      - 2 * W.a₂ ^ 3 * W.a₄ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      + 6 * W.a₁ * W.a₂ * W.a₃ * W.a₄ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      - 3 * W.a₃ ^ 2 * W.a₄ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      + W.a₁ ^ 2 * W.a₄ ^ 2 * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      + 7 * W.a₂ * W.a₄ ^ 2 * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      + 3 * W.a₁ ^ 2 * W.a₂ * W.a₆ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      + 3 * W.a₂ ^ 2 * W.a₆ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      - 9 * W.a₁ * W.a₃ * W.a₆ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      - 18 * W.a₄ * W.a₆ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      - W.a₁ ^ 2 * W.a₂ * W.a₃ * P 0 * Q 0 * Q 1 * Q 2 ^ 2
      - W.a₂ ^ 2 * W.a₃ * P 0 * Q 0 * Q 1 * Q 2 ^ 2 - W.a₁ ^ 3 * W.a₄ * P 0 * Q 0 * Q 1 * Q 2 ^ 2
      - W.a₁ * W.a₂ * W.a₄ * P 0 * Q 0 * Q 1 * Q 2 ^ 2
      - 3 * W.a₃ * W.a₄ * P 0 * Q 0 * Q 1 * Q 2 ^ 2
      + 2 * W.a₁ ^ 3 * W.a₃ * P 1 * Q 0 * Q 1 * Q 2 ^ 2
      - W.a₁ * W.a₂ * W.a₃ * P 1 * Q 0 * Q 1 * Q 2 ^ 2 + 6 * W.a₃ ^ 2 * P 1 * Q 0 * Q 1 * Q 2 ^ 2
      - 4 * W.a₁ ^ 2 * W.a₄ * P 1 * Q 0 * Q 1 * Q 2 ^ 2 - W.a₂ * W.a₄ * P 1 * Q 0 * Q 1 * Q 2 ^ 2
      + 9 * W.a₆ * P 1 * Q 0 * Q 1 * Q 2 ^ 2
      + W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₃ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      + W.a₂ ^ 3 * W.a₃ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 3 * W.a₁ * W.a₂ * W.a₃ ^ 2 * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      + 3 * W.a₃ ^ 3 * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      + W.a₁ ^ 3 * W.a₂ * W.a₄ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      + W.a₁ * W.a₂ ^ 2 * W.a₄ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 5 * W.a₁ ^ 2 * W.a₃ * W.a₄ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 5 * W.a₂ * W.a₃ * W.a₄ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 3 * W.a₁ * W.a₄ ^ 2 * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 3 * W.a₁ ^ 3 * W.a₆ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 3 * W.a₁ * W.a₂ * W.a₆ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - W.a₁ ^ 2 * W.a₄ * P 0 * Q 1 ^ 2 * Q 2 ^ 2 - W.a₂ * W.a₄ * P 0 * Q 1 ^ 2 * Q 2 ^ 2
      + 2 * W.a₁ ^ 2 * W.a₃ * P 1 * Q 1 ^ 2 * Q 2 ^ 2 + 2 * W.a₂ * W.a₃ * P 1 * Q 1 ^ 2 * Q 2 ^ 2
      - 3 * W.a₁ * W.a₄ * P 1 * Q 1 ^ 2 * Q 2 ^ 2 + W.a₁ ^ 2 * W.a₃ ^ 2 * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      + W.a₂ * W.a₃ ^ 2 * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      + W.a₁ ^ 2 * W.a₂ * W.a₄ * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      + W.a₂ ^ 2 * W.a₄ * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      - 3 * W.a₁ * W.a₃ * W.a₄ * P 2 * Q 1 ^ 2 * Q 2 ^ 2 - 3 * W.a₄ ^ 2 * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      - 3 * W.a₁ ^ 2 * W.a₆ * P 2 * Q 1 ^ 2 * Q 2 ^ 2 - 3 * W.a₂ * W.a₆ * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      - W.a₂ ^ 2 * W.a₃ ^ 2 * P 0 * Q 0 * Q 2 ^ 3
      + W.a₁ * W.a₂ * W.a₃ * W.a₄ * P 0 * Q 0 * Q 2 ^ 3
      - 3 * W.a₃ ^ 2 * W.a₄ * P 0 * Q 0 * Q 2 ^ 3 + W.a₁ ^ 2 * W.a₄ ^ 2 * P 0 * Q 0 * Q 2 ^ 3
      + 2 * W.a₂ * W.a₄ ^ 2 * P 0 * Q 0 * Q 2 ^ 3 - 3 * W.a₂ ^ 2 * W.a₆ * P 0 * Q 0 * Q 2 ^ 3
      - 9 * W.a₄ * W.a₆ * P 0 * Q 0 * Q 2 ^ 3 + W.a₁ * W.a₂ * W.a₃ ^ 2 * P 1 * Q 0 * Q 2 ^ 3
      + 3 * W.a₃ ^ 3 * P 1 * Q 0 * Q 2 ^ 3 - 2 * W.a₁ ^ 2 * W.a₃ * W.a₄ * P 1 * Q 0 * Q 2 ^ 3
      - W.a₂ * W.a₃ * W.a₄ * P 1 * Q 0 * Q 2 ^ 3 + 2 * W.a₁ * W.a₄ ^ 2 * P 1 * Q 0 * Q 2 ^ 3
      + 6 * W.a₁ * W.a₂ * W.a₆ * P 1 * Q 0 * Q 2 ^ 3 + 9 * W.a₃ * W.a₆ * P 1 * Q 0 * Q 2 ^ 3
      - W.a₂ * W.a₃ ^ 2 * W.a₄ * P 2 * Q 0 * Q 2 ^ 3
      - W.a₁ ^ 2 * W.a₂ * W.a₄ ^ 2 * P 2 * Q 0 * Q 2 ^ 3
      - W.a₂ ^ 2 * W.a₄ ^ 2 * P 2 * Q 0 * Q 2 ^ 3
      + 4 * W.a₁ * W.a₃ * W.a₄ ^ 2 * P 2 * Q 0 * Q 2 ^ 3 + 4 * W.a₄ ^ 3 * P 2 * Q 0 * Q 2 ^ 3
      - W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₆ * P 2 * Q 0 * Q 2 ^ 3 - W.a₂ ^ 3 * W.a₆ * P 2 * Q 0 * Q 2 ^ 3
      + 3 * W.a₁ * W.a₂ * W.a₃ * W.a₆ * P 2 * Q 0 * Q 2 ^ 3
      - 9 * W.a₃ ^ 2 * W.a₆ * P 2 * Q 0 * Q 2 ^ 3
      + 3 * W.a₁ ^ 2 * W.a₄ * W.a₆ * P 2 * Q 0 * Q 2 ^ 3
      + 3 * W.a₂ * W.a₄ * W.a₆ * P 2 * Q 0 * Q 2 ^ 3 - 27 * W.a₆ ^ 2 * P 2 * Q 0 * Q 2 ^ 3
      - W.a₁ ^ 2 * W.a₃ * W.a₄ * P 0 * Q 1 * Q 2 ^ 3 - W.a₂ * W.a₃ * W.a₄ * P 0 * Q 1 * Q 2 ^ 3
      + W.a₁ ^ 2 * W.a₃ ^ 2 * P 1 * Q 1 * Q 2 ^ 3 + 2 * W.a₂ * W.a₃ ^ 2 * P 1 * Q 1 * Q 2 ^ 3
      - 4 * W.a₁ * W.a₃ * W.a₄ * P 1 * Q 1 * Q 2 ^ 3 - W.a₄ ^ 2 * P 1 * Q 1 * Q 2 ^ 3
      + 3 * W.a₂ * W.a₆ * P 1 * Q 1 * Q 2 ^ 3 + W.a₂ * W.a₃ ^ 3 * P 2 * Q 1 * Q 2 ^ 3
      + W.a₁ ^ 2 * W.a₂ * W.a₃ * W.a₄ * P 2 * Q 1 * Q 2 ^ 3
      + W.a₂ ^ 2 * W.a₃ * W.a₄ * P 2 * Q 1 * Q 2 ^ 3
      - 4 * W.a₁ * W.a₃ ^ 2 * W.a₄ * P 2 * Q 1 * Q 2 ^ 3
      - 4 * W.a₃ * W.a₄ ^ 2 * P 2 * Q 1 * Q 2 ^ 3
      - 3 * W.a₁ ^ 2 * W.a₃ * W.a₆ * P 2 * Q 1 * Q 2 ^ 3 - W.a₂ * W.a₃ ^ 2 * W.a₄ * P 0 * Q 2 ^ 4
      + W.a₁ * W.a₃ * W.a₄ ^ 2 * P 0 * Q 2 ^ 4 + W.a₄ ^ 3 * P 0 * Q 2 ^ 4
      - 3 * W.a₂ * W.a₄ * W.a₆ * P 0 * Q 2 ^ 4 + W.a₂ * W.a₃ ^ 3 * P 1 * Q 2 ^ 4
      - W.a₁ * W.a₃ ^ 2 * W.a₄ * P 1 * Q 2 ^ 4 - W.a₃ * W.a₄ ^ 2 * P 1 * Q 2 ^ 4
      + 3 * W.a₂ * W.a₃ * W.a₆ * P 1 * Q 2 ^ 4 + 3 * W.a₁ * W.a₄ * W.a₆ * P 1 * Q 2 ^ 4
      - 3 * W.a₂ * W.a₃ ^ 2 * W.a₆ * P 2 * Q 2 ^ 4 - W.a₁ ^ 2 * W.a₂ * W.a₄ * W.a₆ * P 2 * Q 2 ^ 4
      - W.a₂ ^ 2 * W.a₄ * W.a₆ * P 2 * Q 2 ^ 4 + 6 * W.a₁ * W.a₃ * W.a₄ * W.a₆ * P 2 * Q 2 ^ 4
      + 6 * W.a₄ ^ 2 * W.a₆ * P 2 * Q 2 ^ 4 - 9 * W.a₂ * W.a₆ ^ 2 * P 2 * Q 2 ^ 4) * (sub_eq_zero.mpr <| (equation_iff _).mp hP)
    + (-3 * W.a₁ ^ 2 * P 0 ^ 2 * P 1 ^ 2 * Q 0 + 3 * W.a₂ * P 0 ^ 2 * P 1 ^ 2 * Q 0
      - 3 * W.a₁ * P 0 * P 1 ^ 3 * Q 0 + 2 * W.a₁ ^ 3 * W.a₂ * P 0 ^ 2 * P 1 * P 2 * Q 0
      - W.a₁ * W.a₂ ^ 2 * P 0 ^ 2 * P 1 * P 2 * Q 0
      - 3 * W.a₁ ^ 2 * W.a₃ * P 0 ^ 2 * P 1 * P 2 * Q 0
      + 3 * W.a₂ * W.a₃ * P 0 ^ 2 * P 1 * P 2 * Q 0 - W.a₁ ^ 4 * P 0 * P 1 ^ 2 * P 2 * Q 0
      + 3 * W.a₁ ^ 2 * W.a₂ * P 0 * P 1 ^ 2 * P 2 * Q 0 + W.a₂ ^ 2 * P 0 * P 1 ^ 2 * P 2 * Q 0
      - 3 * W.a₁ * W.a₃ * P 0 * P 1 ^ 2 * P 2 * Q 0 + 3 * W.a₄ * P 0 * P 1 ^ 2 * P 2 * Q 0
      - W.a₁ ^ 3 * P 1 ^ 3 * P 2 * Q 0 + 2 * W.a₁ * W.a₂ * P 1 ^ 3 * P 2 * Q 0
      + W.a₁ ^ 2 * W.a₂ ^ 3 * P 0 ^ 2 * P 2 ^ 2 * Q 0 + W.a₂ ^ 4 * P 0 ^ 2 * P 2 ^ 2 * Q 0
      - 3 * W.a₁ * W.a₂ ^ 2 * W.a₃ * P 0 ^ 2 * P 2 ^ 2 * Q 0
      + 3 * W.a₂ * W.a₃ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 0
      - 2 * W.a₁ ^ 2 * W.a₂ * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 0
      - 5 * W.a₂ ^ 2 * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 0
      + 3 * W.a₁ * W.a₃ * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 0 + 3 * W.a₄ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 0
      + 9 * W.a₂ * W.a₆ * P 0 ^ 2 * P 2 ^ 2 * Q 0
      - W.a₁ ^ 3 * W.a₂ ^ 2 * P 0 * P 1 * P 2 ^ 2 * Q 0
      - W.a₁ * W.a₂ ^ 3 * P 0 * P 1 * P 2 ^ 2 * Q 0
      + 4 * W.a₁ ^ 2 * W.a₂ * W.a₃ * P 0 * P 1 * P 2 ^ 2 * Q 0
      + W.a₂ ^ 2 * W.a₃ * P 0 * P 1 * P 2 ^ 2 * Q 0
      - 3 * W.a₁ * W.a₃ ^ 2 * P 0 * P 1 * P 2 ^ 2 * Q 0
      + 2 * W.a₁ ^ 3 * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 0
      + 2 * W.a₁ * W.a₂ * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 0
      + 3 * W.a₃ * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 0 - 9 * W.a₁ * W.a₆ * P 0 * P 1 * P 2 ^ 2 * Q 0
      - W.a₁ ^ 2 * W.a₂ ^ 2 * P 1 ^ 2 * P 2 ^ 2 * Q 0 - W.a₂ ^ 3 * P 1 ^ 2 * P 2 ^ 2 * Q 0
      - W.a₁ ^ 3 * W.a₃ * P 1 ^ 2 * P 2 ^ 2 * Q 0
      + 5 * W.a₁ * W.a₂ * W.a₃ * P 1 ^ 2 * P 2 ^ 2 * Q 0
      + W.a₁ ^ 2 * W.a₄ * P 1 ^ 2 * P 2 ^ 2 * Q 0 + 4 * W.a₂ * W.a₄ * P 1 ^ 2 * P 2 ^ 2 * Q 0
      + W.a₂ ^ 2 * W.a₃ ^ 2 * P 0 * P 2 ^ 3 * Q 0
      + W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₄ * P 0 * P 2 ^ 3 * Q 0 + W.a₂ ^ 3 * W.a₄ * P 0 * P 2 ^ 3 * Q 0
      - 4 * W.a₁ * W.a₂ * W.a₃ * W.a₄ * P 0 * P 2 ^ 3 * Q 0
      + 3 * W.a₃ ^ 2 * W.a₄ * P 0 * P 2 ^ 3 * Q 0 - W.a₁ ^ 2 * W.a₄ ^ 2 * P 0 * P 2 ^ 3 * Q 0
      - 5 * W.a₂ * W.a₄ ^ 2 * P 0 * P 2 ^ 3 * Q 0 + 3 * W.a₂ ^ 2 * W.a₆ * P 0 * P 2 ^ 3 * Q 0
      + 9 * W.a₄ * W.a₆ * P 0 * P 2 ^ 3 * Q 0 - W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₃ * P 1 * P 2 ^ 3 * Q 0
      - W.a₂ ^ 3 * W.a₃ * P 1 * P 2 ^ 3 * Q 0 + 2 * W.a₁ * W.a₂ * W.a₃ ^ 2 * P 1 * P 2 ^ 3 * Q 0
      + 2 * W.a₁ ^ 2 * W.a₃ * W.a₄ * P 1 * P 2 ^ 3 * Q 0
      + 4 * W.a₂ * W.a₃ * W.a₄ * P 1 * P 2 ^ 3 * Q 0 + W.a₁ * W.a₄ ^ 2 * P 1 * P 2 ^ 3 * Q 0
      - 6 * W.a₁ * W.a₂ * W.a₆ * P 1 * P 2 ^ 3 * Q 0 + W.a₂ * W.a₃ ^ 2 * W.a₄ * P 2 ^ 4 * Q 0
      - W.a₁ * W.a₃ * W.a₄ ^ 2 * P 2 ^ 4 * Q 0 - W.a₄ ^ 3 * P 2 ^ 4 * Q 0
      + W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₆ * P 2 ^ 4 * Q 0 + W.a₂ ^ 3 * W.a₆ * P 2 ^ 4 * Q 0
      - 3 * W.a₁ * W.a₂ * W.a₃ * W.a₆ * P 2 ^ 4 * Q 0 - 3 * W.a₁ * P 0 ^ 2 * P 1 ^ 2 * Q 1
      - 3 * P 0 * P 1 ^ 3 * Q 1 + W.a₁ ^ 2 * W.a₂ * P 0 ^ 2 * P 1 * P 2 * Q 1
      + W.a₂ ^ 2 * P 0 ^ 2 * P 1 * P 2 * Q 1 - 6 * W.a₁ * W.a₃ * P 0 ^ 2 * P 1 * P 2 * Q 1
      - 3 * W.a₄ * P 0 ^ 2 * P 1 * P 2 * Q 1 - W.a₁ ^ 3 * P 0 * P 1 ^ 2 * P 2 * Q 1
      - W.a₁ * W.a₂ * P 0 * P 1 ^ 2 * P 2 * Q 1 - 6 * W.a₃ * P 0 * P 1 ^ 2 * P 2 * Q 1
      - W.a₁ ^ 2 * P 1 ^ 3 * P 2 * Q 1 - W.a₂ * P 1 ^ 3 * P 2 * Q 1
      + W.a₁ ^ 2 * W.a₂ * W.a₃ * P 0 ^ 2 * P 2 ^ 2 * Q 1
      + W.a₂ ^ 2 * W.a₃ * P 0 ^ 2 * P 2 ^ 2 * Q 1 - 3 * W.a₁ * W.a₃ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 1
      - 3 * W.a₃ * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 1 - W.a₁ ^ 3 * W.a₃ * P 0 * P 1 * P 2 ^ 2 * Q 1
      - W.a₁ * W.a₂ * W.a₃ * P 0 * P 1 * P 2 ^ 2 * Q 1 - 6 * W.a₃ ^ 2 * P 0 * P 1 * P 2 ^ 2 * Q 1
      + W.a₁ ^ 2 * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 1 + W.a₂ * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 1
      - 9 * W.a₆ * P 0 * P 1 * P 2 ^ 2 * Q 1 - 2 * W.a₁ ^ 2 * W.a₃ * P 1 ^ 2 * P 2 ^ 2 * Q 1
      - 2 * W.a₂ * W.a₃ * P 1 ^ 2 * P 2 ^ 2 * Q 1 - 3 * W.a₃ ^ 3 * P 0 * P 2 ^ 3 * Q 1
      + W.a₁ ^ 2 * W.a₃ * W.a₄ * P 0 * P 2 ^ 3 * Q 1 + W.a₂ * W.a₃ * W.a₄ * P 0 * P 2 ^ 3 * Q 1
      - 9 * W.a₃ * W.a₆ * P 0 * P 2 ^ 3 * Q 1 - W.a₁ ^ 2 * W.a₃ ^ 2 * P 1 * P 2 ^ 3 * Q 1
      - 2 * W.a₂ * W.a₃ ^ 2 * P 1 * P 2 ^ 3 * Q 1 + W.a₁ * W.a₃ * W.a₄ * P 1 * P 2 ^ 3 * Q 1
      + W.a₄ ^ 2 * P 1 * P 2 ^ 3 * Q 1 - 3 * W.a₂ * W.a₆ * P 1 * P 2 ^ 3 * Q 1
      - W.a₂ * W.a₃ ^ 3 * P 2 ^ 4 * Q 1 + W.a₁ * W.a₃ ^ 2 * W.a₄ * P 2 ^ 4 * Q 1
      + W.a₃ * W.a₄ ^ 2 * P 2 ^ 4 * Q 1 - 3 * W.a₂ * W.a₃ * W.a₆ * P 2 ^ 4 * Q 1
      - 3 * W.a₁ * W.a₃ * P 0 ^ 2 * P 1 ^ 2 * Q 2 + 3 * W.a₄ * P 0 ^ 2 * P 1 ^ 2 * Q 2
      - 3 * W.a₃ * P 0 * P 1 ^ 3 * Q 2 + W.a₁ ^ 2 * W.a₂ * W.a₃ * P 0 ^ 2 * P 1 * P 2 * Q 2
      + W.a₂ ^ 2 * W.a₃ * P 0 ^ 2 * P 1 * P 2 * Q 2
      - 3 * W.a₁ * W.a₃ ^ 2 * P 0 ^ 2 * P 1 * P 2 * Q 2
      + W.a₁ ^ 3 * W.a₄ * P 0 ^ 2 * P 1 * P 2 * Q 2
      - 2 * W.a₁ * W.a₂ * W.a₄ * P 0 ^ 2 * P 1 * P 2 * Q 2
      + 9 * W.a₁ * W.a₆ * P 0 ^ 2 * P 1 * P 2 * Q 2 - W.a₁ ^ 3 * W.a₃ * P 0 * P 1 ^ 2 * P 2 * Q 2
      - W.a₁ * W.a₂ * W.a₃ * P 0 * P 1 ^ 2 * P 2 * Q 2 - 3 * W.a₃ ^ 2 * P 0 * P 1 ^ 2 * P 2 * Q 2
      + 4 * W.a₁ ^ 2 * W.a₄ * P 0 * P 1 ^ 2 * P 2 * Q 2 + W.a₂ * W.a₄ * P 0 * P 1 ^ 2 * P 2 * Q 2
      + 9 * W.a₆ * P 0 * P 1 ^ 2 * P 2 * Q 2 - W.a₁ ^ 2 * W.a₃ * P 1 ^ 3 * P 2 * Q 2
      - W.a₂ * W.a₃ * P 1 ^ 3 * P 2 * Q 2 + 3 * W.a₁ * W.a₄ * P 1 ^ 3 * P 2 * Q 2
      + W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      + W.a₂ ^ 3 * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - 3 * W.a₁ * W.a₂ * W.a₃ * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      + 3 * W.a₃ ^ 2 * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - W.a₁ ^ 2 * W.a₄ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - 4 * W.a₂ * W.a₄ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - 3 * W.a₁ ^ 2 * W.a₂ * W.a₆ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - 3 * W.a₂ ^ 2 * W.a₆ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      + 9 * W.a₁ * W.a₃ * W.a₆ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      + 18 * W.a₄ * W.a₆ * P 0 ^ 2 * P 2 ^ 2 * Q 2 - 3 * W.a₃ ^ 3 * P 0 * P 1 * P 2 ^ 2 * Q 2
      - W.a₁ ^ 3 * W.a₂ * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 2
      - W.a₁ * W.a₂ ^ 2 * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 2
      + 5 * W.a₁ ^ 2 * W.a₃ * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 2
      + 2 * W.a₂ * W.a₃ * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 2
      + 3 * W.a₁ ^ 3 * W.a₆ * P 0 * P 1 * P 2 ^ 2 * Q 2
      + 3 * W.a₁ * W.a₂ * W.a₆ * P 0 * P 1 * P 2 ^ 2 * Q 2
      - W.a₁ ^ 2 * W.a₃ ^ 2 * P 1 ^ 2 * P 2 ^ 2 * Q 2 - W.a₂ * W.a₃ ^ 2 * P 1 ^ 2 * P 2 ^ 2 * Q 2
      - W.a₁ ^ 2 * W.a₂ * W.a₄ * P 1 ^ 2 * P 2 ^ 2 * Q 2
      - W.a₂ ^ 2 * W.a₄ * P 1 ^ 2 * P 2 ^ 2 * Q 2
      + 6 * W.a₁ * W.a₃ * W.a₄ * P 1 ^ 2 * P 2 ^ 2 * Q 2 + 3 * W.a₄ ^ 2 * P 1 ^ 2 * P 2 ^ 2 * Q 2
      + 3 * W.a₁ ^ 2 * W.a₆ * P 1 ^ 2 * P 2 ^ 2 * Q 2 + 3 * W.a₂ * W.a₆ * P 1 ^ 2 * P 2 ^ 2 * Q 2
      + W.a₂ * W.a₃ ^ 2 * W.a₄ * P 0 * P 2 ^ 3 * Q 2
      + W.a₁ ^ 2 * W.a₂ * W.a₄ ^ 2 * P 0 * P 2 ^ 3 * Q 2
      + W.a₂ ^ 2 * W.a₄ ^ 2 * P 0 * P 2 ^ 3 * Q 2
      - 4 * W.a₁ * W.a₃ * W.a₄ ^ 2 * P 0 * P 2 ^ 3 * Q 2 - 4 * W.a₄ ^ 3 * P 0 * P 2 ^ 3 * Q 2
      + 9 * W.a₃ ^ 2 * W.a₆ * P 0 * P 2 ^ 3 * Q 2
      - 3 * W.a₁ ^ 2 * W.a₄ * W.a₆ * P 0 * P 2 ^ 3 * Q 2 + 27 * W.a₆ ^ 2 * P 0 * P 2 ^ 3 * Q 2
      - W.a₂ * W.a₃ ^ 3 * P 1 * P 2 ^ 3 * Q 2
      - W.a₁ ^ 2 * W.a₂ * W.a₃ * W.a₄ * P 1 * P 2 ^ 3 * Q 2
      - W.a₂ ^ 2 * W.a₃ * W.a₄ * P 1 * P 2 ^ 3 * Q 2
      + 4 * W.a₁ * W.a₃ ^ 2 * W.a₄ * P 1 * P 2 ^ 3 * Q 2
      + 4 * W.a₃ * W.a₄ ^ 2 * P 1 * P 2 ^ 3 * Q 2
      + 3 * W.a₁ ^ 2 * W.a₃ * W.a₆ * P 1 * P 2 ^ 3 * Q 2
      - 3 * W.a₁ * W.a₄ * W.a₆ * P 1 * P 2 ^ 3 * Q 2 + 3 * W.a₂ * W.a₃ ^ 2 * W.a₆ * P 2 ^ 4 * Q 2
      + W.a₁ ^ 2 * W.a₂ * W.a₄ * W.a₆ * P 2 ^ 4 * Q 2 + W.a₂ ^ 2 * W.a₄ * W.a₆ * P 2 ^ 4 * Q 2
      - 6 * W.a₁ * W.a₃ * W.a₄ * W.a₆ * P 2 ^ 4 * Q 2 - 6 * W.a₄ ^ 2 * W.a₆ * P 2 ^ 4 * Q 2
      + 9 * W.a₂ * W.a₆ ^ 2 * P 2 ^ 4 * Q 2) * (sub_eq_zero.mpr <| (equation_iff _).mp hQ)

lemma diagX_smul (P Q : Fin 3 → R) (u v : R) :
    diagX W (u • P) (v • Q) = (u * v) ^ 2 * diagX W P Q := by
  simp only [diagX, smul_fin3_ext]
  ring1

lemma negDiagY_smul (P Q : Fin 3 → R) (u v : R) :
    negDiagY W (u • P) (v • Q) = (u * v) ^ 2 * negDiagY W P Q := by
  simp only [negDiagY, smul_fin3_ext]
  ring1

lemma diagZ_smul (P Q : Fin 3 → R) (u v : R) :
    diagZ W (u • P) (v • Q) = (u * v) ^ 2 * diagZ W P Q := by
  simp only [diagZ, smul_fin3_ext]
  ring1

lemma map_diagX (f : R →+* S) (P Q : Fin 3 → R) :
    diagX (W.map f) (f ∘ P) (f ∘ Q) = f (diagX W P Q) := by
  simp only [diagX, map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow,
    WeierstrassCurve.map, Function.comp_apply]

lemma map_negDiagY (f : R →+* S) (P Q : Fin 3 → R) :
    negDiagY (W.map f) (f ∘ P) (f ∘ Q) = f (negDiagY W P Q) := by
  simp only [negDiagY, map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow,
    WeierstrassCurve.map, Function.comp_apply]

lemma map_diagZ (f : R →+* S) (P Q : Fin 3 → R) :
    diagZ (W.map f) (f ∘ P) (f ∘ Q) = f (diagZ W P Q) := by
  simp only [diagZ, map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow,
    WeierstrassCurve.map, Function.comp_apply]

end GlobalTheory.AddLaw
