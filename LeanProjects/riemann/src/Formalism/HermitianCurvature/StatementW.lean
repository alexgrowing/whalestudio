import Formalism.YangianSpanCharacter.ExchangeGen

namespace Formalism.FourierDecayAlt.W

open Matrix Formalism.YangianSpanCharacter.T NumberField

variable {R B : Type} [CommRing R] [Ring B] [Algebra R B]

def IsRTT (M : R → Matrix (Fin 2) (Fin 2) B) : Prop :=
  ∀ Y Y' : R, ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B) * E1 (M Y') * E2 (M Y) =
    E2 (M Y) * E1 (M Y') * ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B)

def IsDet (M : R → Matrix (Fin 2) (Fin 2) B) (q : R → R) : Prop :=
  ∀ Y : R, (M (Y + 1))ᵀ * Formalism.YangianSpanCharacter.T.J B * M Y = algebraMap R B (q Y) • Formalism.YangianSpanCharacter.T.J B ∧
    M Y * Formalism.YangianSpanCharacter.T.J B * (M (Y + 1))ᵀ = algebraMap R B (q Y) • Formalism.YangianSpanCharacter.T.J B

def EntriesCommute (M N : R → Matrix (Fin 2) (Fin 2) B) : Prop :=
  ∀ (Y Y' : R) (i j k l : Fin 2), M Y i j * N Y' k l = N Y' k l * M Y i j

def WordFusion : Prop :=
  ∀ (R B : Type) [CommRing R] [Ring B] [Algebra R B]
    (L : List ((R → Matrix (Fin 2) (Fin 2) B) × (R → R))),
    (∀ x ∈ L, IsRTT x.1 ∧ IsDet x.1 x.2) →
    L.Pairwise (fun x y => EntriesCommute x.1 y.1) →
    IsRTT (fun Y => (L.map (fun x => x.1 Y)).prod) ∧
      IsDet (fun Y => (L.map (fun x => x.1 Y)).prod) (fun Y => (L.map (fun x => x.2 Y)).prod)

def NormLower : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
    (aa : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (l : E), l ∈ aa → l ≠ 0 →
      √(FractionalIdeal.absNorm aa : ℝ) ≤ ∏ w : InfinitePlace E, w l

end Formalism.FourierDecayAlt.W
