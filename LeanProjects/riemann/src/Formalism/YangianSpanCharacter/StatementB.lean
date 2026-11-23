import Formalism.FormalDegreeBessel.FinalWR
import Formalism.YangianSpanCharacter.ExchangeGen
import Formalism.YangianSpanCharacter.TJTrev

namespace Formalism.YangianSpanCharacter.B

open Matrix Formalism.YangianSpanCharacter.T Formalism.QuantumDeterminants

def TJTReal : Prop :=
  ∀ (m : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin m) (Y : ℂ),
    (Tm (Y + 1) (pEnd (E := E) l) (cEnd l) (ciEnd l))ᵀ * Formalism.YangianSpanCharacter.T.J (Module.End ℂ (WSm m E)) *
        Tm Y (pEnd (E := E) l) (cEnd l) (ciEnd l) = Formalism.YangianSpanCharacter.T.J (Module.End ℂ (WSm m E))

def TvJTsReal : Prop :=
  ∀ (m : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin m) (Y : ℂ),
    Tm (Y + 1) (-pbEnd (E := E) l) (cbEnd l) (cbiEnd l) * Formalism.YangianSpanCharacter.T.J (Module.End ℂ (WSm m E)) *
        (Tm Y (-pbEnd (E := E) l) (cbEnd l) (cbiEnd l))ᵀ = Formalism.YangianSpanCharacter.T.J (Module.End ℂ (WSm m E))

def RTTReal : Prop :=
  ∀ (m : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin m) (Y Y' : ℂ),
    ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (Module.End ℂ (WSm m E))) -
          Pf (Module.End ℂ (WSm m E))) * T1 Y' (pEnd (E := E) l) (cEnd l) (ciEnd l) *
        T2 Y (pEnd (E := E) l) (cEnd l) (ciEnd l) =
      T2 Y (pEnd (E := E) l) (cEnd l) (ciEnd l) * T1 Y' (pEnd (E := E) l) (cEnd l) (ciEnd l) *
        ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (Module.End ℂ (WSm m E))) -
          Pf (Module.End ℂ (WSm m E)))

def ExchangeTReal : Prop :=
  ∀ (m : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin m) (Y Yb : ℂ),
    Tbt Yb (pEnd (E := E) l) (cEnd l) (ciEnd l) *
        pt1 ((Yb - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (Module.End ℂ (WSm m E))) -
          Pf (Module.End ℂ (WSm m E))) * T1 Y (pEnd (E := E) l) (cEnd l) (ciEnd l) =
      T1 Y (pEnd (E := E) l) (cEnd l) (ciEnd l) *
        pt1 ((Yb - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (Module.End ℂ (WSm m E))) -
          Pf (Module.End ℂ (WSm m E))) * Tbt Yb (pEnd (E := E) l) (cEnd l) (ciEnd l)

end Formalism.YangianSpanCharacter.B
