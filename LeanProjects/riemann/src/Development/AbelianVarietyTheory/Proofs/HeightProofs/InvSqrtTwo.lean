import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IterateOnePlusCasOfEq

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum.CasBasis

variable {n : ℕ}

def pairs (ε : Fin n → Bool) (same : Bool) : List (Fin n × Fin n) :=
  (List.product (List.finRange n) (List.finRange n)).filter
    fun p => decide (p.1 < p.2) && ((ε p.1 == ε p.2) == same)

abbrev unitE (a b : Fin n) : Mx n := Matrix.single a b 1

abbrev invSqrtTwo : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

def kList (ε : Fin n → Bool) : List (Mx n) :=
  (List.finRange n).map (fun a => Complex.I • unitE a a) ++
    (pairs ε true).flatMap fun p =>
      [invSqrtTwo • (unitE p.1 p.2 - unitE p.2 p.1), (invSqrtTwo * Complex.I) • (unitE p.1 p.2 + unitE p.2 p.1)]

def pList (ε : Fin n → Bool) : List (Mx n) :=
  (pairs ε false).flatMap fun p =>
    [invSqrtTwo • (unitE p.1 p.2 + unitE p.2 p.1), (invSqrtTwo * Complex.I) • (unitE p.1 p.2 - unitE p.2 p.1)]

def kB (ε : Fin n → Bool) : Fin (kList ε).length → Mx n := (kList ε).get

def pB (ε : Fin n → Bool) : Fin (pList ε).length → Mx n := (pList ε).get

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def lapOne (ε : Fin n → Bool) (σ : Mx n → (H →L[ℂ] H)) (v : H) : H :=
  onePlusCas σ (kB ε) v - ∑ b, dRep σ (pB ε b) (dRep σ (pB ε b) v)

end GlobalTheory.TypeSum.CasBasis

end
