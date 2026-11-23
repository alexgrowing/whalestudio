import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadAATopOfParts

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def RightRuleE : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (D : Set (Q.Mx k r)) (f : Q.Mx k r → E), inWb k r z' → IsOpen D → Q.SmoothLev k r 0 D f →
    Q.RightEq k r z' 0 D f → ∀ g ∈ Q.Glev k r 0 ∩ D, ∀ a b : Fin r, a.val < b.val →
      Q.EH k r (eI k r a) (eI k r b) f g = (if b.val = a.val + 1 then (1 : ℂ) else 0) • f g

def LeftRuleCell : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (D : Set (Q.Mx k r)) (f : Q.Mx k r → E), inWb k r z → IsOpen D →
    (∀ g ∈ Q.Glev k r 0 ∩ D, ∀ n ∈ Q.Nlev k r 0, n * g ∈ D) → Q.SmoothLev k r 0 D f → Q.LeftEq k r z 0 D f →
    ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D → ∀ a b : Fin r, b.val < a.val →
      Q.EH k r (eI k r a) (eI k r b) f (Q.wCell k r (Fin.last r) c * g) =
        (if a.val = b.val + 1 then c a / c b else 0) • f (Q.wCell k r (Fin.last r) c * g)

def TorusCell : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (D : Set (Q.Mx k r)) (f : Q.Mx k r → E),
    IsOpen D → Q.SmoothLev k r 0 D f → ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r),
    Q.wCell k r (Fin.last r) c * g ∈ D → ∀ l : Fin r,
      Q.EH k r (eI k r l) (eI k r l) f (Q.wCell k r (Fin.last r) c * g) =
        pOp l (fun c' => f (Q.wCell k r (Fin.last r) c' * g)) c

def GaugeP : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (r : ℕ) (n : Fin r → ℕ) (H : (Fin r → ℂ) → E)
    (c : Fin r → ℂ), c ∈ OmX r → DifferentiableAt ℝ H c → ∀ l : Fin r,
      pOp l (fun c' => ((∏ a, ‖c' a‖ ^ n a : ℝ) : ℂ) • H c') c =
        ((∏ a, ‖c a‖ ^ n a : ℝ) : ℂ) • (pOp l H c + ((n l : ℂ) / 2) • H c)

def MinorCellOfParts : Prop := RightRuleE → LeftRuleCell → TorusCell → GaugeP → MinorCell

end Formalism.FourierDecayAlt.P.PBN
