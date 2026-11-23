import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapToda

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def RightRuleEv : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (D : Set (Q.Mx k r)) (f : Q.Mx k r → E), inWb k r z' → IsOpen D → Q.SmoothLev k r 0 D f →
    Q.RightEq k r z' 0 D f → ∀ g ∈ Q.Glev k r 0 ∩ D, ∀ a b : Fin r, b.val < a.val →
      Q.EH k r (esI k r a) (esI k r b) f g = (if a.val = b.val + 1 then (1 : ℂ) else 0) • f g

def LeftRuleCellv : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (D : Set (Q.Mx k r)) (f : Q.Mx k r → E), inWb k r z → IsOpen D →
    (∀ g ∈ Q.Glev k r 0 ∩ D, ∀ n ∈ Q.Nlev k r 0, n * g ∈ D) → Q.SmoothLev k r 0 D f → Q.LeftEq k r z 0 D f →
    ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D → ∀ a b : Fin r, b.val < a.val →
      Q.EH k r (esI k r b) (esI k r a) f (Q.wCell k r (Fin.last r) c * g) =
        (if a.val = b.val + 1 then star (c a) / star (c b) else 0) • f (Q.wCell k r (Fin.last r) c * g)

def TorusCellv : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (D : Set (Q.Mx k r)) (f : Q.Mx k r → E),
    IsOpen D → Q.SmoothLev k r 0 D f → ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r),
    Q.wCell k r (Fin.last r) c * g ∈ D → ∀ l : Fin r,
      Q.EH k r (esI k r l) (esI k r l) f (Q.wCell k r (Fin.last r) c * g) =
        -pbOp l (fun c' => f (Q.wCell k r (Fin.last r) c' * g)) c

def MirrorChainExpansion : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (M : Type) [AddCommGroup M] [Module ℂ M] (k r : ℕ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (La : A →ₗ[ℂ] M) (ρ : ℂ), GlRel E →
    ∀ (m : ℕ) (hm : m + 2 ≤ r) (u : ℂ),
    (∀ (x : A) (a : Fin r), r - m - 1 < a.val → La (x * E (esI k r a) (esI k r ⟨r - m - 2, by omega⟩)) = 0) →
    (∀ x : A, La (x * E (esI k r ⟨r - m - 1, by omega⟩) (esI k r ⟨r - m - 2, by omega⟩)) = La x) →
    (∀ (x : A) (b : Fin r), r - m - 2 < b.val →
      La (E (esI k r ⟨r - m - 2, by omega⟩) (esI k r b) * x) = (if b.val = r - m - 1 then ρ else 0) • La x) →
    La (qminor E (colsVm k r (m + 2)) (colsVm k r (m + 2)) u) =
      La (qminor E (colsVm k r (m + 1)) (colsVm k r (m + 1)) u *
          Tm E (u - ((m + 1 : ℕ) : ℂ)) (esI k r ⟨r - m - 2, by omega⟩) (esI k r ⟨r - m - 2, by omega⟩)) -
        ρ • La (qminor E (colsVm k r m) (colsVm k r m) u)

end Formalism.FourierDecayAlt.P.CutMP.TVG
