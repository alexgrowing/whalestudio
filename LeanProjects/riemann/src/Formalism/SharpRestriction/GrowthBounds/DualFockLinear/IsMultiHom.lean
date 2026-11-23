import Formalism.SharpRestriction.GrowthBounds.ScaleEdges
import Formalism.LocalToGlobal.GroupLattices.FockModels.WeylDim

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.L2.G.Model (Nv)

def Xs (m : ℕ) (top vec : Bool) (ν : Fin (m + 1) → ℕ) : Set (Fin (m + 1) × Fin (m + 1) →₀ ℕ) :=
  {e | e ∈ ssIdx (m + 1) (m + 1) ν ∧ (top = true → (vec = true → e (0, 0) = ν 0) ∧ (vec = false → ∀ t, e (0, t) = 0))}

def thAll (R : Type) [CommRing R] (n' m : ℕ) (vec : Fin n' → Bool) :
    MvPolynomial (Fin n' × Fin (m + 1)) R →ₐ[R] MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R :=
  aeval fun v => blockEmb R v.1 (Nv R m (vec v.1) v.2)

def IsMultiHom {R : Type} [CommRing R] {n' k : ℕ} (d : Fin n' → ℕ) (Q : MvPolynomial (Fin n' × Fin k) R) : Prop :=
  ∀ e ∈ Q.support, ∀ s, ∑ c : Fin k, e (s, c) = d s

def PosInd : Prop :=
  ∀ (F : Type) [Field F] (m : ℕ), 2 ≤ m → ∀ (top vec : Bool) (d : ℕ) (ν : Fin (m + 1) → ℕ),
    (top = false → d = 0) → (top = true → vec = false → ∀ t : Fin (m + 1), m ≤ t.val + 1 → ν t = 0) →
    ∀ b : Xs m top vec ν → MvPolynomial (Fin (m + 1) × Fin (m + 1)) F,
      (∀ x, (colLex (m + 1) (m + 1)).degree (b x) = x.1 ∧ (colLex (m + 1) (m + 1)).leadingCoeff (b x) = 1) →
      LinearIndependent F (fun y : {α : Fin (m + 1) →₀ ℕ // ∑ c, α c = d} × Xs m top vec ν =>
        (∏ c, Nv F m vec c ^ (y.1.1 c)) * b y.2)

def BigInd : Prop :=
  ∀ (F : Type) [Field F] (n' m : ℕ), 2 ≤ m → ∀ (top vec : Fin n' → Bool) (d : Fin n' → ℕ) (ν : Fin n' → Fin (m + 1) → ℕ),
    (∀ s, top s = false → d s = 0) →
    (∀ s, top s = true → vec s = false → ∀ t : Fin (m + 1), m ≤ t.val + 1 → ν s t = 0) →
    ∀ b : ∀ s, Xs m (top s) (vec s) (ν s) → MvPolynomial (Fin (m + 1) × Fin (m + 1)) F,
      (∀ s x, (colLex (m + 1) (m + 1)).degree (b s x) = x.1 ∧ (colLex (m + 1) (m + 1)).leadingCoeff (b s x) = 1) →
      ∀ (J : Finset (∀ s, Xs m (top s) (vec s) (ν s)))
        (Q : (∀ s, Xs m (top s) (vec s) (ν s)) → MvPolynomial (Fin n' × Fin (m + 1)) F),
        (∀ i, IsMultiHom d (Q i)) →
        ∑ i ∈ J, thAll F n' m vec (Q i) * ∏ s, blockEmb F s (b s (i s)) = 0 → ∀ i ∈ J, Q i = 0

def CntTop : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (lo : Fin (m + 1) → ℤ), Antitone lo → lo 0 = lo 1 → ∀ vec : Bool,
    ((Nat.card (Xs m true vec (nuOf (if vec = true then lo else fun i => -lo i.rev))) : ℕ) : ℚ) =
      Formalism.CountingSumsFrames.weylDim m (fun i : Fin m => lo i.succ)

def CntSpec : Prop :=
  ∀ (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam → ∀ vec : Bool,
    ((Nat.card (Xs m false vec (nuOf lam)) : ℕ) : ℚ) = Formalism.CountingSumsFrames.weylDim (m + 1) lam

end Formalism.MainNotions.TestSideCounting
