import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
import Formalism.ThetaLiftIndependence.Statement
import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds

noncomputable section

open scoped Classical

namespace GlobalTheory.LoopC

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

abbrev Fg (T : D.host.E) : Type := LFlag (hS D) D.R.rS T

abbrev Fb (u : D.what₂.Word) : Type := FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)

abbrev LatW : Type := Submodule (𝓞 D.host.E) (D.sp.X 0).V

def IsBase (u : D.what₂.Word) (F0 : Fb D u) : Prop := F0.e = D.sp.hypE ∧ F0.z = D.zmOf u

def seen {T : D.host.E} (F : Fg D T) (M : LatV D) : LatW D :=
  (M ⊔ toO (hS D) (Xsp F)).comap ((D.sp.iXY 0).restrictScalars (𝓞 D.host.E))

def sat (L P : LatW D) : LatW D :=
  L ⊓ (Submodule.span D.host.E (P : Set (D.sp.X 0).V)).restrictScalars (𝓞 D.host.E)

def perpE (P : LatW D) : Submodule D.host.E (D.sp.X 0).V := ⨅ p ∈ P, LinearMap.ker ((D.sp.X 0).hT p)

def perpW (L P : LatW D) : LatW D := L ⊓ (perpE D P).restrictScalars (𝓞 D.host.E)

def idxW (A B : LatW D) : ℕ := Nat.card (A ⧸ B.comap A.subtype)

def rkW (P : LatW D) : ℕ := finrank D.host.E (Submodule.span D.host.E (P : Set (D.sp.X 0).V))

def detW (P : LatW D) : ℝ := latDetH (D.sp.X 0).hT P

def SubOK (L P : LatW D) (s : ℕ) (Q : ℝ) : Prop :=
  P ≤ L ∧ rkW D P = D.R.k - s ∧ 1 ≤ idxW D (sat D L P) P ∧ (idxW D (sat D L P) P : ℝ) ≤ Q ∧ detW D P ≤ Q

def N1 (Λ : LatV D) {T : D.host.E} (F : Fg D T) : Set ((hS D).V ≃ₗ[D.host.E] (hS D).V) :=
  {n | n ∈ NLam Λ F ∧ ∀ b, n (frame F b) = frame F b}

def YS : LatV D :=
  Submodule.span (𝓞 D.host.E)
    {y | ∃ (a : Fin D.R.rS) (x : D.host.E),
      x ∈ (ddS D ^ ((D.R.rS : ℤ) - (a : ℕ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ∧
        y = x • D.sp.hypF a}

def IsSplit {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LatV D) : Prop :=
  Λ = XS D F0 ⊔ (Λ ⊓ toO (hS D) (Wb D)) ⊔ YS D

def FixFr {T : D.host.E} (F : Fg D T) (n : (hS D).V ≃ₗ[D.host.E] (hS D).V) : Prop :=
  n ∈ Formalism.HermitianLatticesTheory.isom (hS D).hT ∧ (∀ b, n (frame F b) = frame F b) ∧ ∀ x ∈ orth (hS D) (Xsp F), n x - x ∈ Xsp F

def FrSet (Λ : LatV D) {T : D.host.E} (F : Fg D T) (T' : D.host.E) (Z : GramM D) (P : LatW D) : Set (Fg D T') :=
  {F' | IsTermF D Λ F F' ∧ ZEquiv (ZhatL F F') Z ∧ P ≤ seen D F (Thp Λ F F')}

def cntFr (Λ : LatV D) {T : D.host.E} (F : Fg D T) (T' : D.host.E) (Z : GramM D) (P : LatW D) : ℕ∞ :=
  cntCl (FrSet D Λ F T' Z P) (TEqv D Λ F)

def ExSet (Λ : LatV D) {T : D.host.E} (F : Fg D T) (T' : D.host.E) (Z : GramM D) (P : LatW D) : Set (Fg D T') :=
  {F' | IsLift Λ F' ∧ (∀ a, F'.fl.e a ∈ Λ) ∧ ZhatL F F' = Z ∧ P ≤ seen D F (Thp Λ F F')}

def FixSet (Λ : LatV D) {T : D.host.E} (F : Fg D T) (T' : D.host.E) (Z : GramM D) (P : LatW D)
    (φ : P →ₗ[𝓞 D.host.E] (hS D).V) : Set (Fg D T') :=
  {F' | IsLift Λ F' ∧ (∀ a, F'.fl.e a ∈ Λ) ∧ ZhatL F F' = Z ∧
    ∀ (p : P) (b : Fin (D.R.rS + 1)), (hS D).hT (D.sp.iXY 0 (p : (D.sp.X 0).V) + φ p) (frame F' b) = 0}

def IsWcomp (P : LatW D) (x : (hS D).V) (w : (D.sp.X 0).V) : Prop :=
  w ∈ perpE D P ∧ ∀ σ ∈ perpE D P, (hS D).hT (D.sp.iXY 0 σ) x = (D.sp.X 0).hT σ w

def Gmat (T T' : D.host.E) (Z : GramM D) : D.host.E :=
  leadMinorE Z (D.R.rS + 1) * star (leadMinorE Z (D.R.rS + 1)) -
    T * T' * (leadMinorE Z D.R.rS * star (leadMinorE Z D.R.rS))

def rowMinor (Z : GramM D) (b₀ : Fin (D.R.rS + 1)) : D.host.E :=
  ((Z.submatrix Fin.castSucc id).submatrix id b₀.succAbove).det

def QOK (u u' : D.what₂.Word) (Z : GramM D) (Q : ℝ) : Prop :=
  1 ≤ Q ∧ D.host.rdE ^ (2 * D.R.f * D.R.rS) ≤ Q ∧
  (∃ b₀, rowMinor D Z b₀ ≠ 0 ∧ ∏ τ, ‖embS D τ (rowMinor D Z b₀)‖ ^ 2 ≤ Q) ∧
  Gmat D ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E) Z ≠ 0 ∧
  ∏ τ, ‖embS D τ (Gmat D ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E) Z)‖ ≤ Q

def fixB (s : ℕ) (N De Q : ℝ) : ℝ :=
  9 ^ (s * D.R.f) * (De ^ 2 * N ^ 2 * Q) ^ (s + s * D.R.rS) * Q ^ (2 * D.R.rS ^ 2)

def frB (s : ℕ) (N De Q : ℝ) : ℝ := N ^ (2 * D.R.rS) * De ^ D.R.rS * fixB D s N De Q

def glueSet (u : D.what₂.Word) (L' : LatW D) : Set (LatV D) :=
  {L | L.FG ∧ spanE (hS D) L = Wb D ∧ dualIn (hS D) L = L ∧ D.zmOf u ∈ L ∧
    (∀ c : D.host.E, c • D.zmOf u ∈ L → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) ∧
    L.comap ((D.sp.iXY 0).restrictScalars (𝓞 D.host.E)) = L'}

end GlobalTheory.LoopC

end
