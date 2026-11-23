import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartEqsOfParts

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev GenW (k r : ℕ) := Polynomial ℂ × List (ℂ × B.Mat k r)

def fexp {k r : ℕ} : List (GenW k r) → List (Polynomial ℂ × List (B.Mat k r))
  | [] => [(1, [])]
  | gn :: gs => (fexp gs).map (fun t => (gn.1 * t.1, t.2)) ++
      gn.2.flatMap (fun dX => (fexp gs).map (fun t => (Polynomial.C dX.1 * t.1, dX.2 :: t.2)))

section ops

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def genOpR (gn : GenW k r) (u : ℂ) (F : B.Mat k r → E) : B.Mat k r → E :=
  fun h => gn.1.eval u • F h + (gn.2.map fun dX => dX.1 • Formalism.REAL.RdV dX.2 F h).sum

def genOpL (gn : GenW k r) (u : ℂ) (F : B.Mat k r → E) : B.Mat k r → E :=
  fun h => gn.1.eval u • F h + (gn.2.map fun dX => dX.1 • Q.LdV dX.2 F h).sum

def wsEvalR (ws : List (Polynomial ℂ × List (B.Mat k r))) (u : ℂ) (f : B.Mat k r → E) (g : B.Mat k r) : E :=
  (ws.map fun t => t.1.eval u • B.Rw t.2 f g).sum

def wsEvalL (ws : List (Polynomial ℂ × List (B.Mat k r))) (u : ℂ) (f : B.Mat k r → E) (g : B.Mat k r) : E :=
  (ws.map fun t => t.1.eval u • t.2.foldr Q.LdV f g).sum

end ops

def capGen {k r t : ℕ} (Zg : Fin t → Fin t → B.Mat k r) (σ : Equiv.Perm (Fin t)) (i : Fin t) : GenW k r :=
  (if σ i = i then Polynomial.X - Polynomial.C ((i : ℕ) : ℂ) else 0,
    [(1, hpart1 (Hpk k r) (Zg (σ i) i)), (Complex.I, hpart2 (Hpk k r) (Zg (σ i) i))])

def capGens {k r t : ℕ} (Zg : Fin t → Fin t → B.Mat k r) (σ : Equiv.Perm (Fin t)) : List (GenW k r) :=
  List.ofFn (capGen Zg σ)

def zgCV (k r : ℕ) : Fin (Q.mdim k r 0) → Fin (Q.mdim k r 0) → B.Mat k r :=
  fun a b => Matrix.single (Q.posL k r 0 a) (Q.posL k r 0 b) (1 : ℂ)

def zgB {k r : ℕ} (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) : Fin k → Fin k → B.Mat k r :=
  fun a b => Q.unitB (Hpk k r) Bs a b

def RdVRep : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (X : B.Mat k r) (U : Set (B.Mat k r))
    (F f : B.Mat k r → E), B.inLie k r X → IsOpen U → ContDiffOn ℝ 1 F U →
    (∀ g ∈ U, g ∈ B.GV k r → f g = F g) → ∀ h ∈ U, h ∈ B.GV k r →
      Formalism.REAL.RdV X f h = fderiv ℝ F h (h * X) ∧ Q.LdV X f h = fderiv ℝ F h (X * h)

def FExpEvalR : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (gens : List (GenW k r)) (u : ℂ)
    (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
    (∀ gn ∈ gens, ∀ dX ∈ gn.2, B.inLie k r dX.2) → B.CkOn (gens.length : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
      (gens.map (fun gn => genOpR gn u)).foldr (fun T h => T h) f g = wsEvalR (fexp gens) u f g

def FExpEvalL : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (gens : List (GenW k r)) (u : ℂ)
    (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
    (∀ gn ∈ gens, ∀ dX ∈ gn.2, B.inLie k r dX.2) → B.CkOn (gens.length : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
      (gens.map (fun gn => genOpL gn u)).foldr (fun T h => T h) f g = wsEvalL (fexp gens) u f g

def CVAsGens : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (Y : ℂ) (f : B.Mat k r → E) (g : B.Mat k r),
    Q.CV k r Y f g = ∑ σ : Equiv.Perm (Fin (Q.mdim k r 0)), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ((capGens (zgCV k r) σ).map (fun gn => genOpR gn (Q.uC k r 0 Y))).foldr (fun T h => T h) f g

def CapRAsGens : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) (w : ℂ)
    (f : B.Mat k r → E) (g : B.Mat k r),
    Q.capR k r Bs w f g = ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ((capGens (zgB Bs) σ).map (fun gn => genOpR gn w)).foldr (fun T h => T h) f g

def CapLAsGens : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) (w : ℂ)
    (f : B.Mat k r → E) (g : B.Mat k r),
    Q.capLft k r Bs w f g = ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ((capGens (zgB Bs) σ).reverse.map (fun gn => genOpL gn w)).foldr (fun T h => T h) f g

def FExpDeg : Prop :=
  ∀ (k r : ℕ) (gens : List (GenW k r)), (∀ gn ∈ gens, gn.1.natDegree ≤ 1) →
    ∀ t ∈ fexp gens, t.1.natDegree + t.2.length ≤ gens.length ∧ ∀ X ∈ t.2, ∃ gn ∈ gens, ∃ d : ℂ, (d, X) ∈ gn.2

def FExpSymb : Prop :=
  ∀ (k r : ℕ) (gens : List (GenW k r)) (τ : B.Mat k r → ℂ) (u s : ℂ),
    ((fexp gens).map fun t => t.1.eval u * s ^ t.2.length * (t.2.map τ).prod).sum =
      (gens.map fun gn => gn.1.eval u + s * (gn.2.map fun dX => dX.1 * τ dX.2).sum).prod

def DetShiftCoeff : Prop :=
  ∀ (t : ℕ) (M : Matrix (Fin t) (Fin t) ℂ) (j : ℕ), j ≤ t →
    MvPolynomial.coeff (Finsupp.single (0 : Fin 2) (t - j) + Finsupp.single (1 : Fin 2) j)
      (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin 2) ℂ) *
        ∏ i : Fin t, ((if σ i = i then MvPolynomial.X 0 - MvPolynomial.C ((i : ℕ) : ℂ) else 0) +
          MvPolynomial.X 1 * MvPolynomial.C (M (σ i) i))) =
      (-1) ^ j * M.charpoly.coeff (t - j)

def CoeffInterp : Prop :=
  ∀ (N m : ℕ), m ≤ N → ∃ (Ys : Fin (N + 1) → ℝ) (lam : Fin (N + 1) → ℂ),
    ∀ q : Polynomial ℂ, q.natDegree ≤ N → ∑ i, lam i * q.eval (Ys i : ℂ) = q.coeff m

def CapWordsOfParts : Prop :=
  RdVRep → FExpEvalR → CVAsGens → FExpDeg → FExpSymb → DetShiftCoeff → CoeffInterp → CapWords

def CapRWordsOfParts : Prop :=
  RdVRep → FExpEvalR → CapRAsGens → FExpDeg → FExpSymb → DetShiftCoeff → CoeffInterp → CapRWords

def CapLWordsOfParts : Prop :=
  RdVRep → FExpEvalL → CapLAsGens → FExpDeg → FExpSymb → DetShiftCoeff → CoeffInterp → CapLWords

theorem capWords_all_of (hJ : CapWordsOfParts) (hJR : CapRWordsOfParts) (hJL : CapLWordsOfParts) (h1 : RdVRep)
    (hR : FExpEvalR) (hL : FExpEvalL) (hCV : CVAsGens) (hCR : CapRAsGens) (hCL : CapLAsGens) (hD : FExpDeg)
    (hS : FExpSymb) (hDet : DetShiftCoeff) (hI : CoeffInterp) : CapWords ∧ CapRWords ∧ CapLWords :=
  ⟨hJ h1 hR hCV hD hS hDet hI, hJR h1 hR hCR hD hS hDet hI, hJL h1 hL hCL hD hS hDet hI⟩

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
