import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.HermitianCurvature.StatementD
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.PeriodIntegrals.CapelliEig

namespace GlobalTheory.ThA

open Formalism.FourierDecayAlt MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

noncomputable section

def aT (k r : ℕ) (α : ℂ) : B.Mat k r :=
  Matrix.diagonal fun i => if i.val < r then α ^ (r - i.val)
    else if i.val ≤ r + k then 1 else ((star α) ^ (i.val - (r + k)))⁻¹

def conjF {k r : ℕ} {V : Type*} (α : ℂ) (F : B.Mat k r → V) : B.Mat k r → V :=
  fun x => F (aT k r α * x * (aT k r α)⁻¹)

def KH (k r : ℕ) : Set (B.Mat k r) :=
  UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _)

def IsStdOf {k r : ℕ} (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (Bs : B.RealPlaceData k r L.Wp L.Wq) : Prop :=
  Bs.z = L.z ∧ Bs.z' = L.z' ∧ Bs.π = L.π ∧ Bs.π' = L.π' ∧ Bs.μW = L.μW ∧ Bs.μW' = L.μW' ∧
    Bs.μN = D.muN k r ∧ Bs.μsec = μsec

def IsRatioN (k r : ℕ) (cN : ℝ) : Prop :=
  0 < cN ∧ Formalism.MainNotions.S.haarLie (Nset k r) 1 = ENNReal.ofReal cN • D.muN k r

def lamN {k r : ℕ} (L : Formalism.MainNotions.S.LocBessel k r) (cN : ℝ) : ℝ :=
  L.κN.toReal * cN * ‖cStd / L.c‖ ^ B.kap k r

def Admissible : Prop :=
  ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : B.Mat k r → (H →L[ℂ] H)),
    Formalism.MainNotions.S.IsURepOn (UH (Hpk k r)) σ → Formalism.MainNotions.S.IsIrredOn (UH (Hpk k r)) σ →
    ∀ (S : Submodule ℂ H) (hS : ∀ g ∈ KH k r, ∀ x ∈ S, σ g x ∈ S), FiniteDimensional ℂ S →
      (∀ S' : Submodule ℂ H, S' ≤ S → (∀ g ∈ KH k r, ∀ x ∈ S', σ g x ∈ S') → S' = ⊥ ∨ S' = S) →
      ∃ M : Submodule ℂ H, FiniteDimensional ℂ M ∧ ∀ T : S →ₗ[ℂ] H,
        (∀ g (hg : g ∈ KH k r) (x : S), T ⟨σ g x, hS g hg x x.2⟩ = σ g (T x)) → ∀ x, T x ∈ M

def DomBy {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : B.Mat k r → (H →L[ℂ] H))
    (w v : H) : Prop :=
  ∃ R C : ℝ, 0 ≤ C ∧ ∀ (y : H) (M : ℝ), (∀ x ∈ B.GV k r, B.gN x ≤ R → ‖⟪y, σ x w⟫_ℂ‖ ≤ M) → 0 ≤ M →
    ‖⟪y, v⟫_ℂ‖ ≤ C * M

def aDec (r : ℕ) (h : ℝ) : ℝ := h / (8 * Real.sqrt (2 * ((r : ℝ) + 1)))

def CoefOK : Prop :=
  ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ), 1 ≤ k → GapAtLeast L.ε L.lam h →
    120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h →
    ∀ (f : B.Mat k r → (L.Wq →L[ℂ] L.Wp)) (a b : B.Mat k r), Formalism.MainNotions.S.IsKFinCoefH L.σ f →
      a ∈ B.GV k r → b ∈ B.GV k r →
      B.CkOn ⊤ (B.GV k r) (fun g => f (a * g * b)) ∧ (∀ m : ℕ, B.InCC (aDec r h) m (fun g => f (a * g * b))) ∧
      ∀ Y : ℂ, ∀ g ∈ B.GV k r,
        Q.CV k r Y (fun g => f (a * g * b)) g = capP (fun s => (L.lam s : ℂ)) Y • f (a * g * b)

end

end GlobalTheory.ThA
