import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

variable {n r : ℕ}

def SLoc (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : Set (Formalism.REAL.UJ ε) :=
  {g | InS e z (uMat g)}

def IsHaarS {ε : Fin n → Bool} (S : Set (Formalism.REAL.UJ ε)) (μ : Measure (Formalism.REAL.UJ ε)) : Prop :=
  IsHaarLoc S μ ∧ IsFiniteMeasureOnCompacts μ

structure FrameLoc (ε : Fin n → Bool) (k : ℕ) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' : ℝ) : Prop where
  dim : n = 2 * r + 1 + k
  k_pos : 1 ≤ k
  sig : (Finset.univ.filter (fun i => ε i = false)).card = r + 1
  e_li : LinearIndependent ℂ e
  ee : ∀ a b, hJ ε (e a) (e b) = 0
  ez : ∀ a, hJ ε (e a) z = 0
  ez' : ∀ a, hJ ε (e a) z' = 0
  zz : hJ ε z z = -(T : ℂ)
  zz' : hJ ε z' z' = -(T' : ℂ)
  T_pos : 0 < T
  T'_pos : 0 < T'

def ZLoc (ε : Fin n → Bool) (sc : ℝ) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (g : Formalism.REAL.UJ ε) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  Zhat ε (famSc sc e z) (famSc sc e z') (uMat g)

def GoodLoc (T T' : ℝ) : Set (Fin (r + 1) → ℂ) :=
  {c | (∀ l, c l ≠ 0) ∧ 0 < Gv T T' (Matrix.diagonal c)}

def wtLoc (k : ℕ) (T T' : ℝ) (c : Fin (r + 1) → ℂ) : ℝ :=
  Gv T T' (Matrix.diagonal c) ^ (k - 1) * JacV (Matrix.diagonal c)

def dcLoc : Measure (Fin (r + 1) → ℂ) :=
  Measure.pi fun _ => (2 : ℝ≥0∞) • (volume : Measure ℂ)

def IsSecLoc (ε : Fin n → Bool) (sc : ℝ) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' : ℝ)
    (h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε) : Prop :=
  ∀ c ∈ GoodLoc (r := r) T T', ZLoc ε sc e z z' (h c) = Matrix.diagonal c

def DisintLoc (ε : Fin n → Bool) (k : ℕ) (T T' : ℝ) (μS μS' : Measure (Formalism.REAL.UJ ε))
    (h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε) (C : ℝ) : Prop :=
  ∀ φ : Formalism.REAL.UJ ε → ℝ≥0∞, Measurable φ →
    ∫⁻ x, φ x ∂(Formalism.REAL.muG ε) =
      ∫⁻ c in GoodLoc (r := r) T T', ENNReal.ofReal (C * wtLoc k T T' c) *
        ∫⁻ s, ∫⁻ s', φ (s * h c * s'⁻¹) ∂μS' ∂μS ∂(dcLoc (r := r))

def JacLoc : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' sc : ℝ),
    FrameLoc ε k e z z' T T' → 0 < sc →
    ∀ μS μS' : Measure (Formalism.REAL.UJ ε), IsHaarS (SLoc ε e z) μS → IsHaarS (SLoc ε e z') μS' →
    ∀ h, IsSecLoc ε sc e z z' T T' h → ∃ C, 0 < C ∧ DisintLoc ε k T T' μS μS' h C

def DiagDCLoc : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' sc : ℝ),
    FrameLoc ε k e z z' T T' →
    ∀ c ∈ GoodLoc (r := r) T T', ∀ g g' : Formalism.REAL.UJ ε,
      ZLoc ε sc e z z' g = Matrix.diagonal c → ZLoc ε sc e z z' g' = Matrix.diagonal c →
      ∃ s ∈ SLoc ε e z, ∃ s' ∈ SLoc ε e z', g' = s * g * s'⁻¹

def OrbitLoc : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' sc : ℝ),
    FrameLoc ε k e z z' T T' → 0 < sc →
    ∀ h, IsSecLoc ε sc e z z' T T' h →
    ∀ g : Formalism.REAL.UJ ε, IsReg T T' (ZLoc ε sc e z z' g) →
      ∃ c ∈ GoodLoc (r := r) T T', ∃ s ∈ SLoc ε e z, ∃ s' ∈ SLoc ε e z', g = s * h c * s'⁻¹

def NullLoc : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' sc : ℝ),
    FrameLoc ε k e z z' T T' → 0 < sc →
    Formalism.REAL.muG ε {g | ¬ IsReg T T' (ZLoc ε sc e z z' g)} = 0

def SecMeasLoc : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' sc : ℝ),
    FrameLoc ε k e z z' T T' → 0 < sc → ∃ h, Measurable h ∧ IsSecLoc ε sc e z z' T T' h

def NLoc (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : Set (Formalism.REAL.UJ ε) :=
  {g | InN ε e z (uMat g)}

def HLoc (ε : Fin n → Bool) (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : Set (Formalism.REAL.UJ ε) :=
  {g | (∀ a, uMat g *ᵥ e a = e a) ∧ (∀ a, uMat g *ᵥ p a = p a) ∧ uMat g *ᵥ z = z}

def UnimodLoc : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' : ℝ),
    FrameLoc ε k e z z' T T' →
    ∀ μ : Measure (Formalism.REAL.UJ ε), IsHaarS (SLoc ε e z) μ →
    ∀ s ∈ SLoc ε e z, μ.map (fun x => x * s) = μ

def NHLoc : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e p : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' : ℝ),
    FrameLoc ε k e z z' T T' → (∀ a b, hJ ε (e a) (p b) = if a = b then 1 else 0) → (∀ a b, hJ ε (p a) (p b) = 0) →
    (∀ b, hJ ε z (p b) = 0) →
    ∀ μN μH : Measure (Formalism.REAL.UJ ε), IsHaarS (NLoc ε e z) μN → IsHaarS (HLoc ε e p z) μH →
    IsHaarS (SLoc ε e z) ((μN.prod μH).map (fun q => q.1 * q.2))

def P5 : Prop := JacLoc → DiagDCLoc → SecMeasLoc → UnimodLoc → NHLoc → StepReal → HaarDisintegrationReal

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates
