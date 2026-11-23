import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacLocOfHpk

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

def coordSc (r : ℕ) (sc : ℝ) (q : (Fin r → ℂ) × ℂ) : Fin (r + 1) → ℂ :=
  Fin.snoc (α := fun _ => ℂ) (fun a : Fin r => (((sc : ℂ) ^ (r - a.1))⁻¹) ^ 2 * q.1 a) q.2

def psiP {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (u : Formalism.REAL.UJ ε) : Formalism.QuantumDeterminants.Mt k r :=
  fun i j => (P⁻¹ * uMat u * P) i j

def PFrame : Prop :=
  ∀ (r k : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e : Fin r → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (T T' : ℝ), FrameLoc ε k e z z' T T' → GoodPos ε e z z' →
    ∃ P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r ∧ IsUnit P.det ∧
      (∀ a, P *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) = e a) ∧
      ∃ zH zH' : Fin (2 * r + k + 1) → ℂ, Formalism.QuantumDeterminants.inWb k r zH ∧ Formalism.QuantumDeterminants.inWb k r zH' ∧
        P *ᵥ zH = z ∧ P *ᵥ zH' = z' ∧ Formalism.QuantumDeterminants.Tz k r zH = T ∧ Formalism.QuantumDeterminants.Tz k r zH' = T'

def SetCorr : Prop :=
  ∀ (r k : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e : Fin r → Fin (2 * r + k + 1) → ℂ) (z zH : Fin (2 * r + k + 1) → ℂ)
    (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r →
    IsUnit P.det →
    (∀ a, P *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) = e a) → Formalism.QuantumDeterminants.inWb k r zH → P *ᵥ zH = z →
    0 < Formalism.QuantumDeterminants.Tz k r zH →
    ∀ u : Formalism.REAL.UJ ε, u ∈ SLoc ε e z ↔ P⁻¹ * uMat u * P ∈ Formalism.QuantumDeterminants.Sset k r zH

def HaarCorr : Prop :=
  ∀ (r k : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e : Fin r → Fin (2 * r + k + 1) → ℂ) (z zH : Fin (2 * r + k + 1) → ℂ)
    (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r →
    IsUnit P.det →
    (∀ a, P *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) = e a) → Formalism.QuantumDeterminants.inWb k r zH → P *ᵥ zH = z →
    0 < Formalism.QuantumDeterminants.Tz k r zH → 1 ≤ k →
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) ((Formalism.REAL.muG ε).map (psiP P)) ∧
    ∀ μW μN : Measure (Formalism.QuantumDeterminants.Mt k r), Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r zH) μW →
      Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
      ∀ μS : Measure (Formalism.REAL.UJ ε), IsHaarS (SLoc ε e z) μS →
        ∃ c : ℝ, 0 < c ∧ μS.map (psiP P) = ENNReal.ofReal c • Formalism.MainNotions.S.muS μW μN

def ZBig : Prop :=
  ∀ (r k : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e : Fin r → Fin (2 * r + k + 1) → ℂ)
    (z z' zH zH' : Fin (2 * r + k + 1) → ℂ) (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (sc : ℝ),
    Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r → IsUnit P.det → (∀ a, P *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) = e a) →
    Formalism.QuantumDeterminants.inWb k r zH → Formalism.QuantumDeterminants.inWb k r zH' → P *ᵥ zH = z → P *ᵥ zH' = z' → 0 < sc →
    ∀ μsec, Formalism.QuantumDeterminants.IsSection k r zH zH' μsec →
    ∀ q : (Fin r → ℂ) × ℂ, (∀ a, q.1 a ≠ 0) → Formalism.QuantumDeterminants.Tz k r zH * Formalism.QuantumDeterminants.Tz k r zH' < Complex.normSq q.2 →
      Formalism.REAL.inUJ ε (P * Formalism.QuantumDeterminants.bigCell k r q.1 (μsec q.2) * P⁻¹) ∧
      Zhat ε (famSc sc e z) (famSc sc e z') (P * Formalism.QuantumDeterminants.bigCell k r q.1 (μsec q.2) * P⁻¹) =
        Matrix.diagonal (coordSc r sc q)

def BigMem : Prop :=
  ∀ (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) →
    μᴴ * Formalism.QuantumDeterminants.Hb k * μ = Formalism.QuantumDeterminants.Hb k → Formalism.QuantumDeterminants.bigCell k r c μ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)

def CoordW : Prop :=
  ∀ (r k : ℕ) (T T' sc : ℝ), 1 ≤ k → 0 < T → 0 < T' → 0 < sc →
    ∃ κ : ℝ, 0 < κ ∧ ∀ F : (Fin (r + 1) → ℂ) → ℝ≥0∞,
      ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) * F (coordSc r sc q) =
        ENNReal.ofReal κ * ∫⁻ c in GoodLoc (r := r) T T', ENNReal.ofReal (wtLoc k T T' c) * F c ∂(dcLoc (r := r))

def SecWb : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → Formalism.QuantumDeterminants.inWb k r z → Formalism.QuantumDeterminants.inWb k r z' →
    0 < Formalism.QuantumDeterminants.Tz k r z → 0 < Formalism.QuantumDeterminants.Tz k r z' → ∃ μsec, Formalism.QuantumDeterminants.IsSection k r z z' μsec

def JacExGoodN : Prop :=
  ∀ (r k : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e : Fin r → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (T T' sc : ℝ), FrameLoc ε k e z z' T T' → GoodPos ε e z z' → 0 < sc →
    ∃ h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε, IsSecLoc ε sc e z z' T T' h ∧
      ∀ μS μS' : Measure (Formalism.REAL.UJ ε), IsHaarS (SLoc ε e z) μS → IsHaarS (SLoc ε e z') μS' →
        ∃ C, 0 < C ∧ DisintLoc ε k T T' μS μS' h C

theorem jacExGood_of_N (H : JacExGoodN) : JacExGood := by
  intro n r k ε e z z' T T' sc hF hG hsc
  have hn : n = 2 * r + k + 1 := by have := hF.dim; omega
  subst hn
  exact H r k ε e z z' T T' sc hF hG hsc

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
