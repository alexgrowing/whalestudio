import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CruxSt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TwoSided

noncomputable section

open MeasureTheory Matrix Set

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def Fd (m : ℕ) (y : M2 n) : ℂ := deriv (fun z : ℂ => fz m 0 z y) 0

def Crux0 : Prop :=
  ∀ (n m : ℕ), m < n → ∀ (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n), Continuous ι →
    (∀ g, InK g ↔ ∃ k, ι k = g) → ∃ (P : Matrix (Fin n) (Fin n) ℂ) (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b x : M2 n),
      IsSingTest ψ ∧ InG a ∧ InG b ∧ InG x ∧ deriv (fun z => tOp μ ι (rhoP ι m 0 P) ψ a b (fz m 0 z) x) 0 ≠ 0

def ERed : Prop := Crux0 → Crux

def FdProps : Prop :=
  ∀ (n m : ℕ), ContDiffOn ℂ ⊤ (Fd (n := n) m) (DomZ n) ∧
    ∀ (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
      [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n), Continuous ι →
      (∀ g, InK g ↔ ∃ k, ι k = g) → ∀ (ρ : Kg → ℂ) (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b x : M2 n), Continuous ρ →
      Continuous ψ → HasCompactSupport ψ → InG a → InG b → InG x →
      deriv (fun z => tOp μ ι ρ ψ a b (fz m 0 z) x) 0 = tOp μ ι ρ ψ a b (Fd m) x

def DjFd : Prop :=
  ∀ (n m j : ℕ) (x : M2 n), 1 ≤ j → j ≤ n → x ∈ DomZ n →
    detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
      Fd m (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1))) =
    deriv (fun z : ℂ => (∏ i ∈ Finset.range j, ((i : ℂ) - z)) * (∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z))) 0 *
      hF j m 0 x

def FdInv : Prop :=
  ∀ (n m j : ℕ) (x P S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ), True

def KSplit : Prop :=
  ∀ (n m : ℕ) (a0 b0 : Fin n) (Kg : Type) [Group Kg] (ι : Kg →* M2 n), (∀ g, InK g ↔ ∃ k, ι k = g) →
    ∃ (L : ℕ) (c : Fin L → ℂ) (kl : Fin L → Kg), ∀ k,
      fV m 0 (ι k) * ((u1 (ι k))⁻¹ * u2 (ι k)) b0 a0 = ∑ l, c l * rhoP ι m 0 1 (k * kl l)

def SphU : Prop :=
  ∀ (n : ℕ) (F : M2 n → ℂ) (U : Set (M2 n)), IsOpen U → ContDiffOn ℂ ⊤ F U →
    ∀ {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
    (μ : Measure Kg) [IsFiniteMeasure μ] [IsFiniteMeasureOnCompacts μ] (ι : Kg → M2 n), Continuous ι →
    ∀ (c : Kg → ℂ), Continuous c → ∀ {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (LA : M2 n → Matrix ιA ιA ℂ →L[ℂ] M2 n) (LB : M2 n → Matrix ιB ιB ℂ →L[ℂ] M2 n),
    (∀ M x T, LA (M * x) T = M * LA x T) → (∀ M x S, LB (M * x) S = M * LB x S) →
    ∀ (g : M2 n), (∀ k, ι k * g ∈ U) →
    detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
        ∫ k, F (ι k * (g + LA g T + LB g S)) * c k ∂μ)) =
      ∫ k, detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
        F (ι k * g + LA (ι k * g) T + LB (ι k * g) S))) * c k ∂μ

end PositivityTheory.Rg.Sw.HSt
