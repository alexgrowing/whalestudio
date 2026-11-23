import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.LocTauAlt

noncomputable section

open MeasureTheory Matrix Set

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

def ub2 (x : M2 n) : Matrix (Fin n) (Fin n) ℂ := -x⁻¹.toBlocks₁₁ + Complex.I • x⁻¹.toBlocks₂₁

def Om (x : M2 n) : Matrix (Fin n) (Fin n) ℂ := ub2 x * (ub1 x)⁻¹

def eQ (m : ℕ) (e : ℤ) (z : ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) (x : M2 n) : ℂ := fz m e z x * (Om x * Q).trace

def rhoP {Kg : Type} (ι : Kg → M2 n) (m : ℕ) (e : ℤ) (Y : Matrix (Fin n) (Fin n) ℂ) (k : Kg) : ℂ :=
  star (fz m e 0 (ι k) * ((u2 (ι k))⁻¹ * Y * u1 (ι k)).trace)

def LoweringDerivativeVacuum : Prop :=
  ∀ (n m : ℕ) (e : ℤ) (z : ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) (x : M2 n), InG x → rC (lowQ Q) (fz m e z) x = z * eQ m e z Q x

def MultiplicityOneTestOperators : Prop :=
  ∀ (n m : ℕ) (e : ℤ) (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n), Continuous ι →
    (∀ g, InK g ↔ ∃ k, ι k = g) → ∀ (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b : M2 n),
    Continuous ψ → HasCompactSupport ψ → InG a → InG b →
    ∃ c : ℂ → ℂ, Differentiable ℂ c ∧ ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (x : M2 n), InG x →
      tOp μ ι (rhoP ι m e Y) ψ a b (fz m e z) x = eQ m e z (c z • Yᴴ) x

def SingularTestsKillVacuum : Prop :=
  ∀ (n m : ℕ) (e : ℤ), m < n → ∀ (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n), Continuous ι →
    (∀ g, InK g ↔ ∃ k, ι k = g) → ∀ (ρ : Kg → ℂ) (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b x : M2 n), Continuous ρ →
    IsSingTest ψ → InG a → InG b → InG x → tOp μ ι ρ ψ a b (fz m e 0) x = 0

def Crux : Prop :=
  ∀ (n m : ℕ) (e : ℤ), m < n → ∀ (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n), Continuous ι →
    (∀ g, InK g ↔ ∃ k, ι k = g) → ∃ (P : Matrix (Fin n) (Fin n) ℂ) (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b x : M2 n),
      IsSingTest ψ ∧ InG a ∧ InG b ∧ InG x ∧ deriv (fun z => tOp μ ι (rhoP ι m e P) ψ a b (fz m e z) x) 0 ≠ 0

def AsmLT : Prop := LoweringDerivativeVacuum → MultiplicityOneTestOperators → SingularTestsKillVacuum → Crux → LocTau

end PositivityTheory.Rg.Sw.HSt
