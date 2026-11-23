import Formalism.PeriodIntegrals.NUnimodLoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnimodularLattice.NonstandardUnimodularLattice

open MeasureTheory Matrix

noncomputable section

namespace PI.NUnimodLoc.UnitaryGroupMassFormula

open PI PI.QuotSetU

def FrameConj : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e f : Fin r → Fin (2 * r + k + 1) → ℂ)
    (wf : Fin k → Fin (2 * r + k + 1) → ℂ) (z0 z : Fin (2 * r + k + 1) → ℂ) (c : ℂ),
    IsFrameJ ε e f wf z0 → c ≠ 0 → z0 = c • z →
    ∃ P Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Q * P = 1 ∧ P * Q = 1 ∧
      ∀ g, (Formalism.REAL.inUJ ε g ∧ InN ε e z g) ↔ Q * g * P ∈ Nset k r

def Transfer : Prop :=
  ∀ (m : ℕ) (ε : Fin m → Bool) (T S : Set (Matrix (Fin m) (Fin m) ℂ))
    (P Q : Matrix (Fin m) (Fin m) ℂ), Q * P = 1 → P * Q = 1 →
    (∀ g, (Formalism.REAL.inUJ ε g ∧ g ∈ T) ↔ Q * g * P ∈ S) →
    (∀ μ : Measure (MtM m), IsHaarOnM S μ → IsRightInvM S μ) →
    ∀ μ : Measure (Formalism.REAL.UJ ε), SigmaFinite μ → μ ≠ 0 → μ {g : Formalism.REAL.UJ ε | uMat g ∈ T}ᶜ = 0 →
      (∀ s ∈ {g : Formalism.REAL.UJ ε | uMat g ∈ T}, μ.map (fun x => s * x) = μ) →
      ∀ s ∈ {g : Formalism.REAL.UJ ε | uMat g ∈ T}, μ.map (fun x => x * s) = μ

theorem nUnimodLoc_of (hF : FrameConj) (hT : Transfer) : NUnimodLoc := by
  intro k r ε e f wf z0 z c hfr hc hz μ hμ hne hsupp hleft
  obtain ⟨P, Q, hQP, hPQ, hiff⟩ := hF k r ε e f wf z0 z c hfr hc hz
  exact hT (2 * r + k + 1) ε {g | InN ε e z g} (Nset k r) P Q hQP hPQ (fun g => hiff g)
    (nonstandard_unimodular_lattice k r) μ hμ hne hsupp hleft

end PI.NUnimodLoc.UnitaryGroupMassFormula
