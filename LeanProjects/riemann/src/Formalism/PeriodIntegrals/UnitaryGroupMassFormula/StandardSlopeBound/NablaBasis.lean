import Formalism.PeriodIntegrals.HookBound
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord

noncomputable section

namespace PI.SlopeSteps

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.L2.DIV

def gramOf {N : ℕ} (ν : Fin N → ℕ) {r : ℕ} (e : Fin r → MvPolynomial (Fin N × Fin N) ℤ) : Matrix (Fin r) (Fin r) ℚ :=
  Matrix.of fun i j =>
    fockQ (map (Int.castRingHom ℚ) (e i)) (map (Int.castRingHom ℚ) (e j)) / fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν)

def MonoFactLow : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ) (m : Fin N × Fin N →₀ ℕ), (∀ s, ∑ a, m (a, s) = ν s) →
    ∏ s, (ν s).factorial ≤ N ^ (∑ s, ν s) * ∏ k ∈ m.support, (m k).factorial

def NablaGramLow : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ) (r : ℕ) (e : Module.Basis (Fin r) ℤ (dualWeyl ℤ N N ν)), Antitone ν →
    (((∏ s, (ν s).factorial : ℕ) : ℚ) / ((N : ℚ) ^ (∑ s, ν s) * fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν))) ^ r ≤
      (gramOf ν fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ)).det

def GramDual : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ) (r r' : ℕ) (e : Module.Basis (Fin r) ℤ (weyl ℤ N N le_rfl ν))
    (e' : Module.Basis (Fin r') ℤ (dualWeyl ℤ N N ν)), Antitone ν →
    r = r' ∧ (gramOf ν fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ)).det *
      (gramOf ν fun i => (e' i : MvPolynomial (Fin N × Fin N) ℤ)).det = 1

def NablaBasis : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ), ∃ (r : ℕ), Nonempty (Module.Basis (Fin r) ℤ (dualWeyl ℤ N N ν))

def StdSlopeLowOf : Prop := NablaGramLow → GramDual → NablaBasis → PI.StdSlopeLow

example {N : ℕ} (ν : Fin N → ℕ) {r : ℕ} (e : Module.Basis (Fin r) ℤ (weyl ℤ N N le_rfl ν)) :
    PI.stdGram ν e = gramOf ν fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ) := rfl

end PI.SlopeSteps
