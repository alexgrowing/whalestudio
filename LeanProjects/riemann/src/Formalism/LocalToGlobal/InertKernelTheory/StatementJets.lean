import Formalism.LocalToGlobal.InertKernelTheory.StatementInt

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

def dYu {p : ℕ} [Fact p.Prime] (C : WeierstrassCurve.VariableChange ℂ_[p]) (W : WeierstrassCurve ℂ_[p])
    (wq : PowerSeries ℂ_[p]) (g : PowerSeries ℂ_[p]) : PowerSeries ℂ_[p] :=
  algebraMap ℂ_[p] (PowerSeries ℂ_[p]) ((C.u : ℂ_[p]ˣ) : ℂ_[p]) * (dX (flog W wq))⁻¹ * dX g

def OrthBasisExists : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
      admitted D N N' L L' →
      ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b ∧ Orthonormal D b

def ModelExists : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 → ∀ lam : Qbar →+* ℂ_[p],
      ∃ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]),
        IsModel lam (lamOf D cc δ) C ∧ IsWq (C • wModel lam (lamOf D cc δ)) wq

def LogDerInt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]),
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → IsWq W wq →
      PowerSeries.constantCoeff (dX (flog W wq)) = 1 ∧ ∀ n, IsIntP (PowerSeries.coeff n (dX (flog W wq)))

def VariableChangeUnitIntegralAtInertPrimes : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (lam : Qbar →+* ℂ_[p]) (C : WeierstrassCurve.VariableChange ℂ_[p]),
      IsModel lam (lamOf D cc δ) C → IsIntP ((C.u : ℂ_[p]ˣ) : ℂ_[p])

def PhiJetInt : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (lam : Qbar →+* ℂ_[p]) (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]),
      IsModel lam (lamOf D cc δ) C → IsWq (C • wModel lam (lamOf D cc δ)) wq →
      PowerSeries.constantCoeff (ePhi1 lam (lamOf D cc δ) C wq) = 1 ∧
      ∀ n : ℕ, IsIntP (PowerSeries.constantCoeff
        ((dYu C (C • wModel lam (lamOf D cc δ)) wq)^[n] (ePhi1 lam (lamOf D cc δ) C wq)))

def JetsOfInt : Prop :=
  IntInert → OrthBasisExists → ModelExists → LogDerInt → VariableChangeUnitIntegralAtInertPrimes → PhiJetInt → JetsInert

end Formalism.L2.KerInert
