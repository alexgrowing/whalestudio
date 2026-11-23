import Formalism.LocalToGlobal.InertKernelTheory.StatementBe
import Formalism.LocalToGlobal.InertKernelTheory.DefsSigma

noncomputable section

namespace Formalism.L2.KerInert

open Formalism.MainNotions.GL3Theta Formalism.L2.G.Pend

def GenusOneModelExists : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ),
    Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], Nat.Coprime (Ideal.absNorm cc) p → 5 ≤ p → InertK D p →
    ∀ lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p],
      ∃ g : G1 p, g.lam = lam ∧ At D cc δ g ∧ ModelOverW g.lam g.abelian₂ g.C ∧ LTIso g

def GenusOneModelExistsLattice : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ),
    Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → InertK D p →
    ∀ lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p],
      ∃ (cc' : Ideal (NumberField.RingOfIntegers D.host.K)) (δ' : ℂ) (g : G1 p),
        Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc' ∧ Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc' δ' ∧
        Formalism.MainNotions.TaylorLogMetric.lamOf D cc' δ' = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ ∧
        g.lam = lam ∧ At D cc' δ' g ∧ ModelOverW g.lam g.abelian₂ g.C ∧ LTIso g

def GenusOneLubinTateModelExists : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ),
    Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], Nat.Coprime (Ideal.absNorm cc) p → 5 ≤ p → InertK D p →
    ∀ lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p], beW D →
      ∃ (g : G1 p) (_ : LTIso g), g.lam = lam ∧
        At D cc δ g ∧ 5 ≤ p ∧ InertK D p ∧ ModelOverW g.lam g.abelian₂ g.C ∧ BeWAt D g

def CurveDatumEx : Prop :=
  ∀ D : Formalism.BasicNotions.D7, ∃ (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ),
    Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc ∧ Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ ∧ ∀ p : ℕ, Nat.Coprime (Ideal.absNorm cc) p

end Formalism.L2.KerInert
