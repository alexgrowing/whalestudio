import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CM4
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementK
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.IsotropicVanish
import Formalism.FormalGroupLog.Statement

noncomputable section

namespace GlobalTheory.Honda

open PowerSeries

variable {K : Type} [NormedField K]

def Unr (K : Type) [NormedField K] (l : ℕ) (σ : K →+* K) : Prop :=
  l.Prime ∧ 2 < l ∧ ‖(l : K)‖ < 1 ∧ (∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖(l : K)‖) ∧ (∀ x : K, ‖σ x‖ = ‖x‖) ∧
    ∀ x : K, ‖x‖ ≤ 1 → ‖σ x - x ^ l‖ < 1

def ResAlg (K : Type) [NormedField K] : Prop :=
  ∀ f : Polynomial K, f.Monic → 0 < f.natDegree → (∀ n, ‖f.coeff n‖ ≤ 1) → ∃ x : K, ‖x‖ ≤ 1 ∧ ‖f.eval x‖ < 1

def CoefLe (r : ℝ) (f : K⟦X⟧) : Prop := ∀ n, ‖coeff n f‖ ≤ r

def frobOp (τ : K →+* K) (q i : ℕ) (f : K⟦X⟧) : K⟦X⟧ :=
  (PowerSeries.map (τ ^ i) f).subst ((X : K⟦X⟧) ^ (q ^ i))

def hondaSum (τ : K →+* K) (q : ℕ) (c : ℕ → K) (f : K⟦X⟧) : K⟦X⟧ :=
  PowerSeries.mk fun n => ∑ j ∈ Finset.range n, c j * coeff n (frobOp τ q (j + 1) f)

def IntLog [IsUltrametricDist K] (f e : K⟦X⟧) : Prop :=
  Formalism.L2.Th1.C.IsLogPair f e ∧ CoefLe 1 (derivative K f) ∧ Formalism.L2.Th1.C.FGInt (Formalism.G.unitBall K) f e

open Formalism.L2.Th1.CM in

def EndOmega : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), d % 4 = 3 → HasCMBy d L →
    ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ d → (¬ ∃ a : ZMod l, a ^ 2 = -(d : ZMod l)) →
    ∀ (ι : ℂ ≃+* ℂ_[l]) (g2 g3 : ℂ_[l]), IsGoodModel l L ι g2 g3 →
      ∀ n : ℕ, ‖coeff n ((uSer g2 g3).subst
        (C (ι (omegaK d)) * Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW g2 g3)))‖ ≤ 1

end GlobalTheory.Honda
