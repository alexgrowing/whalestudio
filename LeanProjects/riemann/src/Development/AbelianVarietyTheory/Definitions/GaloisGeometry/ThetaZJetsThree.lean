import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementH
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementJ
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementE
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
import Formalism.LocalToGlobal.InertKernelTheory.StatementIota

noncomputable section

open scoped BigOperators
open Formalism.L2.Th1.H (cmL CmOK matH IsSelfDual Th alphaQ)
open Formalism.L2.Th1.GD (LocNorm)
open Formalism.L2.Th1.E (IntCurve Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace GlobalTheory.ThLoc

def LatAt (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0) {n : Type} [Fintype n]
    [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ) (p : ℕ) [Fact p.Prime]
    (ι : ℂ ≃+* ℂ_[p]) : Prop :=
  CmOK a₀ b₀ c₀ dK ∧ IsSelfDual (matH h) Λ ∧ (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ) ∧
    θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ ∧ LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι

def ThetaZJetsThree : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), d % 8 = 7 → d % 3 = 2 → Formalism.L2.Th1.CM.HasCMBy d L →
  ∀ (ι : ℂ ≃+* ℂ_[3]) (W : WeierstrassCurve ℂ_[3]), Unif 3 L ι W → IntCurve W →
  ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → Formalism.L2.Th1.CM.omegaK d * (ω₀ / 2) ∉ L.lattice →
    (starRingEnd ℂ) (Formalism.L2.Th1.CM.omegaK d) * (ω₀ / 2) ∉ L.lattice →
  ∀ (n : Type) [Fintype n] (κ : Type) [Fintype κ] (r : κ → ℂ_[3]) (s : κ → n → ℂ) (N : ℕ),
    (∀ k, ‖r k‖ ≤ 1) → 0 < N → ¬ 3 ∣ N → (∀ k i, (N : ℂ) * s k i ∈ L.lattice) →
    JetsIntegral (Formalism.L2.Th1.Top.thetaZ 3 L ι ω₀ r s)

structure Inputs : Prop where

  jInt : Formalism.L2.Th1.CM.JInvariantIntegrality

  modelTwo : Formalism.L2.Th1.Top.GoodModelTwo

  jetsOdd : Formalism.L2.Th1.GD.IntOpLoc

  jetsTwo : Formalism.L2.Th1.GD.IntOpTwoLoc

  jetsThree : ThetaZJetsThree

  shape : Formalism.L2.Th1.GD.EmbSep → Formalism.L2.Th1.GD.ShapeEigenLoc

  algT : Formalism.L2.KerInert.AlgTAll

  lamExt : Formalism.L2.KerInert.LamExt

namespace LatAt

variable {a₀ : ℕ} {b₀ c₀ : ℤ} {dK : ℕ} {ha : 0 < a₀} {hdK : 0 < dK} {lam : ℂ} {hlam : lam ≠ 0} {n : Type} [Fintype n]
  [DecidableEq n] {h : Matrix n n ℂ} {Λ : AddSubgroup (n → ℂ)} {θ : (n → ℂ) → ℂ} {p : ℕ} [Fact p.Prime] {ι : ℂ ≃+* ℂ_[p]}

theorem selfDual (H : LatAt a₀ b₀ c₀ dK ha hdK lam hlam h Λ θ p ι) : IsSelfDual (matH h) Λ := H.2.1

theorem stable (H : LatAt a₀ b₀ c₀ dK ha hdK lam hlam h Λ θ p ι) : ∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ := H.2.2.1

theorem mem_th (H : LatAt a₀ b₀ c₀ dK ha hdK lam hlam h Λ θ p ι) :
    θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ := H.2.2.2.1

theorem locNorm (H : LatAt a₀ b₀ c₀ dK ha hdK lam hlam h Λ θ p ι) : LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι := H.2.2.2.2

end LatAt

example : CmOK 1 1 2 7 := ⟨by norm_num, by decide, by norm_num, by norm_num⟩

example : CmOK 1 1 6 23 ∧ 23 % 8 = 7 ∧ 23 % 3 = 2 := ⟨⟨by norm_num, by decide, by norm_num, by norm_num⟩, by norm_num, by norm_num⟩

end GlobalTheory.ThLoc
