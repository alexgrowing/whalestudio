import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.GaussMean

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

def qEps {n : ℕ} (ε : Fin n → Bool) (y : Fin n → ℂ) : ℝ := ∑ i, (if ε i then 1 else -1) * ‖y i‖ ^ 2

def gauss {n : ℕ} (y : Fin n → ℂ) : ℝ := Real.exp (-∑ i, ‖y i‖ ^ 2)

def gaussDens {n : ℕ} (ε : Fin n → Bool) (β : ℝ) : ℝ :=
  deriv (fun t : ℝ => ∫ y in {y : Fin n → ℂ | qEps ε y ≤ t}, gauss y) β

def sgn (R : Type) [Ring R] (s : Bool) : R := if s then 1 else -1

def gaussSum (I : AutInst) (β : I.E) (x : I.GA) : ENNReal :=
  ∑' y : {y : Fin I.n → I.E // y ∈ lamX I x ∧ star y ⬝ᵥ (I.J *ᵥ y) = β},
    ENNReal.ofReal (∏ v, gauss (((uMat (x.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y.1 i)))

def meanConst (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ) : ℝ :=
  (2 * Formalism.HermitianLatticesTheory.vInv E) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) / 2) * (Formalism.HermitianLatticesTheory.vInv E ^ (M * Formalism.HermitianLatticesTheory.fDeg E))⁻¹ /
    Formalism.HermitianLatticesTheory.lValEta E M

def SiegelMean : Prop :=
  ∀ (I : AutInst), 3 ≤ I.n → ∀ (s : Bool) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
    (fund : Set I.GA), I.IsFundDom (I.muA μf) fund →
    I.muA μf fund < ⊤ ∧
    ∫⁻ x in fund, gaussSum I (sgn I.E s) x ∂(I.muA μf) =
      I.muA μf fund * ENNReal.ofReal (meanConst I.E I.n * ∏ v, gaussDens (I.ε v) (sgn ℝ s))

def IsPerpInst (I I' : AutInst) (e : I'.E ≃+* I.E) (s : Bool) (x : Fin I.n → I.E)
    (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf) : Prop :=
  (∀ y, e (star y) = star (e y)) ∧ I'.n + 1 = I.n ∧ star x ⬝ᵥ (I.J *ᵥ x) = sgn I.E s ∧
    star x ᵥ* (I.J * A) = 0 ∧ Aᴴ * I.J * A = I'.J.map e ∧ x ∈ lamX I (1, xf) ∧
    ∀ y : Fin I'.n → I'.E, y ∈ I'.L ↔ A *ᵥ (fun i => e (y i)) ∈ lamX I (1, xf)

def GaugeUnfold : Prop :=
  ∀ (I I' : AutInst) (e : I'.E ≃+* I.E) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E)
    (xf : I.Gf), 3 ≤ I.n → IsPerpInst I I' e s x A xf →
    ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
      (c' : InfinitePlace I'.F → ℝ) (μf' : Measure I'.Gf) [SigmaFinite μf'] [μf'.IsHaarMeasure]
      (fund : Set I.GA), IsGaugeAll I c → IsGaugeAll I' c' → I.IsFundDom (I.muA μf) fund →
      ENNReal.ofReal (∏ v, c v) * (∫⁻ g in fund, gaussSum I (sgn I.E s) g ∂(I.muA μf)) / μf I.Kset =
        gaugeVol I' c' μf' * ENNReal.ofReal (2 ^ (I.n * I.f) * ∏ v, gaussDens (I.ε v) (sgn ℝ s))

theorem gauss_pos {n : ℕ} (y : Fin n → ℂ) : 0 < gauss y := Real.exp_pos _

example : qEps (fun _ : Fin 1 => true) (fun _ => 1) = 1 := by simp [qEps]

end GlobalTheory.GaussMean
