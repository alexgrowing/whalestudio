import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudy
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization ComplexConjugate Matrix ENNReal
open MeasureTheory Set MvPolynomial

noncomputable section

namespace CP

variable {N : ℕ}

def lineOf (v : Fin (N + 1) → ℂ) : CP N :=
  if h : v = 0 then chartInv 0 0 else Projectivization.mk ℂ v h

lemma lineOf_of_ne {v : Fin (N + 1) → ℂ} (hv : v ≠ 0) : lineOf v = Projectivization.mk ℂ v hv :=
  dif_neg hv

def ambDensity (v : Fin (N + 1) → ℂ) : ℝ := 1 / (1 + normSq2 v) ^ (N + 2)

def ambMeasure (N : ℕ) : Measure (Fin (N + 1) → ℂ) :=
  volume.withDensity fun v => ENNReal.ofReal (ambDensity v)

lemma unitary_injective (U : Matrix.unitaryGroup (Fin (N + 1)) ℂ) :
    Function.Injective (Matrix.toLin' (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) := by
  intro v w h
  have hU : star (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) * U = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.2
  have h' := congrArg (fun x => star (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) *ᵥ x) h
  simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hU] using h'

def unitaryAct (U : Matrix.unitaryGroup (Fin (N + 1)) ℂ) : CP N → CP N :=
  Projectivization.map (Matrix.toLin' (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ))
    (unitary_injective U)

lemma unitaryAct_mk (U : Matrix.unitaryGroup (Fin (N + 1)) ℂ) (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) :
    unitaryAct U (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ (Matrix.toLin' (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) v)
        (fun h0 => hv (unitary_injective U (by rw [h0, map_zero]))) := rfl

def diagUnitary (ζ : Fin (N + 1) → unitary ℂ) : Matrix.unitaryGroup (Fin (N + 1)) ℂ :=
  ⟨Matrix.diagonal fun i => (ζ i : ℂ), by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    show star (ζ i : ℂ) * (ζ i : ℂ) = 1
    exact Unitary.star_mul_self_of_mem (ζ i).2⟩

def fsPair (n : ℕ) (P Q : MvPolynomial (Fin (N + 1)) ℂ) (x : CP N) : ℂ :=
  conj (eval x.rep P) * eval x.rep Q / ((norm2 x.rep ^ (2 * n) : ℝ) : ℂ)

def l2Inner (n : ℕ) (P Q : MvPolynomial (Fin (N + 1)) ℂ) : ℂ := ∫ x, fsPair n P Q x ∂fsMeasure N

end CP

namespace FSInv

open CP

def LinChange.Statement : Prop :=
  ∀ (n : ℕ) (f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)), LinearMap.det f ≠ 0 →
    ∀ g : (Fin n → ℂ) → ℝ≥0∞, Measurable g →
      ∫⁻ u, g u = ENNReal.ofReal (Complex.normSq (LinearMap.det f)) * ∫⁻ z, g (f z)

def Radial.Statement : Prop :=
  ∀ (N : ℕ) (s : ℝ), 0 < s →
    ∫⁻ t : ℂ, ENNReal.ofReal (‖t‖ ^ (2 * N) * (1 / (1 + ‖t‖ ^ 2 * s) ^ (N + 2))) =
      ENNReal.ofReal (Real.pi / (N + 1)) * ENNReal.ofReal (1 / s ^ (N + 1))

def AmbChart.Statement : Prop :=
  ∀ (N : ℕ) (i : Fin (N + 1)) (f : CP N → ℝ≥0∞), Measurable f →
    ∫⁻ v, f (lineOf v) ∂ambMeasure N = ENNReal.ofReal (Real.pi / (N + 1)) *
      ∫⁻ z, f (chartInv i z) * ENNReal.ofReal (1 / (1 + normSqSum z) ^ (N + 1))

def AmbEq.Statement : Prop :=
  ∀ N : ℕ, fsMeasure N =
    ENNReal.ofReal ((N + 1).factorial / Real.pi ^ (N + 1)) • (ambMeasure N).map lineOf

def ChartIndep.Statement : Prop :=
  ∀ (N : ℕ) (i : Fin (N + 1)), fsMeasure N = (fsChartMeasure i).map (chartInv i)

def AmbUnitary.Statement : Prop :=
  ∀ (N : ℕ) (U : Matrix.unitaryGroup (Fin (N + 1)) ℂ),
    (ambMeasure N).map (Matrix.toLin' (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) = ambMeasure N

def UnitaryInv.Statement : Prop :=
  ∀ (N : ℕ) (U : Matrix.unitaryGroup (Fin (N + 1)) ℂ),
    MeasurePreserving (unitaryAct U) (fsMeasure N) (fsMeasure N)

def FormIntegral.Statement : Prop :=
  ∀ (N : ℕ) (i : Fin (N + 1)) (g : CP N → ℝ), AEStronglyMeasurable g (fsMeasure N) →
    ∫ x, g x ∂fsMeasure N =
      ∫ z, g (chartInv i z) * ((N.factorial : ℝ) * 2 ^ N * (chernCoeff i z).det.re)

def PairMk.Statement : Prop :=
  ∀ (N n : ℕ) (P Q : MvPolynomial (Fin (N + 1)) ℂ), P ∈ H0 N n → Q ∈ H0 N n →
    ∀ (v : Fin (N + 1) → ℂ) (hv : v ≠ 0),
      fsPair n P Q (Projectivization.mk ℂ v hv) =
        conj (eval v P) * eval v Q / ((norm2 v ^ (2 * n) : ℝ) : ℂ)

def InnerSelf.Statement : Prop :=
  ∀ (N n : ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ),
    l2Inner (N := N) n P P = (sectionL2NormSq (N := N) n P : ℂ)

def Sesq.Statement : Prop :=
  ∀ (N n : ℕ) (P Q R : MvPolynomial (Fin (N + 1)) ℂ), P ∈ H0 N n → Q ∈ H0 N n → R ∈ H0 N n →
    ∀ c : ℂ,
      l2Inner (N := N) n (P + c • Q) R = l2Inner n P R + conj c * l2Inner n Q R ∧
      l2Inner (N := N) n R (P + c • Q) = l2Inner n R P + c * l2Inner n R Q ∧
      l2Inner (N := N) n Q P = conj (l2Inner n P Q)

def Orth.Statement : Prop :=
  ∀ (N : ℕ) (a b : Fin (N + 1) →₀ ℕ), a ≠ b → a.degree = b.degree →
    l2Inner (N := N) a.degree (monomial a (1 : ℂ)) (monomial b 1) = 0

def Parseval.Statement : Prop :=
  ∀ (N n : ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ), P ∈ H0 N n →
    l2Norm (N := N) n P ^ 2 = ∑ a ∈ P.support,
      ‖P.coeff a‖ ^ 2 * ((∏ i, ((a i).factorial : ℝ)) * N.factorial / (n + N).factorial)

def Definite.Statement : Prop :=
  ∀ (N n : ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ), P ∈ H0 N n →
    (l2Inner (N := N) n P P = 0 ↔ P = 0)

example : LinearMap.det ((2 : ℂ) • LinearMap.id : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) ≠ 0 := by
  rw [LinearMap.det_smul, LinearMap.det_id]; norm_num

example : ((diagUnitary (N := 1) ![1, ⟨-1, by simp [Unitary.mem_iff]⟩] :
    Matrix (Fin 2) (Fin 2) ℂ) 1 1) = -1 := by
  simp [diagUnitary]

example : (Finsupp.single (0 : Fin 2) 1) ≠ Finsupp.single 1 1 ∧
    (Finsupp.single (0 : Fin 2) 1).degree = (Finsupp.single (1 : Fin 2) 1).degree := by
  refine ⟨fun h => ?_, by simp⟩
  have := congrArg (fun f => f 0) h
  simp at this

example : (X 0 : MvPolynomial (Fin 2) ℂ) ∈ H0 1 1 ∧ (![1, 0] : Fin 2 → ℂ) ≠ 0 :=
  ⟨(mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X ℂ 0), fun h => by
    simpa using congrFun h 0⟩

end FSInv

end

end GroundTheory.Heights₂.Heights
