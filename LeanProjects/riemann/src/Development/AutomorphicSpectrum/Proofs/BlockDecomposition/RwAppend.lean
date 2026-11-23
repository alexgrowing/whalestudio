import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarChartIntegralComparison

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.PresSobA

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.SobGL.HaarDom

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

abbrev CLof (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] : Type :=
  E →L[ℝ] F

def expC (X : Mat n) (t : ℝ) : G n := (Matrix.isUnit_exp (t • X)).unit

theorem expC_val (X : Mat n) (t : ℝ) : (expC X t).val = NormedSpace.exp (t • X) := rfl

theorem expC_zero (X : Mat n) : expC X 0 = 1 := by
  apply Units.ext
  simp [expC_val]

def IsTest (φ : Mat n → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ GLs n

section Mol

variable [MeasurableSpace (G n)] (μ : Measure (G n))

def Mol {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (φ : Mat n → ℝ) (x : G n → V) (z : Mat n) : V :=
  ∫ u : G n, φ (z * (u⁻¹ : G n).val) • x u ∂μ

variable [BorelSpace (G n)] [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def lT (y : G n) : Lp V 2 μ →L[ℂ] Lp V 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun z : G n => y⁻¹ * z) (measurePreserving_mul_left μ y⁻¹)).toContinuousLinearMap

def lConv (φ : Mat n → ℝ) (x : Lp V 2 μ) : Lp V 2 μ := ∫ y : G n, φ y.val • lT μ V y x ∂μ

variable {V}

theorem lT_coe (y : G n) (x : Lp V 2 μ) : lT μ V y x =ᵐ[μ] fun z => x (y⁻¹ * z) :=
  Lp.coeFn_compMeasurePreserving x (measurePreserving_mul_left μ y⁻¹)

theorem rR_coe (hU : Unimod) (h : G n) (x : Lp V 2 μ) : rR μ V h x =ᵐ[μ] fun z => x (z * h) := by
  haveI := (hU n μ).1
  have hm : MeasurePreserving (fun y : G n => y * h) μ μ := measurePreserving_mul_right μ h
  have : rR μ V h x = Lp.compMeasurePreserving (fun y : G n => y * h) hm x := by
    simp only [rR, dif_pos hm]
    rfl
  rw [this]
  exact Lp.coeFn_compMeasurePreserving x hm

theorem cls_of_ae {f : Mat n → V} {x : Lp V 2 μ} (h : (fun y : G n => f y.val) =ᵐ[μ] x) :
    MemLp (fun y : G n => f y.val) 2 μ ∧ cls μ f = x := by
  have hm : MemLp (fun y : G n => f y.val) 2 μ := (memLp_congr_ae h).2 (Lp.memLp x)
  refine ⟨hm, ?_⟩
  simp only [cls, dif_pos hm]
  exact Lp.ext (hm.coeFn_toLp.trans h)

theorem coe_cls {f : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) :
    (cls μ f : G n → V) =ᵐ[μ] fun y => f y.val := by
  simp only [cls, dif_pos h]
  exact h.coeFn_toLp

end Mol

theorem isOpen_GLs : IsOpen (GLs n) := by
  have : Continuous fun g : Mat n => g.det := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage this

section Words

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_congr {f f' : Mat n → V} (h : ∀ z ∈ GLs n, f z = f' z) (X : Mat n) :
    ∀ z ∈ GLs n, Rd X f z = Rd X f' z := by
  intro z hz
  have : f =ᶠ[𝓝 z] f' := Filter.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hz) h
  simp only [Rd, this.fderiv_eq]

theorem Rw_append (w w' : List (Bool × Fin n × Fin n)) (f : Mat n → V) :
    Rw (w ++ w') f = Rw w (Rw w' f) := by
  induction w with
  | nil => rfl
  | cons p w ih => simp only [List.cons_append, Rw, ih]

end Words

end GlobalTheory.CompanionTheory.PresSobA
