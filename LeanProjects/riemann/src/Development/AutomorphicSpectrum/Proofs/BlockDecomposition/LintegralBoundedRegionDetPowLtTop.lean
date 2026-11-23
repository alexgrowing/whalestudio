import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GodementJacquetMinusOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhdEqPhk
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GodementJacquetMinusTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOnModulusPowBall

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel ENNReal NNReal

namespace GlobalTheory.CompanionTheory.GLFinVol

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def Tset (c B : ℝ) : Set (GL (Fin 2) F) :=
  {g | (∀ j, (modulus (g.val 0 j / (g.val).det) : ℝ) ≤ c ∧ (modulus (g.val 1 j) : ℝ) ≤ c) ∧
    (modulus (g.val).det : ℝ) ≤ B}

def Qset (c : ℝ) : Set (GL (Fin 2) F) :=
  {g | modulus (g.val).det = 1 ∧ ∀ i j, (modulus (g.val i j) : ℝ) ≤ c}

def Vset (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    Set F := {y | y - 1 ∈ valBall F 1}

section Meas

variable [MeasurableSpace F] [BorelSpace F]

theorem measurable_entry (i j : Fin 2) :
    Measurable fun g : GL (Fin 2) F => modulus (g.val i j) :=
  (continuous_modulus.comp ((continuous_id.matrix_elem i j).comp Units.continuous_val)).measurable

theorem measurable_detm : Measurable fun g : GL (Fin 2) F => modulus (g.val).det :=
  (continuous_modulus.comp (Continuous.matrix_det Units.continuous_val)).measurable

theorem ball_lt_top (μ : Measure F) [μ.IsAddHaarMeasure] (c : ℝ) :
    μ {x : F | (modulus x : ℝ) ≤ c} < ⊤ := by
  have hq1 : (1 : ℝ) < (residueCard F : ℝ) := by exact_mod_cast one_lt_residueCard (K := F)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt c hq1
  refine lt_of_le_of_lt (measure_mono ?_) (isCompact_valBall (K := F) (-(n : ℤ))).measure_lt_top
  intro x hx
  by_cases h0 : x = 0
  · rw [h0]
    exact zero_mem _
  have hmod : (modulus x : ℝ) = (residueCard F : ℝ) ^ (-ord x) := by
    rw [modulus_of_ne_zero h0]
    push_cast
    rfl
  have h1 : (residueCard F : ℝ) ^ (-ord x) < (residueCard F : ℝ) ^ (n : ℤ) := by
    rw [zpow_natCast, ← hmod]
    exact lt_of_le_of_lt hx hn
  have h2 := (zpow_lt_zpow_iff_right₀ hq1).1 h1
  rw [SetLike.mem_coe, mem_valBall_iff_le_ord h0]
  omega

def Aint (μ : Measure F) (B e : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, {y : F | (modulus y : ℝ) ≤ B}.indicator
    (fun y => ENNReal.ofReal ((modulus y : ℝ) ^ (e - 1))) y ∂μ

end Meas

end GlobalTheory.CompanionTheory.GLFinVol
