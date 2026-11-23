import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.ProjectionStatementOfFinal
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.OperatorExistsOfUnitaryContinuous
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.UnitaryRepUnimodularOfFiniteVolume
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.KernelDiagonalOfAbsoluteConvergence

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def cu.End (X : CData) : Prop :=
  cu.UnipFine X ∧ cu.LocGrowth X ∧ (∃ S : CSize X, S.Strata ∧ S.PackCount ∧ S.Inv ∧ S.Lip ∧ S.LowN) ∧ AbsKernelSquareIntegrable X ∧
    UnimodA X

def cu_StepsEnd (n₀ : ℕ) (A C : ℝ) : Prop :=
  ∀ X : CData, X.HypB n₀ A → X.GapAboveThreeHalvesPower → X.GapAboveSquareRootThreshold C → cu.End X

theorem projection_facts_of_schur (D : Formalism.BasicNotions.D7) (n₀ : ℕ) (A C : ℝ) (hn₀ : 1 ≤ n₀) (hC : 46 ≤ C) (ha1 : adm1 D)
    (ha2 : adm2 D) (ha8 : adm8 D) (hdec : DiscreteSeriesDecayBound D) (hloc : LocalProjectorRealPlace D) (hS : cu_StepsEnd n₀ A C) :
    StepsB n₀ A C := by
  intro X hX t1 t2
  by_cases h1 : X.e 1 = 0
  · exact projection_count_cusp_of_trivial_idempotent X hX h1
  · obtain ⟨sU, sL, sS, sK, sA⟩ := hS X hX t1 t2
    have hUm : UnimodF X := UnimodF_of_UnimodA X sA
    have hR : RepA X := unitary_rep_of_finite_adelic_unimodular X hX hUm h1
    obtain ⟨p, c⟩ := projection_and_count_facts D ha1 X hX (spherical_function_integrable_of_local D (integrable_one_place_of_local D hloc) n₀ A X hX t1) hR hUm
    have hF : cu.FinStep X := by
      intro T hT hP
      obtain ⟨κ, -⟩ := c T hT hP
      have hfd : FiniteDimensional ℂ (X.I.eHom X.σs X.μf X.fund X.R X.Re) :=
        ha8 X.I n₀ A X.b X.lam X.g X.g₀ X.e X.H X.σ X.w X.Hs X.σs X.tens X.μf X.fund X.R X.Re hX.1 hX.2.1
      exact Module.Finite.equiv κ
    exact ⟨p, c, cuspidal_range_of_final_facts X D hdec hn₀ hC hX t1 t2 (lowest_K_type_projector_exists D ha2 X hX) hF
      ⟨sU, sL, sS, kernel_diagonal_of_local_projector_of_abs_kernel_L2 D hloc X hX t1 sA sK, sA⟩⟩

end Formalism.MainNotions.LeviCoordinates
