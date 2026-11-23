import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.KernelDiagonalOfTriangleInequality
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.TheoremCountStatementOfGeometry
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.ProjectionStatementOfEnd
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.FormalDegreeOfSchurOrth
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.TraceConjMulEqHilbertSchmidt
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalL1StatementOfProjectors
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyProjectorSectionLocal
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionConvolutionIdentity

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def VolumeCountGeometryConditions (n₀ : ℕ) (A C cb cε Cv Cd Cq : ℝ) : Prop :=
  ∀ X : CData, X.HypC n₀ A C cb → X.FinVol ∧ AllCount X (2 * (X.I.n : ℝ) ^ 2) ∧ GeoS X cε Cv Cd Cq

theorem kernel_geometry_conditions_of_volume_count : ∃ C₃ : ℝ, ∀ (D : Formalism.BasicNotions.D7) (n₀ : ℕ) (A C cb cε Cv Cd Cq : ℝ), 1 ≤ n₀ → C₃ ≤ C →
    adm2 D → DiscreteSeriesDecayBound D → LocalProjectorRealPlace D → DistTri → VolumeCountGeometryConditions n₀ A C cb cε Cv Cd Cq → StepsG'' n₀ A C cb cε Cv Cd Cq := by
  obtain ⟨Ch, -, hH⟩ := Formalism.HermitianLatticeCounting.Final.S7.threshHead 363
  refine ⟨Ch, fun D n₀ A C cb cε Cv Cd Cq hn hC h2 hdec hloc htri hS X hX => ?_⟩
  obtain ⟨hV, hcnt, hG⟩ := hS X hX
  obtain ⟨t1, t2⟩ := gap_thresholds_of_height_bound hH X hn hC hX
  have hd := RegData_of_HypB X hX.1
  have hu := adelic_unimodular_of_finite_covolume X hd hV
  exact ⟨regularRep_measurable_of_finite_volume X hd hV,
    kernel_diagonal_of_triangle_inequality D h2 hdec hloc X hX.1 (le_trans hn hX.1.1.1) t1 t2 hu htri hcnt, hV, hG⟩

theorem packet_bound_of_volume_count_geometry : ∃ c' cb : ℝ, 0 < c' ∧ 0 < cb ∧ ∀ Cd Cq Cv Cres A Cb cε : ℝ, 1 ≤ Cd → 0 ≤ Cq → 16 * Cq ≤ Cd → 1 ≤ Cv →
    1 ≤ A → 0 < cε → cε ≤ 1 / 90000 →
    ∃ (n₁ : ℕ) (C₂ : ℝ), ∀ (D : Formalism.BasicNotions.D7) (n₀ : ℕ) (C : ℝ), n₁ ≤ n₀ → C₂ ≤ C → adm2 D → adm7 D Cres → DiscreteSeriesDecayBound D →
      LocalProjectorRealPlace D → Conclusion2 D n₀ A Cb → DistTri → VolumeCountGeometryConditions n₀ A C cb cε Cv Cd Cq → PointsLemma D n₀ A C c' cb := by
  obtain ⟨c', cb, hc', hcb, h⟩ := theorem_count_of_geometry
  obtain ⟨C₃, h3⟩ := kernel_geometry_conditions_of_volume_count
  refine ⟨c', cb, hc', hcb, fun Cd Cq Cv Cres A Cb cε hCd hCq hCC hCv hA hcε hcε2 => ?_⟩
  obtain ⟨n₁, C₂, h⟩ := h Cd Cq Cv Cres A Cb cε hCd hCq hCC hCv hA hcε hcε2
  refine ⟨max n₁ 1, max C₂ C₃, fun D n₀ C hn hC h2 h7 hdec hloc hb htri hS => ?_⟩
  exact h D n₀ C (le_trans (le_max_left _ _) hn) (le_trans (le_max_left _ _) hC) h2 h7 hdec hb
    (h3 D n₀ A C cb cε Cv Cd Cq (le_trans (le_max_right _ _) hn) (le_trans (le_max_right _ _) hC) h2 hdec hloc htri hS)

def Rest (χ : ∀ n : ℕ, (Fin n → ℝ) → ℕ → ℂ) (n₀ : ℕ) (A C cb cε Cv Cd Cq : ℝ) : Prop :=
  (FPsiEig χ ∧ FConvEig χ ∧ QOrth ∧ QInfChar ∧ QClass χ) ∧ cu_StepsEnd n₀ A 46 ∧ DistTri ∧
    VolumeCountGeometryConditions n₀ A C cb cε Cv Cd Cq

def RestU : Prop :=
  ∃ (χ : ∀ n : ℕ, (Fin n → ℝ) → ℕ → ℂ) (cε Cv Cd Cq : ℝ), 0 < cε ∧ cε ≤ 1 / 90000 ∧ 1 ≤ Cv ∧ 1 ≤ Cd ∧ 0 ≤ Cq ∧
    16 * Cq ≤ Cd ∧ ∀ cb A : ℝ, 0 < cb → 1 ≤ A → ∃ (n₂ : ℕ) (C₄ : ℝ), ∀ (n₀ : ℕ) (C : ℝ), n₂ ≤ n₀ → C₄ ≤ C →
      Rest χ n₀ A C cb cε Cv Cd Cq

end Formalism.MainNotions.LeviCoordinates
