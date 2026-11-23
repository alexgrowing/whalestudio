import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.FoldBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareSeriesSquareIntegrable
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ProjRows
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.RowsDef
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ExplicitFormulaBoundHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RowsProj
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RowsBij
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RegUnitary
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PoincareSeriesFinite
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PoincareSeriesMemLp
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PoincareSeriesInner
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhSchurConv
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhConvProj
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhProdConv
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LatCountG
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SymDist
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ExpTri
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AdIndexEq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionD
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary

open MeasureTheory Formalism.MainNotions.S

namespace Formalism.L2.SG.Closed

section Fold

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]

theorem fold_L2_first : Formalism.L2.SG.PoincareSeriesSquareIntegrable.PoincareSeriesFinite G μ := poincareSeries_finite G μ
theorem fold_L2_second : Formalism.L2.SG.PoincareSeriesSquareIntegrable.PoincareSeriesMemLp G μ := fold_l2_bound_b G μ

end Fold

theorem SchurConv_holds : Formalism.L2.SG.ProjRows.SchurConv := schur_orthogonality_idempotent
theorem ConvProj_holds : Formalism.L2.SG.ProjRows.ConvProj := convolution_projection
theorem ProdConv_holds : Formalism.L2.SG.ProjRows.ProdConv := isConvIdempotent_pi
theorem RegUnitary_holds : Formalism.L2.SG.ProjRows.RegUnitary := Formalism.L2.SG.Pf.regular_representation_unitary
theorem ProjRowsR_holds : Formalism.L2.SG.ProjRows.ProjRowsR :=
  Formalism.L2.SG.ProjRows.projRowsR_of SchurConv_holds ConvProj_holds ProdConv_holds RegUnitary_holds

theorem GfUnimod_holds : Formalism.L2.SG.Pf.GfUnimod := fun I μf _ _ =>
  (PI.WAU.adUnimod_of PI.WAU.kg_subgroup PI.WAU.maximal_compact_isCompact PI.WAU.compact_countable
    PI.adelic_index_eq) I μf inferInstance

theorem UnimodGf_holds : Formalism.L2.SG.Pf.UnimodGf := GfUnimod_holds

theorem AutKCompact_holds : Formalism.L2.SG.Pf.AutKCompact := PI.WAU.maximal_compact_isCompact

theorem RowsBij_holds : Formalism.L2.SG.RowsDef.RowsBij :=
  Formalism.L2.SG.Pf.rows_bijective ProjRowsR_holds UnimodGf_holds

theorem level_subgroup_is_group {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : X.LevelSubgroupCharacter :=
  Formalism.L2.SG.Pf.level_subgroup_character_unitary X

theorem level_subgroup_properties {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : X.LevelSubgroupNormalized :=
  Formalism.L2.SG.Pf.levelSubgroupNormalized_of_compact X AutKCompact_holds

section Count

def latSubEquiv (I : AutInst) (x : I.GA) : PI.LatCountG.Sub I x ≃ Formalism.L2.SG.LitS.Size.Sub I x where
  toFun s := ⟨s.j, s.j_pos, s.b, s.b_ind, s.B, s.B_lat, s.b_mem, s.B_span⟩
  invFun s := ⟨s.j, s.j_pos, s.b, s.b_ind, s.B, s.B_lat, s.b_mem, s.B_span⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem lattice_tau_eq_size_tau (I : AutInst) : PI.LatCountG.tau1 I = Formalism.L2.SG.LitS.Size.tau1 I := by
  funext x
  unfold PI.LatCountG.tau1 Formalism.L2.SG.LitS.Size.tau1
  congr 1
  exact Equiv.iInf_congr (latSubEquiv I x) (fun _ => rfl)

theorem LatCount_holds (I : AutInst) : Formalism.L2.SG.Count.LatCount I := by
  have h := lattice_count_all I
  unfold PI.LatCountG.LatCount at h
  unfold Formalism.L2.SG.Count.LatCount
  rw [lattice_tau_eq_size_tau] at h
  exact h

theorem DistTri_holds : Formalism.MainNotions.LeviCoordinates.DistTri := symDist_of exp_triangle_inequality

end Count

end Formalism.L2.SG.Closed
