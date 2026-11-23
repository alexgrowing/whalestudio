import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsAbLift
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionPrimitiveBundleTranslateLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.HtPt.Ppic
open GlobalTheory.CechPic

theorem pic : ∀ (Q : Out.PolAV (Sp ℂ)) (M : LB Q.A.left), M.IsLB → (∃ u : LB.Gen (abelian₂ Q.A (LB.div M Q.L)), u.IsGen) → ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A, LBIso M (Q.L.pull ((toUnit Q.A ≫ x) * 𝟙 Q.A).left) := by
  intro Q M hM hu
  have hO : (LB.div M Q.L).IsLB := LB.isLB_div hM Q.isLB
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_section_primitiveBundle_translate_localRing GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 ℂ Q _ hO hu
  refine ⟨x, ?_⟩
  have e := (cls_eq_iff hO (LB.isLB_linComb Q.isLB _ _)).2 hx
  rw [cls_div hM Q.isLB, cls_linComb Q.isLB, Fin.sum_univ_two] at e
  refine (cls_eq_iff hM (pull_isLB Q.isLB _)).1 ?_
  rw [cls_pull Q.isLB]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, pull_id] at e
  rw [← sub_eq_add_neg] at e
  exact sub_left_injective e

end PositivityTheory.HtPt.Ppic
