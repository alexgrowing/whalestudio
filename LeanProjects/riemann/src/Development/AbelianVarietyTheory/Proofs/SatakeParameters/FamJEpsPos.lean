import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HodgeTateJumpsAtModulesForSign
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfWindows
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertLongOrbitWordConditionsOfLargeScaleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeWordConditionsOfLargeScaleStatement

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.RecS

theorem famJ_CLw_eq {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) :
    (Fm.params x hx i).CLw = Fm.PK.getD 7 0 := by
  rw [← Fm.params_K x hx i]
  rfl

theorem famJ_eps_pos {eps : ℝ} (Fm : FamP eps) : 0 < eps := by
  obtain ⟨i⟩ := Fm.Ix_zero
  rw [← Fm.L_eps 0 i]
  exact (Fm.L 0 i).sc.eps_pos

theorem famJ_ez_pos {eps : ℝ} (Fm : FamP eps) : 0 < Fm.ez := by
  obtain ⟨i⟩ := Fm.Ix_zero
  rw [← Fm.L_ez 0 i]
  exact (Fm.L 0 i).sc.ez_pos

theorem fam_joints : ∀ {eps : ℝ} (Fm : FamP eps) (C₂ : ℝ), (∀ D : D7, LocalSituation.adm7 D) →
    (∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) →
    ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (i : Fm.Ix x) (HW : HWOf (Fm.D x i).loc),
      LJ.ConclusionJa (Fm.D x i) → RecS.JointB (Fm.L x i) HW C₂ ∧ RecS.JointCD (Fm.L x i) HW := by
  intro eps Fm C₂ h7 hF
  obtain ⟨xB, hB⟩ := GlobalTheory.T.inertLongOrbitWordConditions_of_large_scale eps Fm.ez C₂ (Fm.PK.getD 7 0) (famJ_eps_pos Fm) (famJ_ez_pos Fm)
  obtain ⟨xC, hC⟩ := GlobalTheory.T.inertPrimeWordConditions_of_large_scale eps Fm.ez (Fm.PK.getD 7 0) (famJ_eps_pos Fm) (famJ_ez_pos Fm)
  refine ⟨max xB xC, fun x hx h1 i HW hJ => ⟨?_, ?_⟩⟩
  · refine hB _ _ (Fm.params x h1 i) HW (Fm.L_eps x i) (Fm.L_ez x i) (famJ_CLw_eq Fm x h1 i).le ?_ (h7 _) (hF _) hJ
    rw [Fm.L_x x i h1]
    exact (le_max_left _ _).trans hx
  · refine hC _ _ (Fm.params x h1 i) HW (Fm.L_eps x i) (Fm.L_ez x i) (famJ_CLw_eq Fm x h1 i).le ?_ (h7 _) (hF _) hJ
    rw [Fm.L_x x i h1]
    exact (le_max_right _ _).trans hx

end GlobalTheory.HTW.RecS
