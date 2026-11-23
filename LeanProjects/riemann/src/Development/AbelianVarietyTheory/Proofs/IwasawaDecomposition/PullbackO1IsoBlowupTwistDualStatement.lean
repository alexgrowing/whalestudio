import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackO1IsoBlowupTwistDual
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProjMapProportionalSections
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionsGenerateIdealAlongComapOfTwisted
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_O1_iso_blowup_twist_dual : ∀ (R : Type) [CommRing R] (X W : Scheme.{0}) (J : X.IdealSheafData) (L₀ : LB X) (m : ℕ)
    (σ : Fin (m + 1) → L₀.Sec) (g : W ⟶ X) (ψ : W ⟶ PSpace R m) (D : GlobalTheory.EffCartierData W), L₀.IsLB →
    GlobalTheory.ProjBlowup.Generates J σ → GlobalTheory.ProjBlowup.Proportional σ g ψ → D.idealSheaf = J.comap g →
    LBIso ((GlobalTheory.ProjSpace.O1 R m).pull ψ) (GlobalTheory.CechPic.tens (L₀.pull g) (GlobalTheory.CechPic.dual D.lb)) := by
  first | exact @GlobalTheory.ProjBlowup.lbIso_pull_O1_of_proportional | exact GlobalTheory.ProjBlowup.lbIso_pull_O1_of_proportional | (intros; apply GlobalTheory.ProjBlowup.lbIso_pull_O1_of_proportional <;> assumption)
