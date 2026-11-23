import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.MkEqZeroOfTriv
import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.EpsRedSurjective
import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.MemSupOfPullP
import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.Pull2ChernClassEqZero
import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.PerfectRing
import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.ResSurjD
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.CrystallineDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamStructureToFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidOfFreeOfCrystallineDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace CrystallinePoints.Pd

theorem resSurj.{u} : ResSurj.{u} := resSurj_coreD.{u}

theorem duality_of_surjAll (hF : AbelianDeRham.Free) (hH : AbelianDeRham.Hodge) (hB : AbelianDeRham.BaseChange)
    (hS : SurjAll) : AbelianDeRham.Duality := by
  intro R _ A _ g hA hg L hL ψ hψ
  haveI := hA.comm
  have iso : ∀ x ∈ Fil A, ∀ y ∈ Fil A, ψ x y = 0 :=
    orth_of_surj hF hB hA hg (fun C _ _ A' _ φ h ↦ hS C A' g (GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h)
      ((smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg))
      (LB.isLB_linComb hL _ _) (isCorrForm_lam hψ)
  exact ⟨iso, perfect_ring hF hH hB hA hg hL hψ iso⟩

theorem surjAll_of_dual (hC : CubeTheorem) (hF : AbelianDeRham.Free) (hH : AbelianDeRham.Hodge)
    (hB : AbelianDeRham.BaseChange) (hD : DualAbelianScheme) : SurjAll := by
  intro R _ A _ g hA hg
  obtain ⟨E, hE⟩ := exists_isE
  obtain ⟨B, _, P, hA', hd, h₁, h₂⟩ := hD (Sp R) A hA
  exact surj_of_isDual' hE h₁ (fun hM a b ↦ additive_eps hC hA hA' h₁ hM a b) resSurj hF hH hB hA hg hA' (hd g hg)
    h₂.additive

theorem abelianDeRham (hC : CubeTheorem) (hS : AbelianDeRhamStructure) (hD : DualAbelianScheme) : AbelianDeRham :=
  have hF := GlobalTheory.abelianDeRhamStructure_toFree hS
  ⟨hF, hS.2.1, hS.2.2, AbelianDeRham.rigid_of_free_of_crystallineDeRham hF FubiniStudyChowHeightFormula₂.Adr.crystallineDeRham,
    duality_of_surjAll hF hS.2.1 hS.2.2 (surjAll_of_dual hC hF hS.2.1 hS.2.2 hD)⟩

end CrystallinePoints.Pd
