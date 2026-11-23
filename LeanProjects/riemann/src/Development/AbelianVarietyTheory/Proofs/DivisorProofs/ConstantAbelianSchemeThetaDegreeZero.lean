import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPullbackComposite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHodgeCh2Omega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlteration
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SecondChernDegreeVanishesTrueSurfaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackConstantBundleDegreeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTwoDegreeZeroHodgePullbackStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField

namespace GlobalTheory.PPAS

theorem exists_pull_ringOfIntegers_ch2Omega_zero : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.RegularAlteration → ∀ (K : Type) [Field K] [NumberField K] (E : PPAS (Sp (𝓞 K))), E.HasTheta → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) [IsIntegral Y], IsRegSurf p → ∀ q : Y ⟶ Sp (𝓞 K), ∃ Q : PPAS Y, Q.g = E.g ∧ Q.HasTheta ∧ Q.degOmega p = 0 ∧ Q.IsCh2Omega p 0 := by
  intro HP HR K _ _ E hE k _ Y p _ hY q
  obtain ⟨Q, φ, hg, hP⟩ := exists_pull _ _ E q
  have hT : Q.HasTheta := by
    obtain ⟨L, hL, hs, hcL⟩ := hE
    obtain ⟨h, hc⟩ := hP
    exact ⟨L.pull φ, pull_isLB hL φ, PolBaseChange.sym_pull h hs, by
      rw [hc, hcL, pull_sqMap_lam h, CechPic.cls_pull hL]⟩
  refine ⟨Q, hg, hT, ?_, ?_⟩
  · rw [PPAS.degOmega, ← cxDeg_congr (ShFam.Pad.omegaPullIso hP), hg]
    exact GlobalTheory.T.pullback_constant_bundle_degree_zero K (LieVB.omega E.A) E.g E.isVB_omega k Y p hY.toIsArithVar q
  · obtain ⟨h, H, hN, hc, -⟩ := exists_isHodge_ch2Omega HP.p4 k Y p
      (fun Y' q' _ hq => GlobalTheory.RegCoverExists.nonempty_regCover HR k Y' q' hq) hY.toIsArithVar Q
    have e := GlobalTheory.T.chern_two_degree_zero_hodge_pullback HP HR K E hE k Y p hY q Q φ hP h H hN _ hc
    exact ⟨h, H, e ▸ hc⟩

end GlobalTheory.PPAS
