import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureModuliFibreOfMonomialPeriodPreChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundlePowerIsoMinimalSiegelCompactificationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGloballyGeneratedAmplePowerToroidalPullbacStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeCycAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPolarisedChartOfMonomialPreChartSemiAbelianExStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

theorem GlobalTheory.SiegJoin.siegelToroidalPolCharts_of_steps5
    (hF : ∀ g n : ℕ, 1 ≤ g → 3 ≤ n → Odd n → Nonempty (SFam g n (zetaAway n))) (hMin : GlobalTheory.SiegJoin.MinSt5)
    (hPoin : GlobalTheory.Poinc.PoinSt) (hChart : GlobalTheory.SiegJoin.ChartSt5) (hDesc : GlobalTheory.SiegJoin.DescSt5) :
    GlobalTheory.Published.SiegelToroidalPolCharts := by
  intro g hg φ hφ hφ' n hn ho
  have hn0 : n ≠ 0 := by omega
  haveI : IsNoetherianRing (cycAway n) := by haveI := (GlobalTheory.SiegelTor.arBase_cycAway n hn0).1; infer_instance
  obtain ⟨F⟩ := hF g n hg hn ho
  obtain ⟨Z, z, i, OZ, hMA⟩ := hMin g hg n hn ho F
  have hMA' := hMA
  obtain ⟨o', _, β, S', s', U, c, π', G', _, e', _, N', ⟨hTh, hZp, hZn, hiz, hid, hOZ, hOZa⟩, -⟩ := hMA'
  obtain ⟨d, J, S, π, j, BD, hd, hJ, hV, hBl, hP, hj, hjd, hji, hjpre, hBD, hVj, k₀, hk₀⟩ :=
    hPoin g hg n hn ho F Z z i hTh OZ hOZ hOZa φ hφ
  haveI := hj
  have hBlow : BlowAt F z i φ d π j BD := ⟨J, hd, hJ, hV, hBl, hP, hjd, hji, hjpre, hBD, hVj⟩
  obtain ⟨hsm, hpre⟩ := hChart g hg φ hφ hφ' n hn ho F Z z i OZ d S π j BD hMA hBlow
  obtain ⟨G, _, e, hGs, hGd, hGe, hGab⟩ :=
    hDesc g hg φ n hn ho F Z z i d S π j BD hBlow hpre
  haveI := hsm
  haveI : Smooth (π ≫ z) := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) _
  haveI : QuasiSeparated G.hom := by haveI := hGs.separated; infer_instance
  obtain ⟨a, N, ha, hN, hiso⟩ := GlobalTheory.T.hodgeBundle_power_iso_minimalSiegelCompactification g n F Z z i OZ S π j G e hMA
    (fun x => ⟨hBl.1.isDomain_stalk x, hBl.1.isIntegrallyClosed_stalk x⟩) hP hjd hji hGs hGd hGe
  obtain ⟨N'', hN'', hgen, k, hk⟩ := GlobalTheory.T.exists_globallyGenerated_ample_power_toroidalPullback (cycAway n) Z S z π OZ (hodge G g) (GlobalTheory.CechPic.dual BD.lb) a N
    hZp hOZ hOZa (isLB_hodge G g) (GlobalTheory.CechPic.isLB_dual BD.isLB_lb) ha hN hiso ⟨k₀, hk₀⟩
  refine ⟨F, S, π ≫ z, j, hj, G, inferInstance, e, BD, d, N'', hP, hsm, by rw [← Category.assoc, hji, hiz], ?_,
    hGs, hGd, hGe, hGab, hd, ?_, hN'', hgen, k, hk⟩
  · intro x
    exact GlobalTheory.T.mem_closure_moduliFibre_of_monomialPeriodPreChart F (π ≫ z) j φ BD d x (hpre x)
  · intro x
    exact GlobalTheory.T.hasPolarisedChart_of_monomialPreChart_semiAbelianExt F (π ≫ z) j G e φ BD d x hn0 hGs hGd hGe hGab (hpre x)

end
