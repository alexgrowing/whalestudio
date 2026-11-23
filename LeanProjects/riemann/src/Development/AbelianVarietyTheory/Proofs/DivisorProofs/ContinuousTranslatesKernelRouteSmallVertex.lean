import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteCombinationMulLiftByDegree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SmallRoute

theorem continuous_translates_kerSmall : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j))
    (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))) (z : GA D (G.V (.grid i j)) →₀ ℂ),
    Continuous (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) =>
      translates z (kerSmall W Θ' p.1 g₁) p.2) := by
  intro D T L sc G μ₀ hL W B ρ t i j Θ Θ' hΘ g₁ z
  obtain ⟨_, _, _, _, hTG, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.grid i j))
  have hc := W.om_is (.chi (i : ℕ) j) ⟨i.2, j.2.le⟩
  have hm := W.om_is (.mu t (i : ℕ) j) ⟨i.2.le, j.2⟩
  have hK : ∀ d ∈ Θ'.support, Continuous (fun q : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) =>
      W.kerA (.down t i j) d.1.2 q.1 q.2 * W.kerA (.right i j) d.2 q.2 g₁) := by
    intro d hd
    obtain ⟨h2, h1⟩ := theta_of_matched hΘ hd
    refine Continuous.mul ?_ ?_
    · show Continuous fun q : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) =>
        thetaKO (W.om (.mu t (i : ℕ) j)) q.2 q.1 d.1.2
      exact (hm.om_cont _ h1 0).comp (continuous_snd.prodMk continuous_fst)
    · show Continuous fun q : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) =>
        thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) q.2 d.2
      exact (hc.om_cont _ h2 0).comp (continuous_const.prodMk continuous_snd)
  unfold translates kerSmall
  simp only [Finsupp.sum]
  refine continuous_finset_sum _ fun k _ => continuous_const.mul ?_
  refine continuous_finset_sum _ fun d hd => continuous_const.mul ?_
  exact (hK d hd).comp (continuous_fst.prodMk (continuous_snd.mul continuous_const))

end GlobalTheory.SmallRoute
