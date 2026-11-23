import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertieStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousMovPair
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TowerRestrictChar

theorem continuous_char : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT χS' χT' : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)), IsWeilDatumO ψ V W χS χT ω → IsWeilDatumO ψ V' W χS' χT' ω' → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ c : GA D W →* Circle, (∀ h f, IsThetaFunO ψ V W f → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (1, h) f) = (c h : ℂ) • ω' (1, h) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f)) → Continuous c := by
  intro D V V' W r C B hs ψ χS χT χS' χT' ω ω' hω hω' μ 𝓨 hμ c hc
  obtain ⟨_, _, _, hg4, _⟩ := Formalism.IndefR.Eqv.ga_facts D W
  have hres := GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W r C B hs ψ hω.std μ 𝓨 hμ
  obtain ⟨f₀, hf₀, hne⟩ := hres.2
  haveI : IsFiniteMeasure (μ.restrict 𝓨) :=
    ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  set g := GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f₀ with hgdef
  have hg : IsThetaFunO ψ V' W g := (hres.1 f₀ hf₀).2.1
  have hcont1 : Continuous fun h : GA D W => (((1 : GA D V), h) : GA D V × GA D W) :=
    continuous_const.prodMk continuous_id
  have hcont1' : Continuous fun h : GA D W => (((1 : GA D V'), h) : GA D V' × GA D W) :=
    continuous_const.prodMk continuous_id
  suffices hC : Continuous fun h => (c h : ℂ) from continuous_induced_rng.2 hC
  rw [continuous_iff_continuousAt]
  intro h₀

  have hne₀ : ω' (1, h₀) g ≠ 0 := by
    intro h0
    apply hne
    have hinv : ω' (1, h₀⁻¹) * ω' (1, h₀) = 1 := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one, inv_mul_cancel, Prod.mk_one_one, map_one]
    have := congrArg (fun T : Module.End ℂ (WO V' W → ℂ) => T g) hinv
    simp only [Module.End.mul_apply, h0, map_zero, Module.End.one_apply] at this
    exact this.symm
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hne₀

  set Dn : GA D W → ℂ := fun h => ω' (1, h) g x with hDn
  have hDc : Continuous Dn := (hω'.om_cont g hg x).comp hcont1'
  have hD0 : Dn h₀ ≠ 0 := hx

  set Nu : GA D W → ℂ := fun h => GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (1, h) f₀) x with hNu
  have hNc : ContinuousAt Nu h₀ := by
    haveI : SecondCountableTopology (GA D W) := hg4
    obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds h₀
    obtain ⟨c₀, hc₀⟩ := GlobalTheory.WeilSupBound.exists_sup_bound D ψ V W χS χT ω hω f₀ hf₀
      ({(1 : GA D V)} ×ˢ K) (isCompact_singleton.prod hK)
    refine MeasureTheory.continuousAt_of_dominated (bound := fun _ => c₀) ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun h =>
        ((hres.1 _ (hω.om_pres _ _ hf₀)).1 x).aestronglyMeasurable
    · filter_upwards [hKn] with h hh
      exact Filter.Eventually.of_forall fun y =>
        hc₀ ((1 : GA D V), h) ⟨rfl, hh⟩ _
    · exact integrable_const c₀
    · exact Filter.Eventually.of_forall fun y =>
        ((hω.om_cont f₀ hf₀ _).comp hcont1).continuousAt

  have hq : ∀ h, Nu h = (c h : ℂ) * Dn h := fun h => by
    have := congrFun (hc h f₀ hf₀) x
    simpa [hNu, hDn, hgdef] using this
  have hev : ∀ᶠ h in nhds h₀, Dn h ≠ 0 := hDc.continuousAt.eventually_ne hD0
  have hdiv : ContinuousAt (fun h => Nu h / Dn h) h₀ := hNc.div hDc.continuousAt hD0
  refine hdiv.congr ?_
  filter_upwards [hev] with h hh
  rw [hq h, mul_div_assoc, div_self hh, mul_one]

end GlobalTheory.TowerRestrictChar
