import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesOverSplitPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowOfRestrictsToQuadratiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridAlphaBetaRestrictQuadraticPowRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaUnramifiedOutsideStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaUnramifiedOutsideStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharacterQuotientNotUnramifiedOverBasePStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaDivBetaRamifiedFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaDivBetaRamifiedAtLevelStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FunObj

theorem squareChars_isGood : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), SquareStanding G t → ∃ S₀ Q : Finset (HeightOneSpectrum (𝓞 D.host.F)),
      (∀ v ∈ S₀ ∪ Q, (∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v) ∧
        Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v)) ∧
      ∀ B : Base D.host.F D.host.E, S₀ ∪ Q ⊆ B.P → B.v₁ ∉ S₀ ∪ Q → SplitsFully D.host.E B.v₁ →
        HasExp B.emb (alpha G t i j) B.mα → HasExp B.emb (beta G i j) B.mβ →
        Chars.IsGood B ⟨alpha G t i j, beta G i j, S₀, Q⟩ (spW G i j).rank (spW₁ G i j).rank := by
  intro D T L sc G μ₀ hL t i j _hst
  refine ⟨G.pl.S0, (L.Q t).image (fun P => P.under (𝓞 D.host.F)) \ G.pl.S0, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_union.1 hv with hv | hv
    · have hw : G.pl.w v ∈ locPl G t := Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)
      have e := G.pl.under_w hv
      exact ⟨⟨_, hw, e⟩, e ▸ GlobalTheory.T.gridLocalTensorPlaces_over_split_places hL t _ hw⟩
    · obtain ⟨P, hP, e⟩ := Finset.mem_image.1 (Finset.mem_sdiff.1 hv).1
      have hw : P ∈ locPl G t := Finset.mem_union_right _ hP
      exact ⟨⟨P, hw, e⟩, e ▸ GlobalTheory.T.gridLocalTensorPlaces_over_split_places hL t _ hw⟩
  · intro B hsub hv₁ hsp hα hβ
    have h2 : Module.finrank D.host.F D.host.E = 2 := D.sp.cm.deg2
    obtain ⟨rα, rβ⟩ := GlobalTheory.T.thetaGrid_alpha_beta_restrict_quadratic_pow_rank hL t i j
    refine ⟨?_, ?_, GlobalTheory.T.restrictsToQuadraticSignPow_of_restrictsToQuadraticCharPow _ _ h2 _ _ rα, GlobalTheory.T.restrictsToQuadraticSignPow_of_restrictsToQuadraticCharPow _ _ h2 _ _ rβ, hα, hβ, ?_, hsub, ?_, ?_, ?_, ⟨hv₁, hsp⟩⟩
    · have hm := (hL.mu0 j).1
      have hx := (hL.xi t).1
      have he := hL.eta.1
      refine ⟨(hm.1.mul hx.1).mul (he.1.pow _), fun x => ?_⟩
      have e1 := hm.2 x
      have e2 := hx.2 x
      have e3 := he.2 x
      show L.mu0 ((j : ℕ) + 1) _ * L.xi t _ * (L.eta ^ _) _ = 1
      rw [MonoidHom.pow_apply]
      rw [e1, e2, e3]
      simp
    · have hc := (G.ch.chi_eq (D.R.m - (i : ℕ)) (by omega) (by omega)).1
      have he := hL.eta.1
      refine ⟨hc.1.mul (he.1.pow _), fun x => ?_⟩
      have e1 := hc.2 x
      have e3 := he.2 x
      show G.ch.chi (D.R.m - (i : ℕ)) _ * (L.eta ^ _) _ = 1
      rw [MonoidHom.pow_apply, e1, e3]
      simp
    · exact Finset.disjoint_sdiff
    · intro w hw
      rcases Finset.mem_union.1 hw with hw | hw
      · rcases (G.pl.mem_S0_of_sum_eq).1 hw with h | h
        · exact GlobalTheory.T.not_unrAt_of_under_eq_v0 hL t i j w h
        · exact GlobalTheory.T.alpha_div_beta_ramified_first hL t i j w h
      · obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hw
        obtain ⟨P, hP, e⟩ := Finset.mem_image.1 h1
        exact GlobalTheory.T.alpha_div_beta_ramified_at_level hL t i j w P hP e h2
    · intro w hw
      have hw' : w.under (𝓞 D.host.F) ∉ G.pl.S0 ∪ ((L.Q t).image (fun P => P.under (𝓞 D.host.F)) \ G.pl.S0) := hw
      refine GlobalTheory.T.alpha_unramified_outside hL t i j w (fun h => hw' (Finset.mem_union_left _ h)) fun P hP e => hw' ?_
      by_cases h : w.under (𝓞 D.host.F) ∈ G.pl.S0
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨Finset.mem_image.2 ⟨P, hP, e⟩, h⟩)
    · intro w hw
      have hw' : w.under (𝓞 D.host.F) ∉ G.pl.S0 ∪ ((L.Q t).image (fun P => P.under (𝓞 D.host.F)) \ G.pl.S0) := hw
      exact GlobalTheory.T.beta_unramified_outside hL i j w (fun h => hw' (Finset.mem_union_left _ h))

end GlobalTheory.FunObj

end
