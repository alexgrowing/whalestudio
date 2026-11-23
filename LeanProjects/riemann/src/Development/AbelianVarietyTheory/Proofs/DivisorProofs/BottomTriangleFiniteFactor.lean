import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AutomorphicArithmetic.LocalEmbeddings.BotMain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomDictionaryFramesExponentsKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingSplitPrimeGridLocalTensorPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesSplitIdempotentSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterUnramifiedMuStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridCharactersUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharacterQuotientNotUnramifiedOverBaseP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaDivBetaRamifiedFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaDivBetaRamifiedAtLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterUnramifiedOffBad
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosedSubgroupOfLocalStabilizerPairs
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.bottom_triangle_finite_factor : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T), IsFinF W.ψ W.θ true FA FW (X.f t) → IsFinF W.ψ W.θ false FA' FW (X.f' t) → ∃ (Pi : ModuleCat.{0} ℂ) (rf : GA D WW → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi) (p : (WO A WW → ℂ) →ₗ[ℂ] Pi) (p' : (WO A' WW → ℂ) →ₗ[ℂ] Pi), IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' ∧ ((∀ P, p (fockF W.ψ W.θ true FA FW (X.f t) P) = 0) ∨ ∃ (P : PolF D WW.rank A.rank) (P' : PolF D WW.rank A'.rank) (κ : ℂ), p (fockF W.ψ W.θ true FA FW (X.f t) P) ≠ 0 ∧ p (fockF W.ψ W.θ true FA FW (X.f t) P) = κ • p' (fockF W.ψ W.θ false FA' FW (X.f' t) P')) := by
  intro hH hPr _ hLM
  refine GlobalTheory.BotDict.gBig_three GlobalTheory.BotDict.bottom_dictionary GlobalTheory.BotDict.bottom_dictionary GlobalTheory.BotDict.bottom_dictionary ?_
  intro D T Lc sc G μ₀ C x b hL hd _ _ W i j A A' WW X hX FA FA' FW t hf hf'
  classical
  obtain ⟨_, _, _, _, _, -, -, -, hd⟩ := hd W i j A A' WW X hX
  have e : Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) =
      G.nu t i (j + 1) := mul_div_mul_right_eq_div _ _ _
  have e' : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j = G.nu t i (j + 1) := mul_div_mul_right_eq_div _ _ _
  refine GlobalTheory.BotMatch.match_of_tri hH hPr hLM W.ψ_std W.θ_is X hX.is t (hd t).1 (e ▸ chrEq_nu G t i j hL)
    (GlobalTheory.T.exists_embedding_splitPrime_gridLocalTensorPlaces hL t) (fun w hw hu => ?_) (fun w hw => ?_) (GlobalTheory.T.gridLocalTensorPlaces_splitIdempotent_sum hL t).1
    ((GlobalTheory.T.gridLocalTensorPlaces_splitIdempotent_sum hL t).2 _ (hX.is.idem t)).1 FA FA' FW hf hf'
  · have hu' : GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E)
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) w := by
      rw [e', ← e]; exact hu
    by_cases hs : w.under (𝓞 D.host.F) ∈ G.pl.S0
    · rcases G.pl.mem_S0_of_sum_eq.1 hs with h | h
      · exact GlobalTheory.ThetaGridRamifiedOverBasePlace.thetaGridCharacterQuotient_not_unramified_over_basePlace hL t i j w h hu'
      · exact GlobalTheory.FunObj.SqNum.not_unrAt_alpha_div_beta_over_S₁ hL t i j w h hu'
    · rcases Finset.mem_union.1 hw with h | h
      · unfold Places.W0 at h
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
        exact hs (by rw [G.pl.under_w hv]; exact hv)
      · exact GlobalTheory.TwistRam.not_unrAt_alpha_div_beta hL t i j w w h rfl hs hu'
  · obtain ⟨ε, hε⟩ := GlobalTheory.StabDense.exists_placeIdem (D := D) (w.under (𝓞 D.host.F))
    have hs : w.under (𝓞 D.host.F) ∉ G.pl.S0 := fun hs =>
      hw (G.pl.w _) (Finset.mem_union_left _ (by unfold Places.W0; exact Finset.mem_image_of_mem _ hs)) (G.pl.under_w hs)
    have h1 := GlobalTheory.BasePairChar.unrAt_of_unramAt hε (GlobalTheory.T.level_character_unramified_mu G μ₀ hL t _ ε hε hs (fun P hP => hw P (Finset.mem_union_right _ hP)) j) rfl
    have h2 := GlobalTheory.BasePairChar.unrAt_of_unramAt hε (GlobalTheory.T.grid_characters_unramified G μ₀ hL t _ ε hε hs i).1 rfl
    have h3 := GlobalTheory.BasePairChar.unrAt_of_unramAt hε (GlobalTheory.T.grid_characters_unramified G μ₀ hL t _ ε hε hs i).2 rfl
    have h4 : ∀ n : ℕ, GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (Lc.eta ^ n) w := fun n => by
      induction n with
      | zero => rw [pow_zero]; exact fun _ _ => map_one Circle.toUnits
      | succ n ih => rw [pow_succ]; exact ih.mul h3
    exact ⟨h1.mul (h4 _), h2.mul (h4 _)⟩
