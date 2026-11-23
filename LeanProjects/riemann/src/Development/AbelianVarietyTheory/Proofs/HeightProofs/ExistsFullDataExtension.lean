import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ShortGenIndepConnection
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCoeffDeltaOKOfCover
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSpecialPrimeLevelCoverOfFieldConditionsStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LawsShortOfDeltaOK
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPsiTieOfValues
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSecCharVal
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin2.FullExt

theorem exists_delta_xiAt_noVol (D : D7) (J : CoreJ D) (hJ : LawsJ J) (hP : J.Q.Pins) (hC : J.Q.Canon) (p : ℕ) (hF : FieldOK0 D p)
    (P : HeightOneSpectrum (𝓞 D.host.K)) (hp : ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal) (xi : (AfE D)ˣ →* ℂˣ)
    (hxi : XiOK D p xi) (j : ℕ) (hj : InR D j) :
    ∃ e : ∀ n, DeltaDat (J.Q.Xo j) J.Q.c n, ∀ n, (∃ φ, e n = GlobalTheory.FormTies.withCoeff (e 0) φ) ∧
      DeltaOK (e n) p (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧ XiAt J j (e n) xi := by
  obtain ⟨hpr, -, hd⟩ := GlobalTheory.T.exists_specialPrime_levelCover_of_fieldConditions D J.Q hP hC p hF P hp
  obtain ⟨d, hc, ha⟩ := hd j hj
  obtain ⟨f, hc', hr', hx⟩ := GlobalTheory.XiFun.exists_fun_xiAt D J hJ j hj p _ d xi hc ha hxi
  have ht := GlobalTheory.TwistTie.exists_psiTie_of_xiAt D J hJ j hj p _ { d with cδ := f } xi hpr hc' ha hxi hx
  obtain ⟨φ, hφ⟩ := GlobalTheory.exists_coeff_deltaOK_of_cover _ _ _ _ _ _ _ p _ hc' hr' ht
  exact ⟨fun n => GlobalTheory.FormTies.withCoeff { d with cδ := f } (φ n), fun n => ⟨⟨φ n, rfl⟩, hφ n, hx⟩⟩

theorem exists_full_of_xiOK_noVol : ∀ (D : D7) (J : CoreJ D) (T : Top D), LawsJ J → LawsP T → T.toCore = J.toCore → T.Q.Canon → ∀ p : ℕ, FieldOK0 D p → ∀ (P : HeightOneSpectrum (𝓞 D.host.K)), ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal → ∀ xi, XiOK D p xi → ∃ (dd : ∀ j n, DeltaDat (T.Q.Xo j) T.Q.c n) (TF : Full D), LawsFull TF ∧ TF.toTop = { T with dδ := dd } ∧ TF.J = J ∧ TF.xi = xi ∧ TF.half₂ = (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧ ∀ j, InR D j → GlobalTheory.FormTies.OneCover TF.toTop j ∧ ∀ n, (TF.dδ j n).pd = p := by
  intro D J T hJ hT hc hC p hF P hp xi hxi
  obtain ⟨C, G, nab, d₀⟩ := T
  obtain ⟨C', cE, chiW, x₀, iota⟩ := J
  dsimp only at hc
  subst hc
  have key : ∀ j, ∃ e : ∀ n, DeltaDat (C.Q.Xo j) C.Q.c n, InR D j → ∀ n, (∃ φ, e n = GlobalTheory.FormTies.withCoeff (e 0) φ) ∧
      DeltaOK (e n) p (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧
        XiAt (⟨C, cE, chiW, x₀, iota⟩ : CoreJ D) j (e n) xi := by
    intro j
    by_cases hj : InR D j
    · obtain ⟨e, he⟩ := exists_delta_xiAt_noVol D ⟨C, cE, chiW, x₀, iota⟩ hJ hT.pins hC p hF P hp xi hxi j hj
      exact ⟨e, fun _ => he⟩
    · exact ⟨d₀ j, fun h => absurd h hj⟩
  choose dd hdd using key
  obtain ⟨hLP, hLS⟩ := GlobalTheory.FinalJoin.laws_short_of_deltaOK D ⟨C, cE, chiW, x₀, iota⟩ ⟨C, G, nab, d₀⟩ hJ hT rfl hF.bad p _ hF.own dd
    (fun j hj n => (hdd j hj n).2.1)
  refine ⟨dd, ⟨⟨C, G, nab, dd⟩, cE, chiW, x₀, iota, xi, P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))⟩,
    ⟨hLP, hJ, hLS, hC, fun j hj n => (hdd j hj n).2.1.1.2.2.2.1, fun j hj n => (hdd j hj n).2.1.1.2.1,
      fun j hj n s nab' hn a _ => ?_, fun j hj n => (hdd j hj n).2.2⟩, rfl, rfl, rfl, rfl,
    fun j hj => ⟨fun n => (hdd j hj n).1, fun n => (hdd j hj n).2.1.1.1⟩⟩
  exact GlobalTheory.shortGen_indep_connection GlobalTheory.chartIndependence_unconditional _ _ _ _ _ _ n (dd j n) (nab j) _ _
    (hdd j hj n).2.1.1.2.2.2.2 s nab' hn a

end GlobalTheory.FinalJoin2.FullExt
