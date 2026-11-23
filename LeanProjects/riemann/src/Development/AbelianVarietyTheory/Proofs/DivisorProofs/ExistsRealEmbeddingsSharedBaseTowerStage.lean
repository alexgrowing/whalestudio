import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DownRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTauEOverRealPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharactersArchExponentsGapGtRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStandingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitCompletelyAuxiliaryPlaceOutsideFinsetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowOfRestrictsToQuadratiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridAlphaBetaRestrictQuadraticPowRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaUnramifiedOutsideStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaUnramifiedOutsideStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharacterQuotientNotUnramifiedOverBasePStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaDivBetaRamifiedFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaDivBetaRamifiedAtLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingSplitPrimeGridLocalTensorPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigThetaKernelIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsMulOfCondExp

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStepBig

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base HasExp SplitsFully Chars)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spW spW₁ alpha beta)

private theorem standing_of_rec {D : D7} {large₂ : SizeData₂ D} (hR : Rec large₂) {T : Type} {Lc : LevCh D T} {μ₀ : T} (hL : Lc.Is μ₀)
    {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (t : T) : SquareStanding G t := by
  classical
  have hx : 11 ≤ D.host.splitBound := hR.size.2.1.eleven_le
  have hcc : D.host.ccK = ⊤ := hR.size.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨⟨P, -, -⟩, -⟩ := hR.size
  have lev : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := fun p hp hpp =>
    UpperTheory.Ram.Fun.coprime_condN_of_splitK D.host hpp (P.level_split p hp)
  refine ⟨hx, fun w hw => ?_⟩
  have e1 : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) =
      ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) := by
    rw [hcc, Ideal.absNorm_top, mul_one]
  rw [e1]
  rcases Finset.mem_union.1 hw with hw | hw
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨p, hpv, hcop⟩ : ∃ p : ℕ, ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∧ Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := by
      rcases G.pl.mem_S0_of_sum_eq.1 hv with rfl | hv1
      · refine ⟨q0 D, G.pl.basePlace_over_qZero, ?_⟩
        have hs := (leastSplitAuxiliaryPrimeThetaChain_spec D).2.1
        have hM : Nat.Coprime (Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D) (q0 D) := by
          rw [Nat.Coprime, Nat.gcd_rec, hs, Nat.gcd_one_left]
        have hdv : D.host.QS * D.host.q * D.host.d ∣ Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D := by
          unfold LevelStarExponents.condE
          exact Dvd.dvd.mul_left dvd_rfl _
        exact (hM.coprime_dvd_left hdv).symm
      · rcases (S1_mem_OmF D).1 hv1 with h | h | h | h
        · exact ⟨_, h, lev _ (D.host.g_level 0) (D.host.g_prime 0)⟩
        · exact ⟨_, h, lev _ (D.host.g_level 1) (D.host.g_prime 1)⟩
        · exact ⟨_, h, lev _ D.host.pde_level.1 D.host.pde_prime⟩
        · exact ⟨_, h, lev _ D.host.pde_level.2 D.host.pde'_prime⟩
    have hpw : ((p : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal := by
      rw [← G.pl.under_w hv, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at hpv
      exact hpv
    exact GlobalTheory.SquareConv.natCast_not_mem (G.pl.w v).isPrime.ne_top hcop hpw
  · intro hmem
    apply (hL.Q_off t w hw).1
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem

section

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} {μ₀ : T}

private theorem rank_weight_component_eq (hL : Lc.Is μ₀) (i j : Fin D.R.m) : (spW G i j).rank = rankV D (i + 1) (j + 1) :=
  (node_isV G hL (X := .grid (i + 1) (j + 1)) ⟨by omega, by omega⟩).rank

private theorem rank_W₁ (hL : Lc.Is μ₀) (i j : Fin D.R.m) : (spW₁ G i j).rank = rankV D i j :=
  (node_isV G hL (X := .grid i j) ⟨by omega, by omega⟩).rank

private theorem chs_α (hL : Lc.Is μ₀) (i j : Fin D.R.m) (t : T) : (GlobalTheory.SqStep.chs G i j t).α = alpha G t i j := by
  unfold alpha GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps
  rw [rank_W₁ hL]
  rfl

private theorem chs_β (hL : Lc.Is μ₀) (i j : Fin D.R.m) (t : T) : (GlobalTheory.SqStep.chs G i j t).β = beta G i j := by
  unfold beta GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps
  rw [rank_W₁ hL]
  rfl

private theorem exps (hL : Lc.Is μ₀) (i j : Fin D.R.m) (τf : InfinitePlace D.host.F → D.what₂.Tau)
    (hτf : ∀ w, ((starRingEnd ℂ).comp (tauE D (τf w))).comp (algebraMap D.host.F D.host.E) = w.embedding) :
    ∃ mα mβ : InfinitePlace D.host.F → ℤ,
      (∀ t, HasExp (fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩) (alpha G t i j) mα) ∧
      HasExp (fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩) (beta G i j) mβ ∧
      ∀ w, ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℤ) < mα w - mβ w := by
  choose mα hα eα using fun t => GlobalTheory.T.hasArchimedeanCharExponents_conj_of_hasInfExp _ _ (fun τ => GlobalTheory.SquareExps.alpha_exp (G := G) hL t i j j.2 τ) τf hτf
  obtain ⟨mβ, hβ, eβ⟩ := GlobalTheory.T.hasArchimedeanCharExponents_conj_of_hasInfExp _ _ (fun τ => GlobalTheory.SquareExps.beta_exp (G := G) hL i j i.2 τ) τf hτf
  refine ⟨mα μ₀, mβ, fun t => ?_, hβ, fun w => ?_⟩
  · have e : mα μ₀ = mα t := funext fun w => by
      have := (eα μ₀ w).trans (eα t w).symm
      exact_mod_cast this
    rw [e]
    exact hα t
  · have key := GlobalTheory.T.chiGridVertexRank_add_lt_two_exponent_add_centre sc.cGap (τf w) i j i.2 j.2
    have h1 := eα μ₀ w
    have h2 := eβ w
    have : (((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℤ) : ℚ) < ((mα μ₀ w - mβ w : ℤ) : ℚ) := by
      push_cast at h1 h2 key ⊢
      rw [h1, h2]
      linarith
    exact_mod_cast this

private theorem under_notMem (hL : Lc.Is μ₀) (t : T) {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : P ∈ twPl G t) :
    P ∈ Lc.Q t ∧ P.under (𝓞 D.host.F) ∉ G.pl.S0 := by
  classical
  obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hP
  refine ⟨(Finset.mem_union.1 h1).resolve_left h2, fun h => h2 ?_⟩
  have hw : G.pl.w (P.under (𝓞 D.host.F)) ∈ G.pl.W0 := Finset.mem_image_of_mem _ h
  have hw' : G.pl.w (P.under (𝓞 D.host.F)) ∈ locPl G t := Finset.mem_union_left _ hw
  have e := GlobalTheory.FunObj.Good.under_injOn hL G t hw' h1 (G.pl.under_w h)
  rw [← e]
  exact hw

private theorem chars_good (hL : Lc.Is μ₀) (t : T) (i j : Fin D.R.m) (B : Base D.host.F D.host.E)
    (hsub : (GlobalTheory.SqStep.chs G i j t).T ⊆ B.P) (hv₁ : B.v₁ ∉ (GlobalTheory.SqStep.chs G i j t).T) (hsp : SplitsFully D.host.E B.v₁)
    (hα : HasExp B.emb (alpha G t i j) B.mα) (hβ : HasExp B.emb (beta G i j) B.mβ) :
    (GlobalTheory.SqStep.chs G i j t).IsGood B (rankV D (i + 1) (j + 1)) (rankV D i j) := by
  classical
  have h2 : Module.finrank D.host.F D.host.E = 2 := D.sp.cm.deg2
  obtain ⟨rα, rβ⟩ := GlobalTheory.T.thetaGrid_alpha_beta_restrict_quadratic_pow_rank (G := G) hL t i j
  rw [rank_W₁ hL] at rα
  rw [rank_weight_component_eq hL] at rβ
  have eα := chs_α (G := G) hL i j t
  have eβ := chs_β (G := G) hL i j t
  have eν : (GlobalTheory.SqStep.chs G i j t).ν = alpha G t i j / beta G i j := by
    unfold Chars.ν
    rw [eα, eβ]
  refine ⟨?_, ?_, eα ▸ GlobalTheory.T.restrictsToQuadraticSignPow_of_restrictsToQuadraticCharPow _ _ h2 _ _ rα, eβ ▸ GlobalTheory.T.restrictsToQuadraticSignPow_of_restrictsToQuadraticCharPow _ _ h2 _ _ rβ, eα ▸ hα, eβ ▸ hβ, ?_, hsub, ?_, ?_, ?_,
    ⟨hv₁, hsp⟩⟩
  · have hm := (hL.mu0 j).1
    have hx := (hL.xi t).1
    have he := hL.eta.1
    refine ⟨(hm.1.mul hx.1).mul (he.1.pow _), fun x => ?_⟩
    have e1 := hm.2 x
    have e2 := hx.2 x
    have e3 := he.2 x
    show Lc.mu0 ((j : ℕ) + 1) _ * Lc.xi t _ * (Lc.eta ^ _) _ = 1
    rw [MonoidHom.pow_apply]
    rw [e1, e2, e3]
    simp
  · have hc := (G.ch.chi_eq (D.R.m - (i : ℕ)) (by omega) (by omega)).1
    have he := hL.eta.1
    refine ⟨hc.1.mul (he.1.pow _), fun x => ?_⟩
    have e1 := hc.2 x
    have e3 := he.2 x
    show G.ch.chi (D.R.m - (i : ℕ)) _ * (Lc.eta ^ _) _ = 1
    rw [MonoidHom.pow_apply, e1, e3]
    simp
  · refine Finset.disjoint_right.2 fun v hv hv0 => ?_
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hv
    exact (under_notMem hL t hP).2 hv0
  · intro w hw
    rw [eν]
    rcases Finset.mem_union.1 hw with hw | hw
    · rcases (G.pl.mem_S0_of_sum_eq).1 hw with h | h
      · exact GlobalTheory.T.not_unrAt_of_under_eq_v0 hL t i j w h
      · exact GlobalTheory.T.alpha_div_beta_ramified_first hL t i j w h
    · obtain ⟨P, hP, e⟩ := Finset.mem_image.1 hw
      obtain ⟨h1, h2⟩ := under_notMem hL t hP
      exact GlobalTheory.T.alpha_div_beta_ramified_at_level hL t i j w P h1 e (e ▸ h2)
  · intro w hw
    have hw' : w.under (𝓞 D.host.F) ∉ (GlobalTheory.SqStep.chs G i j t).T := hw
    rw [eα]
    have h0 : w.under (𝓞 D.host.F) ∉ G.pl.S0 := fun h => hw' (Finset.mem_union_left _ h)
    refine GlobalTheory.T.alpha_unramified_outside hL t i j w h0 fun P hP e => hw' ?_
    refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨P, Finset.mem_filter.2 ⟨Finset.mem_union_right _ hP, fun h => ?_⟩, e⟩)
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
    rw [G.pl.under_w hv] at e
    exact h0 (e ▸ hv)
  · intro w hw
    have hw' : w.under (𝓞 D.host.F) ∉ (GlobalTheory.SqStep.chs G i j t).T := hw
    rw [eβ]
    exact GlobalTheory.T.beta_unramified_outside hL i j w (fun h => hw' (Finset.mem_union_left _ h))

end

private theorem fit_down_left_mul {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} {W : G.Weil}
    {i j : Fin D.R.m} {t μ₀ : T} {Bs : Base D.host.F D.host.E} {a' : ℕ} :
    ∀ (k b : ℕ), Fit G W i j t μ₀ Bs (b + 2 * k) a' → Fit G W i j t μ₀ Bs b a'
  | 0, _, h => by simpa using h
  | k + 1, b, h => fit_down_left_mul k b (Fit.down_left (by rw [show b + 2 * k + 2 = b + 2 * (k + 1) by ring]; exact h))

private theorem fit_down_right_mul {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} {W : G.Weil}
    {i j : Fin D.R.m} {t μ₀ : T} {Bs : Base D.host.F D.host.E} {a : ℕ} :
    ∀ (k b : ℕ), Fit G W i j t μ₀ Bs a (b + 2 * k) → Fit G W i j t μ₀ Bs a b
  | 0, _, h => by simpa using h
  | k + 1, b, h => fit_down_right_mul k b (Fit.down_right (by rw [show b + 2 * k + 2 = b + 2 * (k + 1) by ring]; exact h))

theorem _root_.GlobalTheory.T.exists_realEmbeddings_sharedBase_towerStage : GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∃ emb : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w, ∀ t : T,
        ∃ Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E, Bs.emb = emb ∧ GlobalTheory.SqStepBig.Fit G W i j t μ₀ Bs A.rank A'.rank := by
  classical
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ he hx hR T Lc μ₀ hL G => ?_⟩⟩
  intro W _ i j p q A A' WW X hX
  choose τf hτf using (GlobalTheory.T.exists_conj_tauE_comp_algebraMap_eq_embedding (D := D))
  refine ⟨fun w => ⟨_, hτf w⟩, fun t => ?_⟩
  have hst := standing_of_rec hR hL G t
  obtain ⟨mα, mβ, hα, hβ, hκ⟩ := exps (G := G) hL i j τf hτf
  have hloc : ∀ v ∈ (GlobalTheory.SqStep.chs G i j t).T, ∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v := by
    intro v hv
    rcases Finset.mem_union.1 hv with hv | hv
    · exact ⟨G.pl.w v, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv), G.pl.under_w hv⟩
    · obtain ⟨P, hP, e⟩ := Finset.mem_image.1 hv
      exact ⟨P, (Finset.mem_filter.1 hP).1, e⟩
  have hτ := fun v : ((GlobalTheory.SqStep.chs G i j t).T : Finset (HeightOneSpectrum (𝓞 D.host.F))) =>
    GlobalTheory.LocPlTau.exists_splitPrime_locPl hL t v.1 (hloc v.1 v.2)
  choose τP hτP using hτ
  obtain ⟨v₁, hv₁P, hv₁s, -, ⟨τ₁⟩⟩ := GlobalTheory.T.exists_splitCompletely_auxiliary_place_outside_finset (G := G) hL t (GlobalTheory.SqStep.chs G i j t).T
  let B : Base D.host.F D.host.E := ⟨W.ψ, fun w => ⟨_, hτf w⟩, mα, mβ, (GlobalTheory.SqStep.chs G i j t).T, τP, v₁, τ₁⟩
  have hB : B.IsGood D.sp.cm.sig := GlobalTheory.T.isAdmissibleCMBaseData_of_squareTupleStanding hL W t hst B rfl hloc
  have hsub₀ : (GlobalTheory.SqStep.chs G i j μ₀).T ⊆ (GlobalTheory.SqStep.chs G i j t).T := by
    rw [GlobalTheory.SqStepArith.chs_T_base G hL i j]
    exact Finset.subset_union_left
  have hfit : Fit G W i j t μ₀ B (rankV D (i + 1) (j + 1)) (rankV D i j) := by
    refine ⟨⟨rfl, subset_rfl, hB.psiP, fun v hv => ?_⟩, hB, fun w => ⟨τf w, fun _ => rfl⟩,
      chars_good hL t i j B subset_rfl hv₁P hv₁s (hα t) hβ,
      chars_good hL μ₀ i j B hsub₀ (fun h => hv₁P (hsub₀ h)) hv₁s (hα μ₀) hβ, hκ⟩
    obtain ⟨w, hw, e⟩ := hloc v.1 hv
    rw [hτP v w hw e]
    exact hw
  refine ⟨B, rfl, ?_⟩
  obtain ⟨hp, hq, hA, hA', -⟩ := hX
  have e1 : rankV D (i + 1) (j + 1) = A.rank + 2 * (pp D j - p) := by omega
  have e2 : rankV D i j = A'.rank + 2 * (qq D j - q) := by omega
  rw [e1, e2] at hfit
  exact fit_down_right_mul _ _ (fit_down_left_mul _ _ hfit)

end GlobalTheory.SqStepBig

end
