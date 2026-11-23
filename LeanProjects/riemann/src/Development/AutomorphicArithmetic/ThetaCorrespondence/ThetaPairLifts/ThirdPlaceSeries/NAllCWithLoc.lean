import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NAllCWithLoc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTiedRowLoc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalTiedWithLoc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NTiedLocTiedOfBuilt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypesOpenWithLoc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NRhoTiedWithLoc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTwOpenExpRelStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.HeightCounting.FitAll
theorem nAllC_withLoc_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists), _root_.GlobalTheory.HeightCounting.LpCmpAlt hL → _root_.GlobalTheory.HeightCounting.CgCmpAlt hL → ∀ (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D') (fr : OmFrame b.D), fr.jE = b.jE → (PhtOn b.A.wd fr fun _ _ _ _ => True) → Elem b.D → GlobalTheory.RowTie.ChebSplit b.D.nd → lowPr b.D ⊆ b.low → ∃ a : _root_.GlobalTheory.HeightCounting.NAllCAlt (withLoc b.L) (chL b.L b.C), (⟨a.cf, a.tp⟩ : Σ c : CharFrame (withLoc b.L), TupTied (withLoc b.L) c (chL b.L b.C)) = ⟨cfL b.L b.cf, tpL b.L b.tp⟩ ∧ a.gal.fr.jE = b.jE ∧ a.gal.mt = mtL b.L b.M ∧ ExpRel b.L b.Bs.exp a.exp ∧ Nonempty (NCharTied (withLoc b.L) (cfL b.L b.cf) (chL b.L b.C) (tpL b.L b.tp)) ∧ NGalChrTied (withLoc b.L) (cfL b.L b.cf) (chL b.L b.C) (tpL b.L b.tp) ∧ ∀ F : RowFrame (withLoc b.L), F.rep = b.rep → _root_.Formalism.L2.RowLocTiedAlt (withLoc b.L) a.gal.lp F := by
  intro hL hLp hCg D' b fr hfr hpht hE hCh hlow
  obtain ⟨g, hgj, hgm, hgt, ⟨dat⟩, ⟨cov⟩, hrow⟩ :=
    _root_.GlobalTheory.FitGal.galTied_withLoc_alt hL hLp D' b fr hfr hpht hE.star hE.int hE.split hCh
  obtain ⟨⟨nt⟩, ⟨lt⟩⟩ := _root_.GlobalTheory.HeightCounting.nTied_locTied_of_built_alt hL hCg D' b
  obtain ⟨TO⟩ := _root_.GlobalTheory.HeightCounting.typesOpen_withLoc_alt b.D b.cf b.jE b.A b.low b.Pq b.S b.hL b.eig b.θ b.Bs b.M b.C b.tp b.ch b.mt
    hE.star hE.int hE.split hCh b.big b.L b.Sp b.Au b.ss
  have rho : NR.NRhoTied (withLoc b.L) := _root_.GlobalTheory.HeightCounting.nRhoTied_withLoc_alt hL D' b hE.star hE.int hE.split hCh TO
  obtain ⟨Tw, hX⟩ := _root_.GlobalTheory.T.exists_twOpen_expRel_of_chebSplit hL D' b hE hCh
  have ty : NormalizedTypesCompatibility (withLoc b.L) b.jE :=
    { eM := TO.par.eM, eM_K := TO.par.eM_K, tA := TO.grp.tA, tκ := TO.grp.tκ, teichC_def := TO.grp.teichC_def,
      iota_loc := fun i => ⟨TO.plB _, TO.plκ _, TO.plB_loc i, TO.plB_iota i⟩,
      ζ := TO.grp.ζ, ζ_gen := TO.grp.ζ_gen, O := TO.grp.O, eSer_def := TO.grp.eSer_def, kv := TO.grp.kv,
      tg_tame := TO.grp.tg_tame, O_equiv := TO.grp.O_equiv, O_tw := TO.grp.O_tw, eP := TO.par.eP,
      locPar_def := TO.par.locPar_def }
  let F0 : TwFrame (withLoc b.L) := ⟨Tw.twF.K0, Tw.twF.eO0, Tw.twF.j0, Tw.twF.Lw, Tw.twF.eO, Tw.twF.eOk, Tw.twF.iCq, Tw.twF.S0x⟩
  have hlow' : lowPr (withLoc b.L) ⊆ b.low := hlow
  have tw : NTwTied (withLoc b.L) F0 := by
    have T := Tw.tw
    have hN : Ideal.absNorm (withLoc b.L).host.ccK ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact (withLoc b.L).host.ccK_ne_bot
    have hd : (NumberField.discr (withLoc b.L).host.E).natAbs ≠ 0 :=
      Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero (withLoc b.L).host.E)
    exact ⟨T.pl_emb, T.ringSpec_baseIntegersEquiv_algebraMap, T.ringSpec_baseEmbedding_compatible, T.eO_alg, T.eOk_alg, T.mu_g, T.hk_split, T.ringSpec_excludedPlaces_eq, T.concreteTwistFrame_extraExcludedPlaces_conj, T.B_range,
      T.sig_inj, T.qs_pos,
      fun i p hp h => T.concreteTwistFrame_extraExcluded_over_smallPrimes i p (hlow' (by simp [lowPr, Nat.mem_primeFactors, hp, h, hN])),
      fun i => T.concreteTwistFrame_extraExcluded_over_smallPrimes i _ (hlow' (by simp [lowPr])), fun i => T.concreteTwistFrame_extraExcluded_over_smallPrimes i _ (hlow' (by simp [lowPr])),
      fun i p hp h => T.concreteTwistFrame_extraExcluded_over_smallPrimes i p (hlow' (by simp [lowPr, Nat.mem_primeFactors, hp, h, hd]))⟩
  refine ⟨
    { gal := g, n := (b.eq ▸ nt), loc := (b.eq ▸ lt), data := dat, cover := (hgm ▸ cov), chiD := Tw.chiD, chi := Tw.chi,
      rho := rho, types := (hgj.symm ▸ ty), twF := F0, tw := tw, nct := Tw.ch.nct, exp := Tw.exp, choice := Tw.ch.choice,
      eMt_level := by rw [hgm]; exact Tw.ch.eMt_level,
      cf := cfL b.L b.cf, tp := tpL b.L b.tp, tupLink := hgt,
      eta_eq := Tw.eta_eq, ringSpec_normalisedCharacter_eq := Tw.ringSpec_normalisedCharacter_eq, del_eq := Tw.del_eq, psi_eq := Tw.psi_eq,
      plB := TO.plB, plκ := TO.plκ, plB_loc := TO.plB_loc, plB_iota := TO.plB_iota,
      etaT_link := Tw.etaT_link, muC_link := Tw.muC_link, iCq_embO := Tw.iCq_embO, embO_star := Tw.embO_star },
    rfl, hgj, hgm, hX, ⟨Tw.chrN⟩, Tw.chrGal, hrow⟩
end GlobalTheory.HeightCounting.FitAll
end
