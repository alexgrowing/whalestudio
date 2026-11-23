import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmConjugationOmegaStatement
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.MemN.exists_nTw_empty : ∀ (B : Base) (C : Cols B) (W : RowsRest B C) (nd : NData B.R B.host W.what₂), IsEmpty nd.Loc → ∃ tw : NTw B.R B.host W.what₂ B.LL0 nd, IsEmpty tw.Tw := by
  intro B C W nd h
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_cm_conjugation_omega B.R B.host W.what₂ nd
  exact ⟨{
      cc := c
      cc_cm := hc
      Tw := Empty
      l := fun i => i.elim
      lPrime := fun i => i.elim
      O0 := fun i => i.elim
      crO0 := fun i => i.elim
      twistBaseCoefficientRing_isDomain := fun i => i.elim
      twistBaseCoefficientRing_isDVR := fun i => i.elim
      algO0 := fun i => i.elim
      twistBaseCoefficientRing_finite_padic := fun i => i.elim
      twistBaseCoefficientRing_residueField_finite := fun i => i.elim
      topO0 := fun i => i.elim
      twistBaseCoefficientRing_topologicalRing := fun i => i.elim
      twistBaseCoefficientRing_isAdic := fun i => i.elim
      emb0 := fun i => i.elim
      emb0b := fun i => i.elim
      restX_coefficientEmbedding_conj := fun i => i.elim
      O := fun i => i.elim
      crO := fun i => i.elim
      domO := fun i => i.elim
      dvrO := fun i => i.elim
      algO := fun i => i.elim
      O_inj := fun i => i.elim
      O_l := fun i => i.elim
      topO := fun i => i.elim
      trO := fun i => i.elim
      O_adic := fun i => i.elim
      resO_ac := fun i => i.elim
      O_complete := fun i => i.elim
      Ok := fun i => i.elim
      crOk := fun i => i.elim
      domOk := fun i => i.elim
      dvrOk := fun i => i.elim
      algOk := fun i => i.elim
      Ok_inj := fun i => i.elim
      Ok_fin := fun i => i.elim
      zk := fun i => i.elim
      zk_prim := fun i => i.elim
      Ok_gen := fun i => i.elim
      pD := fun i => i.elim
      pD_eq := fun i => i.elim
      delta := fun i => i.elim
      delta_open := fun i => i.elim
      delta_anti := fun i => i.elim
      delta_ram := fun i => i.elim
      delta_15 := fun i => i.elim
      delta_tame := fun i => i.elim
      chi1 := fun i => i.elim
      twistCharacterFamily_continuous := fun i => i.elim
      twistCharacterFamily_unramified := fun i => i.elim
      twistCharacterFamily_at_auxiliaryPlaces := fun i => i.elim
      twistCharacterFamily_tame := fun i => i.elim
      Sig := fun i => i.elim
      finSig := fun i => i.elim
      jS := fun i => i.elim
      jS_range := fun i => i.elim
      side := fun i => i.elim
      rhoS := fun i => i.elim
      rhoS_cont := fun i => i.elim
      S0 := fun i => i.elim
      twistExcludedPlaces_contains_residueChar := fun i => i.elim
      placesOver_subset_exceptional := fun i => i.elim
      primes_subset_exceptional := fun i => i.elim
      B := fun i => i.elim
      acgB := fun i => i.elim
      modB := fun i => i.elim
      freeB := fun i => i.elim
      finB := fun i => i.elim
      Theta := fun i => i.elim
      ThetaPsi := fun i => i.elim
      ThetaPsi_one := fun i => i.elim
      hk := fun i => i.elim
      hk_zero := fun i => i.elim
      hEig := fun i => i.elim
      abelian₂ := fun i => i.elim
      finLam := fun i => i.elim
      jL := fun i => i.elim
      sideL := fun i => i.elim
      s2 := fun i => i.elim
      jL_range := fun i => i.elim
      lamG := fun i => i.elim
      lamG_cont := fun i => i.elim
      lamG_unr := fun i => i.elim
      lamG_pD := fun i => i.elim
      lamG_anti := fun i => i.elim
      Xv := fun i => i.elim
      Xv_def := fun i => i.elim
      qs := fun i => i.elim
      qs_sq := fun i => i.elim
      qs_conj := fun i => i.elim
      RCG := fun i => i.elim
      grpRCG := fun i => i.elim
      finRCG := fun i => i.elim
      RCG_l := fun i => i.elim
      art := fun i => i.elim
      art_surj := fun i => i.elim
      art_cont := fun i => i.elim
      art_anti := fun i => i.elim
      art_unr := fun i => i.elim
      art_univ := fun i => i.elim
      res := fun i => i.elim
      res_art := fun i => i.elim
      th := fun i => i.elim
      twOf := fun a => h.elim a
      twSide := fun a => h.elim a
      twOf_l := fun a => h.elim a
      twist₂ := fun a => h.elim a
      twO_emb := fun a => h.elim a
      psiL := fun a => h.elim a
      psiL_ord := fun a => h.elim a
      psiL_open := fun a => h.elim a
      psiL_anti := fun a => h.elim a
      psiL_ram := fun a => h.elim a
      psiL_l := fun a => h.elim a
      chi_tw := fun a => h.elim a }, (inferInstance : IsEmpty Empty)⟩
