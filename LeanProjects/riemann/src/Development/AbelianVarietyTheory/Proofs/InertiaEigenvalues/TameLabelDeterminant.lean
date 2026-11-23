import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjGenTransportExists
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDetStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitaryStatement
import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatePlacesCompletionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjSelfDualHeckeCharConjugatePlaceComponentInvStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LabConjPlace

open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL

theorem loc_artin_ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a) (χ : HChar E) (hu : χ.UnrAt w)
    (σ : Weil h) (hσ : (σ : G E Ω) ∈ Ine (F := E) A) : χ.loc w (a σ) = 1 := by
  have h1 := ha.ord_eq σ
  rw [deg_eq_zero_iff.2 hσ, neg_zero, SphCompletion.ord_completion, neg_eq_zero] at h1
  have h0 : Valued.v ((a σ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≠ 0 := by simp
  apply hu
  show Valued.v _ = 1
  rw [← WithZero.exp_log h0, h1, WithZero.exp_zero]

end GlobalTheory.LabConjPlace

open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.LabConjPlace in

theorem GlobalTheory.LabConjPlace.main : ∀ (hPr : GlobalTheory.NRows.Hypotheses₂) (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), LabAll D P.T → ∀ (S : Reading P.T), IsTrue P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) (hχ : GlobalTheory.SmGL.IsSmoothChar (S i _ hw).mu) (u : (ZMod (D.host.g k))ˣ), GlobalTheory.SplitWeil.IsTame (S i _ hw).mu → labAt hL D k v (Irr.ofDet 1 (S i _ hw).mu hχ) = X - C (u : ZMod (D.host.g k)) → ∀ (w' : PlE D.host), IsConjPl D.host (D.naut.plGw k v) w' → ∀ s : ℝ, D.naut.items₂ k w' (D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w') s) = X - C ((u⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)) := by
  intro hPr hL D P hLab S hS i k v hw hχ u _ hlab w' hc s
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨γ, hγ1, hγ2, hγ3⟩ := hLab
  have hw'over : w' ∈ placesOver D.host.E (D.host.g k) := by
    have h0 := D.naut.plGw_over k v
    simp only [placesOver, Set.mem_setOf_eq] at h0 ⊢
    exact (hc _ _ (by simp)).1 h0
  rw [hγ3 k w' hw'over, P.T.tw, WD.lab_lpTw]
  obtain ⟨jj, hjj⟩ : ∃ jj : Fin D.R.m, jj.1 + 1 = D.nd.j i :=
    ⟨⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, by have := D.nd.j_range i; simp; omega⟩
  set χ := D.naut.tw (D.naut.muC i) D.naut.etaTinv with hχdef
  set μH := P.tp.tup (D.nd.mu i) jj with hμH
  have e1 : (P.chr.e1 χ).1 = μH * P.cf.eta⁻¹ := by
    rw [hχdef, P.chr.tw, P.chr.muC i jj hjj, P.chr.etaTinv]
  have hcomp' : IsComp (P.chr.e1 χ).1 w' ((P.chr.e1 χ).1.loc w') := ⟨ParLaws.isSmoothChar_loc _ w', fun x => rfl⟩
  rw [GlobalTheory.T.rank_one_local_component_det hPr.fin hL D P χ w' _ hcomp']
  obtain ⟨a', ha', ε', -, H'⟩ := ParLaws.isRec_locRec hL (D.nd.plOm.2 w')
  change WD.lab _ _ (ParLaws.locRec hL (D.nd.plOm.2 w') (GlobalTheory.LocGL.IrrGL.ofChar ((P.chr.e1 χ).1.loc w') hcomp'.1)) = _
  rw [H'.one]

  obtain ⟨a, ha, ε, -, Hw⟩ := ParLaws.isRec_locRec hL (D.nd.plOm.2 (D.naut.plGw k v))
  have hlab' : WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v)
      (WD.lpOfChar (D.nd.plOm.2 (D.naut.plGw k v)) ((S i _ hw).mu.comp a) (ha.smooth hχ)) = X - C (u : ZMod (D.host.g k)) := by
    rw [← Hw.one _ hχ]; exact hlab
  have HS : TeichmullerInertiaLabelCondition (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.ntypes.teichC k) (D.ntypes.tg k v) := by
    by_contra hn
    rw [WD.lab_of_not hn] at hlab'
    have := congrArg natDegree hlab'
    rw [natDegree_one, natDegree_X_sub_C] at this
    exact absurd this (by norm_num)
  have hdeg : (WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v)
      (WD.lpOfChar (D.nd.plOm.2 (D.naut.plGw k v)) ((S i _ hw).mu.comp a) (ha.smooth hχ))).natDegree =
      WD.lpDim (WD.lpOfChar (D.nd.plOm.2 (D.naut.plGw k v)) ((S i _ hw).mu.comp a) (ha.smooth hχ)) := by
    rw [hlab', natDegree_X_sub_C]; simp [WD.lpOfChar]
  have htame := WD.tame_of_natDegree_lab hdeg
  rw [WD.lpOfChar] at htame
  have hwild : ∀ σ : Weil (D.nd.plOm.2 (D.naut.plGw k v)), (σ : G _ _) ∈ Wild D.host.E (D.nd.plOm.1 (D.naut.plGw k v)) →
      ((S i _ hw).mu.comp a) σ = 1 := by
    intro σ hσ
    have := congrFun (LinearMap.congr_fun ((WD.tame_mk _).mp htame σ hσ) fun _ => 1) 0
    exact Units.ext (by simpa using this)
  have hval := (WD.lab_lpOfChar_eq_iff HS (ha.smooth hχ) hwild u).mp hlab'

  have hμw : μH.loc (D.naut.plGw k v) = (S i _ hw).mu := by
    obtain ⟨ξ₀, -, huniq, -⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E μH (D.naut.plGw k v)
    exact (huniq _ ⟨ParLaws.isSmoothChar_loc _ _, fun x => rfl⟩).trans (huniq _ (hS.mu i _ hw jj hjj)).symm

  obtain ⟨c, hcE, hcA, hcγ⟩ := hγ2 k v w' hc
  set τc : D.host.E ≃+* D.host.E := (D.host.conj : D.host.E ≃+* D.host.E) with hτc
  have hcE' : ∀ x, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (τc x) := hcE
  have hγ' : γ k w' = GlobalTheory.ConjTransport.conjG c τc hcE' (D.ntypes.tg k v) := by
    ext y
    rw [GlobalTheory.ConjTransport.conjG_apply]
    have := hcγ (c.symm y)
    rw [RingEquiv.apply_symm_apply] at this
    exact this
  have hIne' : γ k w' ∈ Ine (F := D.host.E) (D.nd.plOm.1 w') := by
    rw [hγ']; exact GlobalTheory.ConjTransport.conjG_mem_Ine c τc hcE' hcA HS.2.1
  have HS' : TeichmullerInertiaLabelCondition (D.nd.plOm.1 w') w' (D.ntypes.teichC k) (γ k w') :=
    ⟨GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) hw'over, hIne', HS.2.2⟩
  have hcsd : IsCSD D.host μH := by
    rw [hμH, ← P.chr.muC i jj hjj]; exact (P.chr.csd _).1 (D.naut.muC_csd i)
  obtain ⟨ic, hic, hicE, hicμ⟩ := GlobalTheory.T.conjSelfDual_heckeChar_conjugatePlace_component_inv D.host μH hcsd _ w' hc
  have htr : ∀ (σ : Weil (D.nd.plOm.2 (D.naut.plGw k v))) (σ' : Weil (D.nd.plOm.2 w')),
      (∀ z, c ((σ : G D.host.E D.nd.Om) z) = (σ' : G D.host.E D.nd.Om) (c z)) →
      μH.loc w' (a' σ') = ((S i _ hw).mu (a σ))⁻¹ := by
    intro σ σ' hσ
    rw [← GlobalTheory.T.conjugate_places_completion hL (D.nd.plOm.2 (D.naut.plGw k v)) (D.nd.plOm.2 w') c τc.toRingHom ic
      (fun z => (hcA z).symm) hcE' hic hicE Hw H' (μH.loc w') (ParLaws.isSmoothChar_loc _ _) σ σ' hσ, hicμ, hμw]
  have heta : ∀ σ' : Weil (D.nd.plOm.2 w'), (σ' : G D.host.E D.nd.Om) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w') →
      P.cf.eta.loc w' (a' σ') = 1 := fun σ' hσ' => loc_artin_ine ha' _ (P.cf.isEta.unr w') σ' hσ'
  have hξ : ∀ σ', ((P.chr.e1 χ).1.loc w') (a' σ') = μH.loc w' (a' σ') * (P.cf.eta.loc w' (a' σ'))⁻¹ := by
    intro σ'; rw [e1, HChar.loc_mul, HChar.loc_inv]
  have hwild' : ∀ σ' : Weil (D.nd.plOm.2 w'), (σ' : G _ _) ∈ Wild D.host.E (D.nd.plOm.1 w') →
      (((P.chr.e1 χ).1.loc w').comp a') σ' = 1 := by
    intro σ' hσ'
    have hA' : ∀ y, y ∈ D.nd.plOm.1 w' ↔ c.symm y ∈ D.nd.plOm.1 (D.naut.plGw k v) := fun y => by
      rw [hcA, RingEquiv.apply_symm_apply]
    have hσw : GlobalTheory.ConjTransport.conjG c.symm τc.symm (GlobalTheory.ConjTransport.symm_alg c τc hcE') (σ' : G _ _) ∈
        Wild D.host.E (D.nd.plOm.1 (D.naut.plGw k v)) :=
      GlobalTheory.ConjTransport.conjG_mem_wild c.symm τc.symm _ hA' hσ'
    let σ : Weil (D.nd.plOm.2 (D.naut.plGw k v)) := ⟨_, Ine_le_Weil _ (Wild_le_Ine hσw)⟩
    have h1 := htr σ σ' (fun z => by
      show c (GlobalTheory.ConjTransport.conjG c.symm τc.symm _ (σ' : G _ _) z) = _
      rw [GlobalTheory.ConjTransport.conjG_apply, RingEquiv.symm_symm, RingEquiv.apply_symm_apply])
    have h2 := hwild σ hσw
    rw [MonoidHom.comp_apply] at h2
    rw [MonoidHom.comp_apply, hξ, h1, heta σ' (Wild_le_Ine hσ'), h2]
    simp
  rw [WD.lab_lpOfChar_eq_iff HS' _ hwild']
  rw [MonoidHom.comp_apply, hξ, htr ⟨D.ntypes.tg k v, Ine_le_Weil _ HS.2.1⟩ _ (fun z => (hcγ z).symm),
    heta _ hIne', inv_one, mul_one]
  have hx : algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)) ≠ 0 :=
    (_root_.map_ne_zero _).2 u.ne_zero
  rw [MonoidHom.comp_apply] at hval
  rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, ← hval, map_inv₀]
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, inv_mul_cancel₀ hx, map_one]
