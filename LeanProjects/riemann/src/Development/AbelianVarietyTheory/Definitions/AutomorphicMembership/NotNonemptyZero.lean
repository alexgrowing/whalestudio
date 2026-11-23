import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostEtaTildeCharacterExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdeleSndSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqOfMapEq
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotIsobaricRigid

noncomputable section

namespace GlobalTheory.HeightCounting.CGTrueModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Char

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsTotallyComplex E]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem locPar_unr (hL : GlobalTheory.Published.LocalLanglandsGL) (χ : HChar E) (h : IsPlaceOver A w) (hu : χ.UnrAt w) :
    (ParLaws.locPar hL (CG.ofChar χ) h).unr ∧
      (ParLaws.locPar hL (CG.ofChar χ) h).frobEig = {(((χ.val w)⁻¹ : ℂˣ) : ℂ)} := by
  have e : χ.loc w = SmGL.unrChar (w.adicCompletion E) (χ.val w) := by
    refine MonoidHom.ext fun x => ?_
    have h2 := unif_spec w
    have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
    have h1 : IsUnitAt w (x * (atFin w (unif w) ^ ord (w.adicCompletion E) x)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
        map_inv₀, map_zpow₀, h2, ← WithZero.exp_zsmul, SphCompletion.ord_completion]
      simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
      rw [WithZero.exp_log h0, mul_inv_cancel₀ h0]
    have h3 := hu _ h1
    rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
    exact h3
  obtain ⟨a, ha, ε, -, H⟩ := ParLaws.isRec_locRec hL h
  have e2 : ParLaws.locPar hL (CG.ofChar χ) h = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
    rw [ParLaws.locPar_ofChar, H.one]
    have hs := ha.smooth (ParLaws.isSmoothChar_loc χ w)
    have : ∀ (ξ : (w.adicCompletion E)ˣ →* ℂˣ) (hξ : WeilDeligne.IsSmooth (ξ.comp a)),
        ξ = SmGL.unrChar (w.adicCompletion E) (χ.val w) →
        WD.lpOfChar h (ξ.comp a) hξ = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
      rintro ξ hξ rfl
      exact Test.lpOfChar_unrChar ha _ _
    exact this _ _ e
  rw [e2, WD.frobEig_diag]
  exact ⟨(WD.unr_mk _).2 (WDRep.unr_diag _), by simp⟩

end Char

section Eta

variable {R : Ranks} {H : Formalism.BasicNotions.Host R} {χ : HChar H.E}

theorem ordF_unif {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : ordF v (unif v) = 1 := by
  have h := unif_spec v
  have hk : Valued.v ((atFin v (Formalism.L2.Host.unif v) : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      v.valuation F (Formalism.L2.Host.unif v : F) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (Formalism.L2.Host.unif v : F)
  unfold IsUnifAt at h
  rw [ordF, ← hk, h, WithZero.log_exp]; simp

theorem prod_val (h : IsEtaT H χ) (v : HeightOneSpectrum (𝓞 H.F)) :
    ∏ P ∈ aboveF (L := H.E) H.F v, χ.val P = if (aboveF (L := H.E) H.F v).card = 1 then -1 else 1 := by
  obtain ⟨c, hc, hcm, hr, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have h1 := h.res.1 v (unif v)
  rw [etaFin, ordF_unif, zpow_one, HChar.resFin, MonoidHom.finsetProd_apply] at h1
  rw [← h1]
  refine Finset.prod_congr rfl fun P hP => ?_
  have hP' : P.under (𝓞 H.F) = v := by simpa [aboveF] using hP
  rw [MonoidHom.comp_apply, GlobalTheory.HeckeProduct.locK_unr χ (h.unr P), hr, hP', ordF_unif, zpow_one]

open Classical in
theorem above_eq {w w' : PlE H} (hc : IsConjPl H w w') : aboveF (L := H.E) H.F (w.under (𝓞 H.F)) = {w, w'} := by
  obtain ⟨c, hc', hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have h1 : GlobalTheory.Mem.Chr.ConjPl c.toRingEquiv w w' :=
    (GlobalTheory.Mem.Chr.conjPl_iff_mem _ _ _).2 fun x y e => hc x y (e.trans (hc' _))
  ext P
  have : P ∈ aboveF (L := H.E) H.F (w.under (𝓞 H.F)) ↔ P.under (𝓞 H.F) = w.under (𝓞 H.F) := by simp [aboveF]
  rw [this, GlobalTheory.Mem.Chr.under_eq_iff_conjPl c hcm.rank hcm.ne w P, Finset.mem_insert, Finset.mem_singleton]
  refine or_congr Iff.rfl ⟨fun h' => (GlobalTheory.Mem.Chr.existsUnique_conjPl _ w).unique h' h1, ?_⟩
  rintro rfl
  exact h1

theorem val_inert (h : IsEtaT H χ) {w : PlE H} (hw : ¬ IsSplitPl H w) : χ.val w = -1 := by
  have e : aboveF (L := H.E) H.F (w.under (𝓞 H.F)) = {w} := by
    ext P
    have : P ∈ aboveF (L := H.E) H.F (w.under (𝓞 H.F)) ↔ P.under (𝓞 H.F) = w.under (𝓞 H.F) := by simp [aboveF]
    rw [this, Finset.mem_singleton]
    refine ⟨fun h' => ?_, fun h' => h' ▸ rfl⟩
    by_contra hne
    exact hw ((GlobalTheory.Mem.GoodPlace.isSplitPl_iff H w).2 ⟨P, fun h => hne h.symm, h'⟩)
  have := prod_val h (w.under (𝓞 H.F))
  rw [e] at this
  simpa using this

theorem val_split (h : IsEtaT H χ) {w w' : PlE H} (hw : IsSplitPl H w) (hc : IsConjPl H w w') :
    χ.val w * χ.val w' = 1 := by
  classical
  have e := above_eq hc
  have hne : w ≠ w' := by
    rintro rfl
    obtain ⟨P, h1, h2⟩ := (GlobalTheory.Mem.GoodPlace.isSplitPl_iff H w).1 hw
    have : P ∈ aboveF (L := H.E) H.F (w.under (𝓞 H.F)) := by simpa [aboveF] using h2
    rw [e] at this
    simp at this
    exact h1 this.symm
  have := prod_val h (w.under (𝓞 H.F))
  rw [e, Finset.prod_pair hne, Finset.card_pair hne] at this
  simpa using this

end Eta

section Family

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {D : D7}
  (T : GlobalTheory.RowTie.WDTie D.nd D.naut)

def ofU {R : Ranks} {H : Formalism.BasicNotions.Host R} (χ : HChar H.E) (h : χ.IsUnitary) : HostCGu H 1 :=
  haveI := host_isCMField H; ⟨CG.ofChar χ, CG.isUnitary_ofChar h⟩

theorem unr_symm (w) (x) : D.naut.unr ((T.e w).symm x) ↔ x.unr := by rw [T.unr, Equiv.apply_symm_apply]

theorem frob_symm (w) (x) (h : x.unr) : D.naut.frobEig ((T.e w).symm x) = x.frobEig := by
  rw [T.frobEig _ _ ((unr_symm T w x).2 h), Equiv.apply_symm_apply]

theorem dim_symm (w) (x) : D.naut.lpDim ((T.e w).symm x) = x.lpDim := by rw [← T.dim, Equiv.apply_symm_apply]

theorem ofU_spec {χ : HChar D.host.E} (h : χ.IsUnitary) {w} (hu : χ.UnrAt w) :
    D.naut.unr ((T.e w).symm (ParLaws.locG hL D.nd.plOm (ofU χ h) w)) ∧
    D.naut.frobEig ((T.e w).symm (ParLaws.locG hL D.nd.plOm (ofU χ h) w)) = {(((χ.val w)⁻¹ : ℂˣ) : ℂ)} := by
  have := host_isCMField D.host
  have h1 := locPar_unr hL χ (D.nd.plOm.2 w) hu
  exact ⟨(unr_symm T w _).2 h1.1, (frob_symm T w _ h1.1).trans h1.2⟩

def trueK {η : HChar D.host.E} (hη : IsEtaT D.host η) : CGK D.naut :=
  haveI := host_isCMField D.host
  have L := ParLaws.laws hL hF D.host D.nd.Om D.nd.plOm
  have hi : (η⁻¹).IsUnitary := fun x => by
    have := hη.unitary x
    change ‖(((η.1 x)⁻¹ : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_inv_eq_inv_val, norm_inv, this, inv_one]
  have hu : ∀ w, (η⁻¹).UnrAt w := fun w x hx => by rw [HChar.loc_inv, hη.unr w x hx, inv_one]
  { CG := fun a => {_π : HostCGu D.host a // 0 < a}
    csd := fun π => π.1.IsCsd
    ralg := fun π => π.1.IsRegAlg
    locG := fun π w => (T.e w).symm (ParLaws.locG hL D.nd.plOm π.1 w)
    locG_dim := fun π w => (dim_symm T w _).trans (L.1 π.1 w)
    locG_unr_ae := fun π => (L.2.1 π.1).mono fun w hw => (unr_symm T w _).2 hw
    tw := fun π χ => ⟨π.1.tw χ.1, π.2⟩
    locG_tw := fun π χ w => (T.e w).injective (by
      rw [T.char _ _ _ ((dim_symm T w _).trans (L.1 χ.1 w)), Equiv.apply_symm_apply, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply]
      exact L.2.2.1 π.1 χ.1 w)
    infG := fun π τ => π.1.infChar τ
    infG_card := fun π => L.2.2.2.1 π.1
    ralg_def := fun π => L.2.2.2.2.1 π.1
    infG_tw := fun π χ => L.2.2.2.2.2.1 π.1 χ.1
    csd_tw := fun π χ => L.2.2.2.2.2.2.1 π.1 χ.1
    csd_unr := fun π w w' hπ hc h => by
      have h0 := (unr_symm T w _).1 h
      have h1 := L.2.2.2.2.2.2.2.1 π.1 w w' hπ hc h0
      exact ⟨(unr_symm T w' _).2 h1.1, by rw [frob_symm T w' _ h1.1, frob_symm T w _ h0, h1.2]⟩
    etaT := ⟨ofU η hη.unitary, one_pos⟩
    etaTinv := ⟨ofU η⁻¹ hi, one_pos⟩
    etaT_unr := fun w => (ofU_spec hL T hη.unitary (hη.unr w)).1
    etaT_inert := fun w hw => by
      rw [(ofU_spec hL T hη.unitary (hη.unr w)).2, val_inert hη hw]; simp
    etaTinv_def := fun w => ⟨(ofU_spec hL T hi (hu w)).1, by
      rw [(ofU_spec hL T hi (hu w)).2, (ofU_spec hL T hη.unitary (hη.unr w)).2]; simp⟩
    etaT_split := fun w w' hw hc a b ha hb => by
      rw [(ofU_spec hL T hη.unitary (hη.unr _)).2, Multiset.singleton_inj] at ha hb
      rw [← ha, ← hb, ← Units.val_mul, ← mul_inv, val_split hη hw hc, inv_one, Units.val_one] }

def cgTrue (hE : IsEmpty D.nd.Loc) {η : HChar D.host.E} (hη : IsEtaT D.host η) :
    CGTrue hL (setCG D hE (trueK hL hF T hη)) (wdCG hE _ T) where
  e := fun _ => Function.Embedding.subtype _
  surj := fun _ h π => ⟨⟨π, h⟩, rfl⟩
  zero := ⟨fun π => lt_irrefl 0 π.2⟩
  loc := fun _ _ w => (T.e w).apply_symm_apply _
  tw := fun _ _ _ => rfl
  inf := fun _ _ _ => rfl
  csd := fun _ _ => Iff.rfl

include hF in

theorem exists_cgTrue (hE : IsEmpty D.nd.Loc) :
    ∃ K : CGK D.naut, Nonempty (CGTrue hL (setCG D hE K) (wdCG hE K T)) := by
  obtain ⟨η, hη⟩ := GlobalTheory.Mem.EtaT.etaT_exists D.R D.host
  exact ⟨_, ⟨cgTrue hL hF T hE hη⟩⟩

end Family

section Rec

open GlobalTheory.RowTie.Model

def emptyBC {R : Ranks} {H : Formalism.BasicNotions.Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (hE : IsEmpty N.Loc) (A : NAut N) : NBC A where
  AU := fun _ => PEmpty
  multAU := fun _ a => a.elim
  sphAU := fun _ a => a.elim
  locAU := fun _ a => a.elim
  satAU := fun _ a => a.elim
  satAU_card := fun _ a => a.elim
  Wt := fun _ => PEmpty
  infW := fun _ a => a.elim
  infW_card := fun _ a => a.elim
  wtAU := fun _ a => a.elim
  infW_alg := fun _ a => a.elim
  embAV := fun i => hE.elim i
  embAV_inj := fun i => hE.elim i
  embAV_loc := fun i => hE.elim i
  embAV_sat := fun i => hE.elim i
  embAV_sph := fun i => hE.elim i
  embAV_inf := fun i => hE.elim i

set_option maxHeartbeats 2000000 in

theorem exists_tie (D : D7) (hE : IsEmpty D.nd.Loc) :
    ∃ D' : D7, IsEmpty D'.nd.Loc ∧ Nonempty (GlobalTheory.RowTie.WDTie D'.nd D'.naut) := by
  have : IsEmpty (ndLab D.nd D.nd.lab D.nd.lab_monic).Loc := hE
  let γ : Fin 2 → PlE D.host → G D.host.E D.nd.Om := fun k => Function.extend (D.naut.plGw k) (D.ntypes.tg k) fun _ => 1
  have hγ : ∀ k v, γ k (D.naut.plGw k v) = D.ntypes.tg k v := fun k v => (D.naut.plGw_inj k).extend_apply _ _ v
  let A := wdAut (ndLab D.nd D.nd.lab D.nd.lab_monic) D.naut D.ntypes.teichC γ
  refine ⟨setAut D hE D.nd.lab D.nd.lab_monic A (emptyBC hE A) D.ntypes.tg_mem D.ntypes.tg_gen (fun k v L hL => ?_), hE,
    ⟨tie (ndLab D.nd D.nd.lab D.nd.lab_monic) D.naut D.ntypes.teichC γ⟩⟩
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have := WD.inePol_eq_of_natDegree_lab (D.ntypes.teichC k) (γ k (D.naut.plGw k v)) L hL
  exact (congrArg (WD.inePol L) (hγ k v).symm).trans this

theorem exists_record (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (D : D7)
    (hE : IsEmpty D.nd.Loc) : ∃ (D' : D7) (T : GlobalTheory.RowTie.WDTie D'.nd D'.naut), Nonempty (CGTrue hL D' T) := by
  obtain ⟨D', h, ⟨T⟩⟩ := exists_tie D hE
  obtain ⟨K, hK⟩ := exists_cgTrue hL hF T h
  exact ⟨_, _, hK⟩

end Rec

section Cons

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut}

theorem ralg_iff (C : CGTrue hL D T) {a} (π : D.naut.CG a) :
    haveI := host_isCMField D.host; D.naut.ralg π ↔ (C.e a π).IsRegAlg := by
  rw [D.naut.ralg_def]
  simp only [C.inf]
  have := host_isCMField D.host
  exact (CG.isRegAlg_iff (C.e a π).1).symm

theorem not_nonempty_zero (C : CGTrue hL D T) : ¬ Nonempty (D.naut.CG 0) :=
  not_nonempty_iff.2 C.zero

theorem nontrivial_one (C : CGTrue hL D T) : Nontrivial (D.naut.CG 1) :=
  haveI := host_isCMField D.host
  haveI : Nontrivial (HostCGu D.host 1) := inferInstanceAs (Nontrivial (CGu D.host.E 1))
  (C.equiv 1 one_pos).nontrivial

theorem frob_one (C : CGTrue hL D T) (π : D.naut.CG 1) (w)
    (hu : haveI := host_isCMField D.host; (CGu.equivChar _ (C.e 1 π)).1.UnrAt w) :
    haveI := host_isCMField D.host
    D.naut.unr (D.naut.locG π w) ∧
      D.naut.frobEig (D.naut.locG π w) = {((((CGu.equivChar _ (C.e 1 π)).1.val w)⁻¹ : ℂˣ) : ℂ)} := by
  have := host_isCMField D.host
  have h1 := locPar_unr hL _ (D.nd.plOm.2 w) hu
  rw [CGu.ofChar_equivChar] at h1
  have h2 : D.naut.unr (D.naut.locG π w) := by rw [T.unr, C.loc]; exact h1.1
  exact ⟨h2, by rw [T.frobEig _ _ h2, C.loc]; exact h1.2⟩

end Cons

end GlobalTheory.HeightCounting.CGTrueModel

end
