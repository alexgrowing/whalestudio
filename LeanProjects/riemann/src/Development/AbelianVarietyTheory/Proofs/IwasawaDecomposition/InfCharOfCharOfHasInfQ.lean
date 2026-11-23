import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostEtaTildeCharacterExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdeleSndSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqOfMapEq
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotIsobaricRigid
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryRationalInfTypeSubgroupAndInfTypeUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharConjSelfDualFiniteIdelicIffLocalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharConjSelfDualInfinityInfinitesimalIffFieStatement

noncomputable section

namespace GlobalTheory.HeightCounting.TrueSide

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
    have : ∀ (ξ : (w.adicCompletion E)ˣ →* ℂˣ) (hξ : WeilDeligne.IsSmooth (ξ.comp a)),
        ξ = SmGL.unrChar (w.adicCompletion E) (χ.val w) →
        WD.lpOfChar h (ξ.comp a) hξ = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
      rintro ξ hξ rfl
      exact Test.lpOfChar_unrChar ha _ _
    exact this _ _ e
  rw [e2, WD.frobEig_diag]
  exact ⟨(WD.unr_mk _).2 (WDRep.unr_diag _), by simp⟩

theorem locPar_unr_iff (hL : GlobalTheory.Published.LocalLanglandsGL) (χ : HChar E) (h : IsPlaceOver A w) :
    (ParLaws.locPar hL (CG.ofChar χ) h).unr ↔ χ.UnrAt w := by
  obtain ⟨a, ha, ε, -, H⟩ := ParLaws.isRec_locRec hL h
  rw [ParLaws.locPar_ofChar, H.one, Test.unr_lpOfChar_iff ha (ParLaws.isSmoothChar_loc χ w)]
  refine forall_congr' fun x => imp_congr_left ?_
  have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
  rw [← ord_eq_zero_iff, SphCompletion.ord_completion, neg_eq_zero, IsUnitAt]
  constructor
  · intro hl
    rw [← WithZero.exp_log h0, hl, WithZero.exp_zero]
  · intro hv
    rw [hv, WithZero.log_one]

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

theorem eq_ofU {R : Ranks} {H : Formalism.BasicNotions.Host R} (σ : HostCGu H 1) :
    haveI := host_isCMField H; σ = ofU (CGu.equivChar H.E σ).1 (CGu.equivChar H.E σ).2 :=
  haveI := host_isCMField H; Subtype.ext (CGu.ofChar_equivChar σ).symm

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

theorem ofU_unr_iff {χ : HChar D.host.E} (h : χ.IsUnitary) (w) :
    D.naut.unr ((T.e w).symm (ParLaws.locG hL D.nd.plOm (ofU χ h) w)) ↔ χ.UnrAt w := by
  have := host_isCMField D.host
  exact (unr_symm T w _).trans (locPar_unr_iff hL χ (D.nd.plOm.2 w))

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

def trueK {η : HChar D.host.E} (hη : IsEtaT D.host η) : CGK D.naut :=
  haveI := host_isCMField D.host
  have L := ParLaws.laws hL hF D.host D.nd.Om D.nd.plOm
  have hi : (η⁻¹).IsUnitary := fun x => by
    have := hη.unitary x
    change ‖(((η.1 x)⁻¹ : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_inv_eq_inv_val, norm_inv, this, inv_one]
  have hu : ∀ w, (η⁻¹).UnrAt w := fun w x hx => by rw [HChar.loc_inv, hη.unr w x hx, inv_one]
  { CG := fun a => {π : HostCGu D.host a // 0 < a}
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
    etaT := ⟨ofU η hη.unitary, Nat.one_pos⟩
    etaTinv := ⟨ofU η⁻¹ hi, Nat.one_pos⟩
    etaT_unr := fun w => (ofU_spec hL T hη.unitary (hη.unr w)).1
    etaT_inert := fun w hw => by
      rw [(ofU_spec hL T hη.unitary (hη.unr w)).2, val_inert hη hw]; simp
    etaTinv_def := fun w => ⟨(ofU_spec hL T hi (hu w)).1, by
      rw [(ofU_spec hL T hi (hu w)).2, (ofU_spec hL T hη.unitary (hη.unr w)).2]; simp⟩
    etaT_split := fun w w' hw hc a b ha hb => by
      rw [(ofU_spec hL T hη.unitary (hη.unr _)).2, Multiset.singleton_inj] at ha hb
      rw [← ha, ← hb, ← Units.val_mul, ← mul_inv, val_split hη hw hc, inv_one, Units.val_one] }

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

def trueCG (hE : IsEmpty D.nd.Loc) {η : HChar D.host.E} (hη : IsEtaT D.host η) :
    CGTrue hL (setCG D hE (trueK hL hF T hη)) (wdCG hE _ T) where
  e := fun _ => ⟨Subtype.val, Subtype.val_injective⟩
  surj := fun _ ha π => ⟨⟨π, ha⟩, rfl⟩
  zero := ⟨fun π => lt_irrefl 0 π.2⟩
  loc := fun _ _ w => (T.e w).apply_symm_apply _
  tw := fun _ _ _ => rfl
  inf := fun _ _ _ => rfl
  csd := fun _ _ => Iff.rfl

end Family

section Side

theorem csdFin {R : Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E) : haveI := host_isCMField H;
    (∀ u : (Af H.E)ˣ, χ.1 (finId H.E (Units.map (conjFin (IsCMField.complexConj H.E).toRingEquiv).toMonoidHom u)⁻¹) =
      χ.1 (finId H.E u)) ↔
    ∀ w w', IsConjPl H w w' → ∀ k : H.Eˣ,
      χ.locK w' (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.locK w k)⁻¹ := GlobalTheory.T.heckeChar_conjSelfDual_finite_idelic_iff_local H χ

theorem csdInf {R : Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E) : haveI := host_isCMField H;
    (∀ z, dchi χ (-star z) = dchi χ z) ↔
    ∀ k : H.Eˣ, χ.inf (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.inf k)⁻¹ := GlobalTheory.T.heckeChar_conjSelfDual_infinity_infinitesimal_iff_field H χ

theorem isCsd_ofChar_iff {R : Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E) :
    haveI := host_isCMField H; (CG.ofChar χ).IsCsd ↔ IsCSD H χ := by
  haveI := host_isCMField H
  rw [CG.isCsd_ofChar, CG.thetaInv_one_iff, csdFin H χ, csdInf H χ]
  rfl

theorem infChar_ofChar_of_hasInfQ {R : Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E) (a : R.Psi → ℚ)
    (h : χ.HasInfQ (embPsi H) a) (g : R.Psi) : haveI := host_isCMField H;
    (CG.ofChar χ).infChar (embPsi H g) = {(a g : ℂ)} ∧
      (CG.ofChar χ).infChar ((starRingEnd ℂ).comp (embPsi H g)) = {-(a g : ℂ)} := by
  haveI := host_isCMField H
  obtain ⟨n, hn, hi⟩ := h
  have hI : Function.Injective fun i => InfinitePlace.mk (embPsi H i) := fun i j e => by
    rcases InfinitePlace.mk_eq_iff.1 e with e | e
    · exact GlobalTheory.HalfIntChars.embPsi_inj H e
    · exact (GlobalTheory.HalfIntChars.embPsi_ne_conj H j i (e.symm.trans (RingHom.ext fun x => rfl))).elim
  have h3 := (InfType.expo_of_infType _ χ).2.2 _ _ _ hI hi g
  have ha : ((n g : ℂ) / 2) = (a g : ℂ) := by
    have := hn g
    have e : (a g : ℂ) = ((a g : ℚ) : ℂ) := rfl
    rw [e, show (a g : ℚ) = (n g : ℚ) / 2 by rw [this]; ring]
    push_cast; ring
  refine ⟨by rw [CG.infChar_ofChar, h3.1, ha], ?_⟩
  rw [show (starRingEnd ℂ).comp (embPsi H g) = ComplexEmbedding.conjugate (embPsi H g) from RingHom.ext fun x => rfl,
    CG.infChar_ofChar, h3.2, neg_div, ha]

end Side

section Main

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {D : D7}
  (T : GlobalTheory.RowTie.WDTie D.nd D.naut)

theorem equivChar_ofU {R : Ranks} {H : Formalism.BasicNotions.Host R} (χ : HChar H.E) (h : χ.IsUnitary) :
    haveI := host_isCMField H; (CGu.equivChar H.E (ofU χ h)).1 = χ :=
  haveI := host_isCMField H; CG.toChar_ofChar χ

theorem exists_ofU {R : Ranks} {H : Formalism.BasicNotions.Host R} (σ : HostCGu H 1) : ∃ χ h, σ = ofU χ h :=
  ⟨_, _, eq_ofU σ⟩

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

def trueSide (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (hP : ∀ k v, cf.P.Div k (D.naut.plGw k v)) :
    CharSide (setCG D hE (trueK hL hF T cf.isEta)) (cfCG hE _ cf) :=
  haveI := host_isCMField D.host
  { e1 := (Equiv.subtypeUnivEquiv (fun _ => Nat.one_pos)).trans (CGu.equivChar D.host.E)
    unr_iff := fun π w => by
      obtain ⟨χ, h, e⟩ := exists_ofU π.1
      change D.naut.unr ((T.e w).symm (ParLaws.locG hL D.nd.plOm π.1 w)) ↔ (CGu.equivChar D.host.E π.1).1.UnrAt w
      rw [e, equivChar_ofU]
      exact ofU_unr_iff hL T h w
    frob := fun π w hu => by
      obtain ⟨χ, h, e⟩ := exists_ofU π.1
      change (CGu.equivChar D.host.E π.1).1.UnrAt w at hu
      change D.naut.frobEig ((T.e w).symm (ParLaws.locG hL D.nd.plOm π.1 w)) =
        {(((CGu.equivChar D.host.E π.1).1.val w)⁻¹ : ℂˣ).1}
      rw [e, equivChar_ofU] at *
      exact (ofU_spec hL T h hu).2
    tw := fun π χ => CGu.equivChar_tw π.1 χ.1
    infG := fun π a ha g => by
      obtain ⟨χ, h, e⟩ := exists_ofU π.1
      change (CGu.equivChar D.host.E π.1).1.HasInfQ (embPsi D.host) a at ha
      change π.1.1.infChar (embPsi D.host g) = {(a g : ℂ)} ∧
        π.1.1.infChar ((starRingEnd ℂ).comp (embPsi D.host g)) = {-(a g : ℂ)}
      rw [e, equivChar_ofU] at *
      exact infChar_ofChar_of_hasInfQ D.host χ a ha g
    csd := fun π => by
      obtain ⟨χ, h, e⟩ := exists_ofU π.1
      change π.1.1.IsCsd ↔ IsCSD D.host (CGu.equivChar D.host.E π.1).1
      rw [e, equivChar_ofU]
      exact isCsd_ofChar_iff D.host χ
    etaT := equivChar_ofU _ cf.isEta.unitary
    etaTinv := equivChar_ofU _ cf.isEta.unitary.inv
    plGw := hP }

end Main

end GlobalTheory.HeightCounting.TrueSide

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial

theorem exists_cgTrue_charSide : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (D : D7)
    (hE : IsEmpty D.nd.Loc) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (cf : CharFrame D), (∀ k v, cf.P.Div k (D.naut.plGw k v)) →
    ∃ K : CGK D.naut, Nonempty (CGTrue hL (setCG D hE K) (wdCG hE K T)) ∧ Nonempty (CharSide (setCG D hE K) (cfCG hE K cf)) :=
  fun hL hF D hE T cf hP =>
    ⟨TrueSide.trueK hL hF T cf.isEta, ⟨TrueSide.trueCG hL hF T hE cf.isEta⟩, ⟨TrueSide.trueSide hL hF T hE cf hP⟩⟩

end GlobalTheory.HeightCounting

end
