import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotNonemptyZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LawsT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodToralTwistStable

noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain GlobalTheory.LocGL GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Loc
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem good_loc_ofChar (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) :
    UpperTheory.Zero.LLC.Good (⟨1, ParLaws.toCl ((CG.ofChar χ).loc w)⟩ : IrrGL (w.adicCompletion E)) := by
  have h : (⟨1, ParLaws.toCl ((CG.ofChar χ).loc w)⟩ : IrrGL (w.adicCompletion E)) =
      IrrGL.ofChar (χ.loc w) (ParLaws.isSmoothChar_loc χ w) := ParLawsT.cls_loc_eq_of_isLocComp (CG.isLoc_ofChar χ w)
  rw [h]
  exact ⟨_, hasSupport_self (IrrGL.isCusp_ofChar _ _), fun y hy => Or.inl (by rw [Multiset.mem_singleton.1 hy]; rfl)⟩

theorem cls_loc_twist (π : CG E a) (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) :
    (⟨a, ParLaws.toCl ((π.twist χ).loc w)⟩ : IrrGL (w.adicCompletion E)) =
      IrrGL.tw ⟨a, ParLaws.toCl (π.loc w)⟩ (χ.loc w) (ParLaws.isSmoothChar_loc χ w) := by
  induction π using Quotient.inductionOn with | _ π =>
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL E a π w
  refine (ParLawsT.cls_loc_eq_of_isLocComp (hσ.twist χ)).trans ?_
  rw [show (⟨a, ParLaws.toCl (CG.loc (Quotient.mk _ π) w)⟩ : IrrGL (w.adicCompletion E)) = _ from
    ParLawsT.cls_loc_eq_of_isLocComp hσ]
  exact (IrrGL.tw_of σ.ρ σ.smooth σ.irred _ _).symm

end Loc

section Host
variable {R : Ranks} {H : Formalism.BasicNotions.Host R} {a : ℕ}

theorem goodAll_one (χ : HostCGu H 1) : GoodAll χ := fun w => by
  haveI := host_isCMField H
  have h := good_loc_ofChar χ.1.toChar w
  rwa [CG.ofChar_toChar] at h

theorem goodAll_tw_iff (π : HostCGu H a) (χ : HostCGu H 1) :
    haveI := host_isCMField H; GoodAll (H := H) (π.tw χ) ↔ GoodAll π := by
  haveI := host_isCMField H
  refine forall_congr' fun w => ?_
  have h := cls_loc_twist π.1 χ.1.toChar w
  have h2 := GlobalTheory.RecT.good_tw_iff (⟨a, ParLaws.toCl (π.1.loc w)⟩ : IrrGL (w.adicCompletion H.E)) (χ.1.toChar.loc w)
    (ParLaws.isSmoothChar_loc _ w)
  rw [← h] at h2
  exact h2

end Host

section Char
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsTotallyComplex E]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem locParT_unr (hT : UpperTheory.Zero.LLC.RecTExists) (χ : HChar E) (h : IsPlaceOver A w) (hu : χ.UnrAt w) :
    (ParLawsT.locParT hT (CG.ofChar χ) h).unr ∧
      (ParLawsT.locParT hT (CG.ofChar χ) h).frobEig = {(((χ.val w)⁻¹ : ℂˣ) : ℂ)} := by
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
  obtain ⟨a, ha, H⟩ := ParLawsT.isRecT_locRecT hT h
  have e2 : ParLawsT.locParT hT (CG.ofChar χ) h = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
    rw [ParLawsT.locParT_ofChar_eq, H.one]
    have : ∀ (ξ : (w.adicCompletion E)ˣ →* ℂˣ) (hξ : WeilDeligne.IsSmooth (ξ.comp a)),
        ξ = SmGL.unrChar (w.adicCompletion E) (χ.val w) →
        WD.lpOfChar h (ξ.comp a) hξ = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
      rintro ξ hξ rfl
      exact Test.lpOfChar_unrChar ha _ _
    exact this _ _ e
  rw [e2, WD.frobEig_diag]
  exact ⟨(WD.unr_mk _).2 (WDRep.unr_diag _), by simp⟩

end Char

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

def trueKT (hT : UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
    (η η' : HostCGu D.host 1)
    (h1 : ∀ w, (ParLawsT.locGT hT D.nd.plOm η w).unr)
    (h2 : ∀ w, ¬ IsSplitPl D.host w → (ParLawsT.locGT hT D.nd.plOm η w).frobEig = {-1})
    (h3 : ∀ w, (ParLawsT.locGT hT D.nd.plOm η' w).unr ∧
      (ParLawsT.locGT hT D.nd.plOm η' w).frobEig = (ParLawsT.locGT hT D.nd.plOm η w).frobEig.map (·⁻¹))
    (h4 : ∀ w w', IsSplitPl D.host w → IsConjPl D.host w w' → ∀ a b : ℂ,
      (ParLawsT.locGT hT D.nd.plOm η w).frobEig = {a} →
      (ParLawsT.locGT hT D.nd.plOm η w').frobEig = {b} → a * b = 1) : CGK D.naut :=
  haveI := host_isCMField D.host
  have L := ParLawsT.lawsT hT GlobalTheory.automorphicFormsFiniteGL D.host D.nd.Om D.nd.plOm
  have U : ∀ {a} (π : HostCGu D.host a) w, D.naut.unr ((T.e w).symm (ParLawsT.locGT hT D.nd.plOm π w)) ↔
      (ParLawsT.locGT hT D.nd.plOm π w).unr :=
    fun π w => by rw [T.unr, Equiv.apply_symm_apply]
  have Fr : ∀ {a} (π : HostCGu D.host a) w, (ParLawsT.locGT hT D.nd.plOm π w).unr →
      D.naut.frobEig ((T.e w).symm (ParLawsT.locGT hT D.nd.plOm π w)) = (ParLawsT.locGT hT D.nd.plOm π w).frobEig :=
    fun π w h => by rw [T.frobEig _ _ ((U π w).2 h), Equiv.apply_symm_apply]
  have Dm : ∀ {a} (π : HostCGu D.host a) w, D.naut.lpDim ((T.e w).symm (ParLawsT.locGT hT D.nd.plOm π w)) = a :=
    fun π w => by rw [← T.dim, Equiv.apply_symm_apply]; exact L.1 π w
  { CG := fun a => {π : HostCGu D.host a // 0 < a ∧ GoodAll π}
    csd := fun π => π.1.IsCsd
    ralg := fun π => π.1.IsRegAlg
    locG := fun π w => (T.e w).symm (ParLawsT.locGT hT D.nd.plOm π.1 w)
    locG_dim := fun π w => Dm π.1 w
    locG_unr_ae := fun π => (L.2.1 π.1).mono fun w h => (U π.1 w).2 h
    tw := fun π χ => ⟨π.1.tw χ.1, π.2.1, (goodAll_tw_iff π.1 χ.1).2 π.2.2⟩
    locG_tw := fun π χ w => (T.e w).injective (by
      rw [T.char _ _ _ (Dm χ.1 w), Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact L.2.2.1 π.1 χ.1 w (π.2.2 w))
    infG := fun π τ => π.1.infChar τ
    infG_card := fun π => L.2.2.2.1 π.1
    ralg_def := fun π => L.2.2.2.2.1 π.1
    infG_tw := fun π χ => L.2.2.2.2.2.1 π.1 χ.1
    csd_tw := fun π χ => L.2.2.2.2.2.2.1 π.1 χ.1
    csd_unr := fun π w w' hπ hc hu => by
      have h := L.2.2.2.2.2.2.2.1 π.1 w w' hπ hc ((U π.1 w).1 hu)
      exact ⟨(U π.1 w').2 h.1, by rw [Fr π.1 w' h.1, Fr π.1 w ((U π.1 w).1 hu)]; exact h.2⟩
    etaT := ⟨η, one_pos, goodAll_one η⟩
    etaTinv := ⟨η', one_pos, goodAll_one η'⟩
    etaT_unr := fun w => (U η w).2 (h1 w)
    etaT_inert := fun w h => by rw [Fr η w (h1 w)]; exact h2 w h
    etaTinv_def := fun w => ⟨(U η' w).2 (h3 w).1, by rw [Fr η' w (h3 w).1, Fr η w (h1 w)]; exact (h3 w).2⟩
    etaT_split := fun w w' hs hc a b ha hb => by
      rw [Fr η w (h1 w)] at ha; rw [Fr η w' (h1 w')] at hb; exact h4 w w' hs hc a b ha hb }

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

def trueCGT (hT : UpperTheory.Zero.LLC.RecTExists) (D : D7) (hE : IsEmpty D.nd.Loc) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
    (η η' h1 h2 h3 h4) :
    CGTrueT hT (setCG D hE (trueKT hT D T η η' h1 h2 h3 h4)) (wdCG hE _ T) where
  e := fun _ => Function.Embedding.subtype _
  good := fun _ π => π.2.2
  surj := fun _ h π hπ => ⟨⟨π, h, hπ⟩, rfl⟩
  zero := ⟨fun π => lt_irrefl 0 π.2.1⟩
  loc := fun _ _ w => (T.e w).apply_symm_apply _
  tw := fun _ _ _ => rfl
  inf := fun _ _ _ => rfl
  csd := fun _ _ => Iff.rfl

set_option synthInstance.maxHeartbeats 400000 in

theorem etaLawsT (hT : UpperTheory.Zero.LLC.RecTExists) (D : D7) {χ : HChar D.host.E} (hχ : IsEtaT D.host χ) :
    haveI := host_isCMField D.host
    ∃ η η' : HostCGu D.host 1, η.1 = CG.ofChar χ ∧ η'.1 = CG.ofChar χ⁻¹ ∧
      (∀ w, (ParLawsT.locGT hT D.nd.plOm η w).unr) ∧
      (∀ w, ¬ IsSplitPl D.host w → (ParLawsT.locGT hT D.nd.plOm η w).frobEig = {-1}) ∧
      (∀ w, (ParLawsT.locGT hT D.nd.plOm η' w).unr ∧
        (ParLawsT.locGT hT D.nd.plOm η' w).frobEig = (ParLawsT.locGT hT D.nd.plOm η w).frobEig.map (·⁻¹)) ∧
      (∀ w w', IsSplitPl D.host w → IsConjPl D.host w w' → ∀ a b : ℂ,
        (ParLawsT.locGT hT D.nd.plOm η w).frobEig = {a} →
        (ParLawsT.locGT hT D.nd.plOm η w').frobEig = {b} → a * b = 1) := by
  haveI := host_isCMField D.host
  have hi : (χ⁻¹).IsUnitary := fun x => by
    have := hχ.unitary x
    change ‖(((χ.1 x)⁻¹ : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_inv_eq_inv_val, norm_inv, this, inv_one]
  have hu : ∀ w, (χ⁻¹).UnrAt w := fun w x hx => by rw [HChar.loc_inv, hχ.unr w x hx, inv_one]
  have P := fun w => locParT_unr hT χ (D.nd.plOm.2 w) (hχ.unr w)
  have Q := fun w => locParT_unr hT χ⁻¹ (D.nd.plOm.2 w) (hu w)
  refine ⟨⟨CG.ofChar χ, CG.isUnitary_ofChar hχ.unitary⟩, ⟨CG.ofChar χ⁻¹, CG.isUnitary_ofChar hi⟩, rfl, rfl,
    fun w => (P w).1, fun w hw => (P w).2.trans ?_, fun w => ⟨(Q w).1, (Q w).2.trans ?_⟩,
    fun w w' hw hc a b ha hb => ?_⟩
  · rw [CGTrueModel.val_inert hχ hw]; simp
  · refine Eq.trans ?_ (congrArg (Multiset.map (·⁻¹)) (P w).2).symm
    simp
  · have ha' := (P w).2.symm.trans ha
    have hb' := (P w').2.symm.trans hb
    rw [Multiset.singleton_inj] at ha' hb'
    rw [← ha', ← hb', ← Units.val_mul, ← mul_inv, CGTrueModel.val_split hχ hw hc, inv_one, Units.val_one]

theorem CGTrueT.ralg {hT D T} (C : CGTrueT hT D T) a (π : D.naut.CG a) :
    haveI := host_isCMField D.host; D.naut.ralg π ↔ (C.e a π).IsRegAlg := by
  rw [D.naut.ralg_def]; simp only [C.inf]; exact (GlobalTheory.CuspRep.CG.isRegAlg_iff _).symm

end GlobalTheory.HeightCounting

end
