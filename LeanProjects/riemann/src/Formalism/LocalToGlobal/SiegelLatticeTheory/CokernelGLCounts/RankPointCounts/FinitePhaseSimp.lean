import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PhaseLiftCell
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.UnitriangularPhases
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealFramesCharacters
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.CharacterFixedPoints
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ActFrame
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictK
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiTrivOut

noncomputable section

open scoped Classical ComplexConjugate

namespace Formalism.L2.SG.Pf.FinitePhaseConjugation

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.TermOp.Vanish Formalism.L2.SG.PairVal
open Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Conj

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem nlam_conj2 {Λ Λ' : Submodule (𝓞 E) S.V} {T₁ T₂ : E} {F₁ : LFlag S r T₁} {F₂ : LFlag S r T₂}
    {γ m : S.V ≃ₗ[E] S.V} (hiso : ∀ x y, S.hT (γ x) (γ y) = S.hT x y) (hΛ : ∀ x, γ x ∈ Λ ↔ x ∈ Λ')
    (hF : ∀ a, frame F₁ a = γ (frame F₂ a)) (hm : m ∈ NLam Λ F₁) : γ⁻¹ * m * γ ∈ NLam Λ' F₂ := by
  have hmA := (Formalism.L2.SG.Pf.isAutLam_iff Λ m).1 hm.1
  have hgi : ∀ y, γ (γ⁻¹ y) = y := fun y => by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
  have hig : ∀ y, γ⁻¹ (γ y) = y := fun y => by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
  have hiso' : ∀ x y, S.hT (γ⁻¹ x) (γ⁻¹ y) = S.hT x y := fun x y => by
    rw [← hiso, hgi, hgi]
  have hF' : ∀ a, frame F₂ a = γ⁻¹ (frame F₁ a) := fun a => by rw [hF, hig]
  have hsymm : ∀ y, (γ⁻¹).symm y = γ y := fun y => by
    apply (γ⁻¹).injective
    rw [LinearEquiv.apply_symm_apply, hig]
  have e : ∀ x, (γ⁻¹).symm ((γ⁻¹ * m * γ) x - x) = m ((γ⁻¹).symm x) - (γ⁻¹).symm x := fun x => by
    rw [hsymm, hsymm, map_sub, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hgi]
  refine ⟨(Formalism.L2.SG.Pf.isAutLam_iff Λ' _).2 ⟨fun x y => ?_, fun x => ?_⟩, ?_, ?_⟩
  · simp only [LinearEquiv.mul_apply]
    rw [hiso', hmA.1, hiso]
  · simp only [LinearEquiv.mul_apply]
    rw [← hΛ, hgi, hmA.2, hΛ]
  · intro j x hx
    rw [Formalism.L2.SG.Pf.mem_xflag_of_frame hF'] at hx ⊢
    rw [e]
    exact hm.2.1 j _ hx
  · intro x hx
    rw [Formalism.L2.SG.Pf.mem_orth_of_frame hF' hiso'] at hx
    rw [Formalism.L2.SG.Pf.mem_xsp_of_frame hF', e]
    exact hm.2.2 _ hx

end Conj

theorem psiInfU_inv {D : D7} (X : HidaSetting D) (u : D.what₂.Word) {s : X.B.I.Ginf} (hs : s ∈ X.NinfU u) :
    X.psiInfU u s⁻¹ = (X.psiInfU u s)⁻¹ := by
  obtain ⟨h1, hmul, hinv⟩ := Formalism.L2.SG.Pf.psiInfChar_holds D X u
  have hone : X.psiInfU u 1 = 1 := by
    have h := (hmul 1 h1 1 h1).2
    rw [mul_one] at h
    have hn : X.psiInfU u 1 ≠ 0 := by
      intro h0; have := psiInfU_norm X u 1; rw [h0, norm_zero] at this; exact zero_ne_one this
    exact (mul_right_eq_self₀.1 h.symm).resolve_right hn
  have h := (hmul s hs s⁻¹ (hinv s hs)).2
  rw [mul_inv_cancel, hone] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem psiInf_star {D : D7} (g : ℕ) (x : D.host.E) :
    Formalism.L2.SG.PairVal.psiInf g (star x) = Formalism.L2.SG.PairVal.psiInf g x := by
  let e : D.host.E ≃ₐ[ℚ] D.host.E := AlgEquiv.ofRingEquiv (f := (starRingAut : D.host.E ≃+* D.host.E))
    (fun q => by rw [eq_ratCast (algebraMap ℚ D.host.E) q]; exact map_ratCast _ q)
  have ht : Algebra.trace ℚ D.host.E (star x) = Algebra.trace ℚ D.host.E x := Algebra.trace_eq_of_algEquiv e x
  unfold Formalism.L2.SG.PairVal.psiInf
  rw [ht]

section Main

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

set_option maxHeartbeats 1600000 in

theorem finPhaseC_of (hNR : Formalism.L2.SG.PairVal.NormRepExists D u u' (X.Fu u) (Y.what₂ u))
    (h1 : Formalism.L2.SG.Pf.RowForm.LiftAtSomeC X Y u u' κ) : Formalism.L2.SG.Pf.FinitePhase.FinPhaseC X Y u u' κ := by
  intro R ρ s hrel L U hL hU hZ
  have hgS : X.B.g = gS D := X.g_eq

  have hat : s.1.toTerm.atPt (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) :=
    Formalism.L2.SG.PairVal.ptOf_spec _ ⟨(h1 R ρ s hrel).choose, (h1 R ρ s hrel).choose_spec, hrel⟩
  have hex := hNR s.1.toTerm (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) hat hrel s.2.2.1
  unfold Formalism.L2.SG.PairVal.phaseAt
  rw [dif_pos hex]
  obtain ⟨⟨hP'', hmk''⟩, hAdm'', hL'', hU'', hZ''⟩ := hex.choose_spec

  have hrow := (Y.rowsOK u).1 s.1.lam s.1.mem
  have hmk : mk s.1.lam (lf D (X.Fu u)) (PD D s.1.lam (lf D (X.Fu u)) u') ⟨s.1.frame, s.1.rep.2.2.2.2⟩ =
      mk s.1.lam (lf D (X.Fu u)) (PD D s.1.lam (lf D (X.Fu u)) u') ⟨hex.choose.1, hP''⟩ := hmk''.symm
  obtain ⟨n, hn, m, hm, hfr, -⟩ := (Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) s.1.lam hrow _ _).1 hmk

  obtain ⟨vn, um, hvn, hum, hvnF, humF, hsum⟩ := Formalism.L2.SG.Pf.UnitriangularPhases.phase_move s.1.lam (lf D (X.Fu u)) s.1.frame
    hex.choose.1 hn hm hfr _ hL hU hL'' hU'' hZ hZ''

  have hRL : RatLink X s.1.pt s.1.rep.1.2 := s.1.rep.2.1
  have hiso : s.1.rep.1.2 ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.1.rep.2.2.1
  have hmap : Formalism.HermitianLatticesTheory.gmap s.1.rep.1.2 s.1.lam' = s.1.lam := s.1.rep.2.2.2.1
  set γ := s.1.rep.1.2 with hγ
  have hframe : ∀ b, frame s.1.frame b = γ (frame (lf D (X.Fu u')) b) := fun b =>
    Formalism.L2.SG.Pf.Act.frame_mapLF hiso (X.Fu u') b
  have hΛ : ∀ y, γ y ∈ s.1.lam ↔ y ∈ s.1.lam' := fun y => by
    rw [← hmap]
    constructor
    · rintro ⟨z, hz, hzy⟩
      rwa [γ.injective hzy] at hz
    · intro h; exact ⟨y, h, rfl⟩
  have hgi : ∀ y, γ (γ⁻¹ y) = y := fun y => by rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
  have hig : ∀ y, γ⁻¹ (γ y) = y := fun y => by rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
  have hm' : γ⁻¹ * m * γ ∈ NLam s.1.lam' (lf D (X.Fu u')) := nlam_conj2 (fun x y => hiso x y) hΛ hframe hm
  have hm'F : ∀ b, (γ⁻¹ * m * γ) ((X.Fu u').fvec b) = ∑ c, um c b • (X.Fu u').fvec c := by
    intro b
    have h := humF b
    simp only [hframe] at h
    simp only [LinearEquiv.mul_apply]
    rw [show (X.Fu u').fvec b = frame (lf D (X.Fu u')) b from rfl, h, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, hig]

  obtain ⟨xn, hxn⟩ := Formalism.L2.SG.Pf.ratPt_holds D X n hn.1.1
  obtain ⟨xm, hxm⟩ := Formalism.L2.SG.Pf.ratPt_holds D X (γ⁻¹ * m * γ) hm'.1.1
  have hψn : X.psiInfU u xn⁻¹.1 = Formalism.L2.SG.PairVal.psiInf X.B.g (Formalism.L2.SG.PairVal.sgUp vn) :=
    Formalism.L2.SG.RealObj.RealFramesCharacters.psiInf_rat X u (ratLink_inv X hxn) vn hvnF
  have hψm : X.psiInfU u' xm.1 = Formalism.L2.SG.PairVal.psiInf X.B.g (Formalism.L2.SG.PairVal.sgUp um) :=
    Formalism.L2.SG.RealObj.RealFramesCharacters.psiInf_rat X u' hxm um hm'F
  have hnI : xn.1 ∈ X.NinfU u := Formalism.L2.SG.Pf.nLamNinf_holds D X u s.1.lam xn n hxn hn
  have hnF : xn.2 ∈ X.NfinU u := Formalism.L2.SG.Pf.nLamNfin_holds D X u s.1.lam xn n hxn hn
  have hmI : xm.1 ∈ X.NinfU u' := Formalism.L2.SG.Pf.nLamNinf_holds D X u' s.1.lam' xm _ hxm hm'
  have hmF : xm.2 ∈ X.NfinU u' := Formalism.L2.SG.Pf.nLamNfin_holds D X u' s.1.lam' xm _ hxm hm'
  have hPn := Formalism.L2.SG.Pf.psiProd_all D X u xn (ratLink_mem X hxn) hnI hnF
  have hPm := Formalism.L2.SG.Pf.psiProd_all D X u' xm (ratLink_mem X hxm) hmI hmF
  have hinvn : X.psiInfU u xn⁻¹.1 = (X.psiInfU u xn.1)⁻¹ := by rw [Prod.fst_inv]; exact psiInfU_inv X u hnI

  have hbl : (Y.cs u).lamOf ((Y.cs u).base s.1.lam) = s.1.lam := (Y.cs u).base_lam _ s.1.mem
  have hbl' : (Y.cs u').lamOf ((Y.cs u').base s.1.lam') = s.1.lam' := (Y.cs u').base_lam _ s.1.mem'
  obtain ⟨hC1, -, hC1c⟩ := Formalism.L2.SG.Pf.nilradical_conj_level' D X Y u ((Y.cs u).base s.1.lam) xn n (by rw [hbl]; exact hn) hxn
  obtain ⟨hC2, -, hC2c⟩ :=
    Formalism.L2.SG.Pf.nilradical_conj_level' D X Y u' ((Y.cs u').base s.1.lam') xm _ (by rw [hbl']; exact hm') hxm
  have hχ1 : chiN X ((((Y.cs u).h ((Y.cs u).base s.1.lam) : X.B.I.Gf) * X.xu u)⁻¹ * xn.2 * (((Y.cs u).h ((Y.cs u).base s.1.lam) : X.B.I.Gf) * X.xu u)) = X.psiFinU u xn.2 := by
    have := (hC1c 1 Y.hK.1).1
    rwa [mul_one, Formalism.L2.SG.Pf.ChiNHomPf.chiN_one, mul_one] at this
  have hχ2 : chiN X ((((Y.cs u').h ((Y.cs u').base s.1.lam') : X.B.I.Gf) * X.xu u')⁻¹ * xm.2 * (((Y.cs u').h ((Y.cs u').base s.1.lam') : X.B.I.Gf) * X.xu u')) = X.psiFinU u' xm.2 := by
    have := (hC2c 1 Y.hK.1).2
    rwa [one_mul, Formalism.L2.SG.Pf.ChiNHomPf.chiN_one, one_mul] at this
  have hN1 := Formalism.L2.SG.Pf.ChiNHomPf.level_subgroup_norm_congruence X hC1
  have hN2 := Formalism.L2.SG.Pf.ChiNHomPf.level_subgroup_norm_congruence X hC2
  have hκK := Formalism.L2.SG.NormCut.termK_car (Y.cs u) (Y.cs u') s.1.mem s.1.mem' s.1.rep
  have hκN := Formalism.L2.SG.NormCut.adm_norm_of_carrier (Y.cs u) (Y.cs u') (Formalism.L2.SG.Full.Full.frameTie (X := X) u u')
    (Formalism.L2.SG.Pf.modGAt X) s.1.mem s.1.mem' s.1.rep hκK

  have hRL'' : RatLink X (xn * s.1.rep.1.1 * xm) (n * γ * (γ⁻¹ * m * γ)) := ratLink_mul X (ratLink_mul X hxn hRL) hxm
  have hκ'' : kOf X u u' ((Y.cs u).h ((Y.cs u).base s.1.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base s.1.lam') : X.B.I.Gf)
      (xn * s.1.rep.1.1 * xm) = ((((Y.cs u).h ((Y.cs u).base s.1.lam) : X.B.I.Gf) * X.xu u)⁻¹ * xn.2 * (((Y.cs u).h ((Y.cs u).base s.1.lam) : X.B.I.Gf) * X.xu u)) * (kOf X u u' ((Y.cs u).h ((Y.cs u).base s.1.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base s.1.lam') : X.B.I.Gf) s.1.rep.1.1) * ((((Y.cs u').h ((Y.cs u').base s.1.lam') : X.B.I.Gf) * X.xu u')⁻¹ * xm.2 * (((Y.cs u').h ((Y.cs u').base s.1.lam') : X.B.I.Gf) * X.xu u')) := by
    simp only [kOf, Prod.snd_mul]
    group
  have hK'' : kOf X u u' ((Y.cs u).h ((Y.cs u).base s.1.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base s.1.lam') : X.B.I.Gf)
      (xn * s.1.rep.1.1 * xm) ∈ X.B.I.Kset := by
    rw [hκ'']
    exact Formalism.L2.SG.Pf.unitaryCongruence.K_mul X.B.I (Formalism.L2.SG.Pf.unitaryCongruence.K_mul X.B.I hN1.1 hκK) hN2.1
  have hξm : ∀ c, ModG (VS D) s.1.lam (gS D) ((n * γ * (γ⁻¹ * m * γ)) (frame (lf D (X.Fu u')) c) -
      frameAct (frame (lf D (X.Fu u))) 1 c) := by
    intro c
    have e : (n * γ * (γ⁻¹ * m * γ)) (frame (lf D (X.Fu u')) c) = frame hex.choose.1 c := by
      rw [hfr, hframe]
      simp only [LinearEquiv.mul_apply, hgi]
    rw [e]
    exact hAdm''.2.2 c
  have hkey := Formalism.L2.SG.NormCut.key_gen (Y.cs u) (Y.cs u') (Formalism.L2.SG.Full.Full.frameTie (X := X) u u')
    (Formalism.L2.SG.Pf.modGAt X) s.1.mem (xn * s.1.rep.1.1 * xm) _ hRL'' 1 hξm hK''
  have hfix : ∀ a : Fin D.R.rS, (X.B.I.fmat (kOf X u u' ((Y.cs u).h ((Y.cs u).base s.1.lam) : X.B.I.Gf)
      ((Y.cs u').h ((Y.cs u').base s.1.lam') : X.B.I.Gf) (xn * s.1.rep.1.1 * xm)) - 1) *ᵥ nxt X.e0 X.z0 a ∈
      mL X.B.I X.B.g := by
    intro a
    have h := hkey a.succ
    have hs : ∑ b, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)
        (X.ιE.symm (((1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) b a.succ : 𝓞 D.host.E) : D.host.E)) •
        Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 b =
        Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 a.succ := by
      rw [Finset.sum_eq_single a.succ]
      · simp
      · intro b _ hb; simp [Matrix.one_apply_ne hb]
      · simp
    rw [hs] at h
    have hnxt : nxt X.e0 X.z0 a = Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 a.succ := by
      unfold nxt
      split_ifs with hh
      · have : a.succ = Fin.castSucc ⟨a.1 + 1, hh⟩ := Fin.ext (by simp)
        rw [this, Fin.snoc_castSucc]
      · have : a.succ = Fin.last D.R.rS := Fin.ext (by simp; omega)
        rw [this, Fin.snoc_last]
    rw [hnxt, Matrix.sub_mulVec, Matrix.one_mulVec]
    exact h
  have h1'' := Formalism.L2.SG.Pf.CharacterOnFixedPoints.chiN_of_fix X hfix
  rw [hκ'', Formalism.L2.SG.Pf.ChiNHomPf.chiN_mul X (Formalism.L2.SG.Pf.unitaryCongruence.K_mul X.B.I hN1.1 hκK)
    (Formalism.L2.SG.NormCut.ncong_mul X hN1.1 hN1.2 hκN) hN2.2, Formalism.L2.SG.Pf.ChiNHomPf.chiN_mul X hN1.1 hN1.2 hκN,
    hχ1, hχ2] at h1''

  rw [hgS] at hψn hψm
  have hf1 : X.psiFinU u xn.2 ≠ 0 := right_ne_zero_of_mul_eq_one hPn
  have hf2 : X.psiFinU u' xm.2 ≠ 0 := right_ne_zero_of_mul_eq_one hPm
  have hi1 : X.psiInfU u xn.1 = (X.psiFinU u xn.2)⁻¹ := eq_inv_of_mul_eq_one_left hPn
  have hi2 : X.psiInfU u' xm.1 = (X.psiFinU u' xm.2)⁻¹ := eq_inv_of_mul_eq_one_left hPm
  have ha : Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp vn) = X.psiFinU u xn.2 := by
    rw [← hψn, hinvn, hi1, inv_inv]
  have hc : Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp um) = (X.psiFinU u' xm.2)⁻¹ := by
    rw [← hψm, hi2]
  have hR : Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgLo hex.choose.2.1 + Formalism.L2.SG.PairVal.sgUp hex.choose.2.2) =
      Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgLo L + Formalism.L2.SG.PairVal.sgUp U) *
        Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp vn) *
        (Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp um))⁻¹ := by
    rw [hsum, sub_eq_add_neg, Formalism.L2.SG.Pf.psiInf_add, Formalism.L2.SG.Pf.psiInf_add, Formalism.L2.SG.RealObj.FormRegularity.psiInf_neg,
      psiInf_star]
  rw [Formalism.L2.SG.Pf.phasePair_eq, Formalism.L2.SG.Pf.phasePair_eq, hR, ha, hc, inv_inv]
  have hP0 : Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgLo L + Formalism.L2.SG.PairVal.sgUp U) ≠ 0 :=
    Complex.exp_ne_zero _
  have hpt : s.1.pt = s.1.rep.1.1 := rfl
  rw [hpt]
  field_simp
  linear_combination h1''

end Main

end Formalism.L2.SG.Pf.FinitePhaseConjugation
