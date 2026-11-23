import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefPhase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefPh
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOrb

noncomputable section

namespace Formalism.L2.SG.Pf.LocOrbCut

open MeasureTheory Formalism.MainNotions.S Formalism.L2.SG.Pf.LocOrbSumPf
open Classical

section Dec

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] [IsTopologicalRing E]

theorem sg_dec_eq {m : ℕ} (a : Loc.Pt E (m + 1)) (l ρ l' ρ' : Matrix (Fin (m + 1)) (Fin (m + 1)) E)
    (hl : Formalism.DoubleCosetMeasures.IsLowUni l) (hρ : Formalism.DoubleCosetMeasures.IsUpUni ρ) (hl' : Formalism.DoubleCosetMeasures.IsLowUni l') (hρ' : Formalism.DoubleCosetMeasures.IsUpUni ρ')
    (h : l' * a.mat * ρ' = l * a.mat * ρ) :
    Loc.simpleLow l' + Loc.simpleUp ρ' = Loc.simpleLow l + Loc.simpleUp ρ := by
  have hLo : Formalism.DoubleCosetMeasures.IsLowUni (rI a l) := lowUni_rI a hl
  have hUp : Formalism.DoubleCosetMeasures.IsUpUni (rI a ρ) := upUni_rI a hρ
  have hv : Formalism.DoubleCosetMeasures.IsLowUni (rI a l') := lowUni_rI a hl'
  have hu : Formalism.DoubleCosetMeasures.IsUpUni (rI a ρ') := upUni_rI a hρ'
  have hvPu : rI a l' * Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 * rI a ρ' =
      rI a l * Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 * rI a ρ := by
    have h' := congrArg (rI a) h
    simp only [rI_mul, rI_mat] at h'
    exact h'
  have hLd : IsUnit (rI a l).det := by rw [Formalism.DoubleCosetMeasures.isLowUni_det E hLo]; exact isUnit_one
  have hUd : IsUnit (rI a ρ).det := by rw [Formalism.DoubleCosetMeasures.isUpUni_det E hUp]; exact isUnit_one
  have hfix : ((rI a l)⁻¹ * rI a l') * Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
      (rI a ρ' * (rI a ρ)⁻¹) = Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 := by
    calc _ = (rI a l)⁻¹ * (rI a l' * Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 * rI a ρ') *
          (rI a ρ)⁻¹ := by simp only [Matrix.mul_assoc]
      _ = ((rI a l)⁻¹ * rI a l) * Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
          (rI a ρ * (rI a ρ)⁻¹) := by rw [hvPu]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.nonsing_inv_mul _ hLd, Matrix.mul_nonsing_inv _ hUd, Matrix.one_mul, Matrix.mul_one]
  have h0 := Formalism.DoubleCosetMeasures.Final.phaseWellDef E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 _ _
    (Formalism.DoubleCosetMeasures.isLowUni_mul E (Formalism.DoubleCosetMeasures.isLowUni_inv E hLo) hv) (Formalism.DoubleCosetMeasures.isUpUni_mul E hu (Formalism.DoubleCosetMeasures.isUpUni_inv E hUp)) hfix
  have sa := Formalism.DoubleCosetMeasures.Final.simpleAdd E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum
  rw [(sa _ _).1 (Formalism.DoubleCosetMeasures.isLowUni_inv E hLo) hv, (sa _ _).2 hu (Formalism.DoubleCosetMeasures.isUpUni_inv E hUp)] at h0
  have hLi := (sa (rI a l)⁻¹ (rI a l)).1 (Formalism.DoubleCosetMeasures.isLowUni_inv E hLo) hLo
  rw [Matrix.nonsing_inv_mul _ hLd, sLow_one] at hLi
  have hUi := (sa (rI a ρ) (rI a ρ)⁻¹).2 hUp (Formalism.DoubleCosetMeasures.isUpUni_inv E hUp)
  rw [Matrix.mul_nonsing_inv _ hUd, sUp_one] at hUi
  rw [Formalism.MainNotions.LocalOrbitGerms.Cls.simpleLow_eq, Formalism.MainNotions.LocalOrbitGerms.Cls.simpleUp_eq, Formalism.MainNotions.LocalOrbitGerms.Cls.simpleLow_eq,
    Formalism.MainNotions.LocalOrbitGerms.Cls.simpleUp_eq, ← sLow_rI a l', ← sUp_rI a ρ', ← sLow_rI a l, ← sUp_rI a ρ]
  linear_combination h0 + hLi + hUi

end Dec

end Formalism.L2.SG.Pf.LocOrbCut

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.LocOrbSumPf Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Simple

variable {K : Type} [CommRing K] {n : ℕ}

theorem sLow_conj (A : Matrix (Fin n) (Fin n) K) (d d' : Fin n → K) (c : K)
    (hc : ∀ (j : Fin n) (h : j.val + 1 < n), d ⟨j.val + 1, h⟩ * d' j = c) :
    Formalism.DoubleCosetMeasures.sLow (Matrix.diagonal d * A * Matrix.diagonal d') = c * Formalism.DoubleCosetMeasures.sLow A := by
  unfold Formalism.DoubleCosetMeasures.sLow
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [Matrix.mul_diagonal, Matrix.diagonal_mul, ← hc j h]
    ring
  · rw [mul_zero]

theorem sUp_conj (A : Matrix (Fin n) (Fin n) K) (d d' : Fin n → K) (c : K)
    (hc : ∀ (j : Fin n) (h : j.val + 1 < n), d' j * d ⟨j.val + 1, h⟩ = c) :
    Formalism.DoubleCosetMeasures.sUp (Matrix.diagonal d' * A * Matrix.diagonal d) = c * Formalism.DoubleCosetMeasures.sUp A := by
  unfold Formalism.DoubleCosetMeasures.sUp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [Matrix.mul_diagonal, Matrix.diagonal_mul, ← hc j h]
    ring
  · rw [mul_zero]

theorem sLow_map {S : Type} [CommRing S] (f : K →+* S) (A : Matrix (Fin n) (Fin n) K) :
    Formalism.DoubleCosetMeasures.sLow (A.map f) = f (Formalism.DoubleCosetMeasures.sLow A) := by
  unfold Formalism.DoubleCosetMeasures.sLow
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem sUp_map {S : Type} [CommRing S] (f : K →+* S) (A : Matrix (Fin n) (Fin n) K) :
    Formalism.DoubleCosetMeasures.sUp (A.map f) = f (Formalism.DoubleCosetMeasures.sUp A) := by
  unfold Formalism.DoubleCosetMeasures.sUp
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem sgLo_eq {K' : Type} [Field K'] (A : Matrix (Fin n) (Fin n) K') : PairVal.sgLo A = Formalism.DoubleCosetMeasures.sLow A := rfl

theorem sgUp_eq {K' : Type} [Field K'] (A : Matrix (Fin n) (Fin n) K') : PairVal.sgUp A = Formalism.DoubleCosetMeasures.sUp A := rfl

theorem lowUni_of_isLo {A : Matrix (Fin n) (Fin n) K} (h : IsLo A) : Formalism.DoubleCosetMeasures.IsLowUni A :=
  ⟨fun i j hij => h.2 i j hij, h.1⟩

theorem upUni_of_isUp {A : Matrix (Fin n) (Fin n) K} (h : IsUp A) : Formalism.DoubleCosetMeasures.IsUpUni A :=
  ⟨fun i j hij => h.2 j i hij, h.1⟩

end Simple

section Dec

variable {D : Formalism.BasicNotions.D7}

theorem phL_of_dec (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {w₀ : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)}
    (hOK : (M p).OK) (hw₀ : modPt δ T T' p w = some w₀) {Y l ρ : MatP D p} (hl : IsLo l) (hρ : IsUp ρ)
    (hY : Y = l * modMat δ T T' p w * ρ) :
    phL M δ T T' p w Y = dfac M δ T T' p w * (M p).psiR (Loc.simpleLow l + Loc.simpleUp ρ) := by
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) hOK
  have hO : InOrbP δ T T' p w Y := PCount.inOrbP_of_orb hw₀
    ⟨l, ρ, fun a => ⟨hl.1 a, hρ.1 a⟩, fun a b hab => ⟨hl.2 a b hab, hρ.2 a b hab⟩, hY⟩
  obtain ⟨w₁, hw₁, hex⟩ := hO
  rw [hw₀] at hw₁
  obtain rfl := Option.some.inj hw₁
  unfold phL
  rw [hw₀]
  try dsimp only
  rw [dif_pos hex]
  congr 2
  have hmat := modShift_holds δ T T' p w w₀ hw₀
  have e1 := zAt_eq hmat hex.choose
  rw [← hex.choose_spec] at e1
  have e2 : l * w₀.mat * ρ = Y + shM δ T T' p w := by
    rw [hmat, mul_add, add_mul, mul_shM l ρ (last_of_low l hl.1 hl.2) (last_of_up ρ hρ.1 (fun a b h => hρ.2 b a h)), hY]
  unfold zAt at e1
  exact LocOrbCut.sg_dec_eq w₀ l ρ _ _ (lowUni_of_isLo hl) (upUni_of_isUp hρ)
    (LocOrbCut.uLow_lowUni hex.choose.1) (LocOrbCut.uUp_upUni w₀ hex.choose.2) (e1.trans e2.symm)

end Dec

section ModeL

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem cf_mul_cfi (Zd : LocDat D) (p : PlF D) (a b : Fin (D.R.rS + 1)) (h : a.val = b.val + 1) :
    cf Zd p a * cfi Zd p b = yP Zd p := by
  unfold cf cfi
  have hb : D.R.rS - b.val = (D.R.rS - a.val) + 1 := by have := a.2; omega
  rw [hb, pow_succ, inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (yP_ne Zd p)), one_mul]

theorem phaseLoc_L (hA : ∀ p, Agree δ M p) {γ : TermDef.Term D u u' F0 what₂} {w : Point D.host.E (D.R.rS + 1)}
    {F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {L U : PairVal.MatR D} (hN : PairVal.NormRep γ w F' L U)
    (p : PlF D) (hM : (M p).split = none) :
    phL M δ (D.mem u).A.T (D.mem u').A.T p w (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p) =
      (D.s.atP p).psiE ((D.s.atP p).ιE (-((PairVal.sgLo L + PairVal.sgUp U) / ((gS D : ℕ) : D.host.E)))) := by
  obtain ⟨-, -, hL, hU, e⟩ := hN
  have hL' := PCount.isLo_of_uni hL
  have hU' := PCount.isUp_of_uni hU
  have hf' : ZhatL (lf D F0) F' * Sg D.host.E D.R.rS = L * ptMat w * U := by rw [← zhatOM_eq]; exact e
  have hAg := (hA p).2.2.2.2.2
  have hR : (D.s.atP p).split = none := by
    rcases hR : (D.s.atP p).split with _ | sg
    · rfl
    · simp only [hM, hR] at hAg
  have hfr : ∀ a, algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi ⟨δ, M, hA⟩ p a) *
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf ⟨δ, M, hA⟩ p a) = 1 := fun a => by
    rw [← map_mul, cfi_cf, map_one]
  have hfr' : ∀ a, algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf ⟨δ, M, hA⟩ p a) *
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi ⟨δ, M, hA⟩ p a) = 1 := fun a => by
    rw [← map_mul, cf_cfi, map_one]
  have hmod : Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf ⟨δ, M, hA⟩ p a)) *
      (ptMat w).map (D.s.atP p).ιE *
      Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf ⟨δ, M, hA⟩ p a)) =
      modMat δ (D.mem u).A.T (D.mem u').A.T p w := by
    ext a b
    rw [modMat_apply', Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply']
    by_cases hb : b = sgF w a
    · rw [if_pos hb, if_pos hb, modMat_blk ⟨δ, M, hA⟩]
      simp only [twist, qE, tau0, hR, Ring.inverse_one, mul_one, ite_self, sub_zero, map_mul]
      subst hb
      ring
    · rw [if_neg hb, if_neg hb, map_zero, mul_zero, zero_mul]
  have h1 := PCount.zzp_sgn_ord ⟨δ, M, hA⟩ u u' p hM (ZhatL (lf D F0) F')
  have hdec : CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p =
      (Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf ⟨δ, M, hA⟩ p a)) *
        L.map (D.s.atP p).ιE *
        Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi ⟨δ, M, hA⟩ p a))) *
      modMat δ (D.mem u).A.T (D.mem u').A.T p w *
      (Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi ⟨δ, M, hA⟩ p a)) *
        U.map (D.s.atP p).ιE *
        Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf ⟨δ, M, hA⟩ p a))) := by
    refine h1.trans ?_
    rw [hf', Matrix.map_mul, Matrix.map_mul, regroup _ _ hfr, hmod]
  obtain ⟨w₀, hw₀⟩ := PCount.modPt_full (δ := δ) (D.mem u).A.T (D.mem u').A.T p (hA p).2.1 w
  rw [phL_of_dec M δ (hA p).1 hw₀ (isLo_conj (isLo_map (D.s.atP p).ιE hL') _ _ hfr')
    (isUp_conj (isUp_map (D.s.atP p).ιE hU') _ _ hfr) hdec]
  have hd : dfac M δ (D.mem u).A.T (D.mem u').A.T p w = 1 := by
    unfold dfac
    rw [hR]
  rw [hd, one_mul, Formalism.MainNotions.LocalOrbitGerms.Cls.simpleLow_eq, Formalism.MainNotions.LocalOrbitGerms.Cls.simpleUp_eq,
    sLow_conj _ _ _ (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (yP ⟨δ, M, hA⟩ p))
      (fun j h => by rw [← map_mul, cf_mul_cfi ⟨δ, M, hA⟩ p ⟨j.val + 1, h⟩ j rfl]),
    sUp_conj _ _ _ (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (yP ⟨δ, M, hA⟩ p))
      (fun j h => by rw [← map_mul, mul_comm, cf_mul_cfi ⟨δ, M, hA⟩ p ⟨j.val + 1, h⟩ j rfl]),
    sLow_map, sUp_map]
  unfold Loc.Model.psiR
  rw [hM]
  try dsimp only
  rw [(hA p).2.2.2.2.1]
  congr 1

  have hres : Loc.resChar p ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by
    intro hmem
    have := (D.s_split p).2 hmem
    rw [hR] at this
    exact absurd this (by simp)
  have hg0 : Loc.resChar p ≠ D.host.g 0 := fun h => hres (by simp [h])
  have hg1 : Loc.resChar p ≠ D.host.g 1 := fun h => hres (by simp [h])
  have hgp : gpart p = 1 := by unfold gpart; rw [if_neg hg0, if_neg hg1]
  have hδ : δ p ≠ 0 := (hA p).2.1
  have hu : (D.s.atP p).ιE ((uP p : ℚ) : D.host.E) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF ((uP p : ℚ) : D.host.F)) := by
    rw [← (D.s.atP p).compat, map_ratCast (algebraMap D.host.F D.host.E)]
  have hyP : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (yP ⟨δ, M, hA⟩ p) *
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ = (D.s.atP p).ιE ((uP p : ℚ) : D.host.E) := by
    rw [hu, ← map_mul]
    unfold yP
    congr 1
    field_simp
  have hup : ((uP p : ℚ) : D.host.E) = 1 / ((gS D : ℕ) : D.host.E) := by
    unfold uP
    rw [hgp]
    push_cast
    ring
  have key : (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (yP ⟨δ, M, hA⟩ p) *
        (D.s.atP p).ιE (Formalism.DoubleCosetMeasures.sLow L) +
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (yP ⟨δ, M, hA⟩ p) * (D.s.atP p).ιE (Formalism.DoubleCosetMeasures.sUp U)) *
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ =
      (D.s.atP p).ιE ((Formalism.DoubleCosetMeasures.sLow L + Formalism.DoubleCosetMeasures.sUp U) / ((gS D : ℕ) : D.host.E)) := by
    rw [div_eq_mul_one_div, ← hup, map_mul, map_add, ← hyP]
    ring
  simp only [sgLo_eq, sgUp_eq, map_neg]
  exact congrArg Neg.neg key

section Steps

variable (M δ u u' F0 what₂) in

def PhaseLocG : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : PairVal.MatR D),
    γ.relevant → γ.generic → PairVal.NormRep γ w F' L U → ∀ p : PlF D, (M p).split ≠ none →
    phL M δ (D.mem u).A.T (D.mem u').A.T p w (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p) =
      (D.s.atP p).psiE ((D.s.atP p).ιE (-((PairVal.sgLo L + PairVal.sgUp U) / ((gS D : ℕ) : D.host.E))))

theorem phaseLoc_of (hA : ∀ p, Agree δ M p) (hG : PhaseLocG M δ u u' F0 what₂) : PhaseLoc M δ u u' F0 what₂ := by
  intro γ w F' L U hrel hgen hN p
  by_cases h : (M p).split = none
  · exact phaseLoc_L hA hN p h
  · exact hG γ w F' L U hrel hgen hN p h

end Steps

end ModeL

end Formalism.L2.SG.Pf.Coef
