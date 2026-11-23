import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BesselCompatibility
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondModelFinitePartFrameActionMatrix
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnFormCentralTranslation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColMatch

theorem unitaryAdelicPointFiniteMatrix_inv_eq_of_mul_eq_one {D : D7} (a : GA D (D.sp.X 0)) (M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D))
    (hM : M * GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a = 1) :
    GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ = M := by
  have h1 : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a *
      GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ = 1 := by
    rw [← unitaryAdelicPointFiniteMatrix_base_space_mul, mul_inv_cancel, unitaryAdelicPointFiniteMatrix_base_space_one]
  calc _ = (M * GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a) *
        GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a⁻¹ := by rw [hM, one_mul]
    _ = M := by rw [mul_assoc, h1, mul_one]

theorem col_level_match : ∀ (D : D7) (u : D.what₂.Word) (F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u) (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.Core.Mi.IdE S.X → d.Base → LevX (F₀ u) d h0 → ∀ (B : SBes S.X S.inst u d.c.ψ (D.sp.X 0)), B.lev = d.B 0 D.R.rS h0 → B.Adapted (S.tr u).wt → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (S.tr u) a₀ → ∀ b ∈ GfC (D.sp.X 0), ((d.t 0)⁻¹ * embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o b * d.t 0 ∈ d.lev 0 ↔ ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * b * a₀⁻¹) * ((iotaX S.X S.inst).symm (1, S.X.xu u)) ∈ rowJ S.X S.inst) ∧ ((d.t 0)⁻¹ * embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o b * d.t 0 ∈ d.lev 0 → rowChi S.X S.inst (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * b * a₀⁻¹) * ((iotaX S.X S.inst).symm (1, S.X.xu u))) = levChi (d.st 0).V (d.st 0).β (d.st 0).L ((d.t 0)⁻¹ * embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o b * d.t 0)) := by
  intro D u F₀ S d h0 hE hB hLev B hBl hAd a₀ hH0 b hb
  obtain ⟨y, hy⟩ := GlobalTheory.AdForm.RdVal.finM_mem (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _))
    (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) rfl b
  obtain ⟨hU, hchi⟩ := hLev b hb y hy.symm
  have hgf : a₀ * b * a₀⁻¹ ∈ GfC (D.sp.X 0) := mul_mem (mul_mem hH0.1 hb) (inv_mem hH0.1)
  have hRep := GlobalTheory.Core.Mi.FinFrame.repM_toH D S.X S.inst u d.c.ψ B (F₀ u) (S.tr u) hE hAd (a₀ * b * a₀⁻¹)
  have e0 : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀ =
      ((S.tr u).h0.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) := hH0.2
  have hh0 : (((S.tr u).h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) *
      ((S.tr u).h0.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
  have hfa : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀⁻¹ =
      (((S.tr u).h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) :=
    unitaryAdelicPointFiniteMatrix_inv_eq_of_mul_eq_one a₀ _ (by rw [e0]; exact hh0)
  have hfg : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) (a₀ * b * a₀⁻¹) =
      (((S.tr u).h0 * y * (S.tr u).h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) := by
    refine (unitaryAdelicPointFiniteMatrix_base_space_mul _ _).trans ((congrArg₂ (· * ·) ((unitaryAdelicPointFiniteMatrix_base_space_mul _ _).trans (congrArg₂ (· * ·) e0 hy.symm)) hfa).trans ?_)
    simp only [Subgroup.coe_mul, Units.val_mul]
  have hRF : Formalism.L2.SG.ColDict.RepF S.X (S.tr u).wt (S.tr u).ιA ((B.toH (a₀ * b * a₀⁻¹)).2 : S.X.B.I.Gf)
      ((S.tr u).h0 * y * (S.tr u).h0⁻¹) := by
    have h := hRep
    rw [hfg] at h
    exact h
  obtain ⟨hmemIff, hpsi⟩ := (S.lev u).2 (B.toH (a₀ * b * a₀⁻¹)).2 _ hRF
  have hconj : (S.tr u).h0⁻¹ * ((S.tr u).h0 * y * (S.tr u).h0⁻¹) * (S.tr u).h0 = y := by group
  have hfinE : embA B.d B.o (a₀ * b * a₀⁻¹) ∈ GfC (D.sp.Y 0) := GlobalTheory.Core.Mi.CenAct.embA_mem_GfC B.d B.o hgf
  have hfst : (iotaX S.X S.inst (embA B.d B.o (a₀ * b * a₀⁻¹))).1 = 1 := GlobalTheory.Core.Mi.CenAct.iotaX_fst S.inst hfinE
  have hio : iotaX S.X S.inst (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * b * a₀⁻¹) *
      (iotaX S.X S.inst).symm (1, S.X.xu u)) =
      (1, (S.X.xu u)⁻¹ * ((B.toH (a₀ * b * a₀⁻¹)).2 : S.X.B.I.Gf) * S.X.xu u) := by
    rw [map_mul, map_mul, map_inv, (iotaX S.X S.inst).apply_symm_apply]
    ext
    · simp only [Prod.fst_mul, Prod.fst_inv, hfst, mul_one, inv_one]
    · rfl
  have hrow : ∀ k, k ∈ rowJ S.X S.inst ↔ (iotaX S.X S.inst k).1 = 1 ∧ (iotaX S.X S.inst k).2 ∈ S.X.K2 := fun k => Iff.rfl
  have hU' : ∀ hyU : (y : GL _ _) ∈ (F₀ u).cls0.lev.U,
      ((((S.tr u).h0⁻¹ * ((S.tr u).h0 * y * (S.tr u).h0⁻¹) * (S.tr u).h0 :
        Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
          GL _ _) ∈ (F₀ u).cls0.lev.U) := fun hyU => by rw [hconj]; exact hyU
  refine ⟨⟨fun hk => ?_, fun hr => ?_⟩, fun hk => ?_⟩
  · have hm := hmemIff.2 (hU' (hU.2 hk))
    rw [hrow, hio]
    exact ⟨rfl, hm⟩
  · rw [hrow, hio] at hr
    have h2 := hmemIff.1 hr.2
    rw [hconj] at h2
    exact hU.1 h2
  · have hyU := hU.2 hk
    have hm := hmemIff.2 (hU' hyU)
    have hp := hpsi hm (hU' hyU)
    have hc := hchi hyU
    have hchieq : (((F₀ u).cls0.lev.chi ⟨_, hU' hyU⟩ : ℂˣ) : ℂ) = (((F₀ u).cls0.lev.chi ⟨_, hyU⟩ : ℂˣ) : ℂ) := by
      have key : ∀ (z : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
          (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (hz : z.1 ∈ (F₀ u).cls0.lev.U), z = y →
          (((F₀ u).cls0.lev.chi ⟨_, hz⟩ : ℂˣ) : ℂ) = (((F₀ u).cls0.lev.chi ⟨_, hyU⟩ : ℂˣ) : ℂ) := by
        rintro z hz rfl
        rfl
      exact key _ _ hconj
    unfold rowChi
    rw [hio]
    have hpv : ((psiK S.X u _ ⟨_, hm⟩ : ℂˣ) : ℂ) =
        S.X.chi2 ((S.X.xu u)⁻¹ * ((B.toH (a₀ * b * a₀⁻¹)).2 : S.X.B.I.Gf) * S.X.xu u) := rfl
    have hn : ‖S.X.chi2 ((S.X.xu u)⁻¹ * ((B.toH (a₀ * b * a₀⁻¹)).2 : S.X.B.I.Gf) * S.X.xu u)‖ = 1 :=
      S.Y.hK.2.2.2.2 _ hm
    have h1 : S.X.chi2 ((S.X.xu u)⁻¹ * ((B.toH (a₀ * b * a₀⁻¹)).2 : S.X.B.I.Gf) * S.X.xu u) *
        levChi (d.st 0).V (d.st 0).β (d.st 0).L
          ((d.t 0)⁻¹ * embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o b * d.t 0) = 1 := by
      rw [← hpv, hp, hchieq]
      exact hc
    generalize S.X.chi2 ((S.X.xu u)⁻¹ * ((B.toH (a₀ * b * a₀⁻¹)).2 : S.X.B.I.Gf) * S.X.xu u) = c at hn h1 ⊢
    generalize levChi (d.st 0).V (d.st 0).β (d.st 0).L
      ((d.t 0)⁻¹ * embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o b * d.t 0) = L at h1 ⊢
    have hsc : star c * c = 1 := by
      rw [Complex.star_def, Complex.conj_mul', hn]
      simp
    calc star c = star c * (c * L) := by rw [h1, mul_one]
      _ = (star c * c) * L := by ring
      _ = L := by rw [hsc, one_mul]

end GlobalTheory.ColMatch

end
