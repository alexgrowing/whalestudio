import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StMatSpec
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.VolPinAsm
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CovolOneEqOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BlkOfOfPtEntry
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FibreCounting
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupLift
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalCommonStabiliserUnitriangularCoordsStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.CovDict

open Formalism.L2.SG.Pf.VolPinAsm

section Gen

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {m : ℕ}

theorem sum_smul_sum (e : Fin m → V) (P Q : Matrix (Fin m) (Fin m) K) (b : Fin m) :
    ∑ a, P a b • ∑ c, Q c a • e c = ∑ c, (Q * P) c b • e c := by
  simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by rw [mul_comm]

theorem fm_conj {e f : Fin m → V} (ψ τ : V ≃ₗ[K] V) {P B : Matrix (Fin m) (Fin m) K} (hP : IsUnit P.det)
    (hψ : ∀ b, ψ (e b) = ∑ a, P a b • f a) (hτ : FM f τ B) :
    FM e (fun y => ψ.symm (τ (ψ y))) (P⁻¹ * B * P) := by
  intro b
  have hτ' : ∀ a, τ (f a) = ∑ c, B c a • f c := hτ
  apply ψ.injective
  show ψ (ψ.symm (τ (ψ (e b)))) = _
  rw [LinearEquiv.apply_symm_apply, hψ b, map_sum]
  simp only [map_smul, hτ']
  rw [sum_smul_sum, map_sum]
  simp only [map_smul, hψ]
  rw [sum_smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mul_assoc P⁻¹ B P, Matrix.mul_nonsing_inv_cancel_left _ _ hP]

theorem mat_eq_of_indep {e : Fin m → V} (he : LinearIndependent K e) (y : Fin m → V)
    {M M' : Matrix (Fin m) (Fin m) K} (h1 : ∀ b, y b = ∑ a, M a b • e a) (h2 : ∀ b, y b = ∑ a, M' a b • e a) :
    M = M' := by
  ext c b
  have h0 : ∑ i, (M i b - M' i b) • e i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← h1 b, ← h2 b, sub_self]
  exact sub_eq_zero.1 ((Fintype.linearIndependent_iff.1 he) _ h0 c)

end Gen

end GlobalTheory.HL.CovDict

namespace GlobalTheory.HL.CovDict

open Formalism.L2.SG.Pf.VolPinAsm Formalism.L2.SG.Pf.StabilizerIndexVolumes Matrix

theorem dict_coords : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → t₀.relevant → ∀ (γw s s' : X.B.I.Ginf), Formalism.L2.SG.RealObj.IsPtRep X u u' w γw → s ∈ X.SinfU u → s' ∈ X.SinfU u' → t₀.pt.1 = s * γw * s'⁻¹ → ∃ σ : Formalism.L2.SG.RealObj.FreeE w → ℂ, (∀ p, ‖σ p‖ = (D.host.rdE : ℝ) ^ (p.1.2.val - p.1.1.val)) ∧ ∃ A : InfinitePlace X.B.I.F → (Formalism.L2.SG.RealObj.FreeE w → ℂ) →ₗ[ℂ] (Formalism.L2.SG.RealObj.FreeE w → ℂ), (∀ v x x' p, (∀ q : Formalism.L2.SG.RealObj.FreeE w, q.1.2.val - q.1.1.val < p.1.2.val - p.1.1.val → x q = x' q) → A v x p - x p = A v x' p - x' p) ∧ ∀ (x : X.B.I.GA) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X x n → c.grp ρ n ∈ G.K0 → ∀ v, Formalism.L2.SG.RealObj.stCoord X u' w γw (s⁻¹ * x.1 * s) v = A v (fun p => σ p * Formalism.L2.SG.Pf.VolPinAsm.phiV X v (GlobalTheory.HL.TraceConjugationCover.stMat G (c.grp ρ n) p.1.1 p.1.2)) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t₀ ρ U U' hMv _ γw s s' _ _ hs' hpt
  obtain ⟨-, -, hU', -, hρ'⟩ := hMv
  have hrd : (0 : ℝ) < D.host.rdE := (Formalism.BasicNotions.rdE_pos_le D).1
  have hrdc : (D.host.rdE : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hrd.ne'
  have hU'u : IsUnit U'.det := by rw [up_det hU']; exact isUnit_one
  choose S hSU hS using fun v => inS_frame (hs' v)
  have hSu : ∀ v, IsUnit (S v).det := fun v => by rw [up_det (hSU v)]; exact isUnit_one
  set N : InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ := fun v =>
    U'.map (phiV X v) * S v with hN
  have hNU : ∀ v, IsUpUni (N v) := fun v => up_mul (upUni_map (phiV X v) hU') (hSU v)
  have hNu : ∀ v, IsUnit (N v).det := fun v => by rw [up_det (hNU v)]; exact isUnit_one
  refine ⟨fun p => (D.host.rdE : ℂ) ^ (p.1.2.1 - p.1.1.1), fun p => ?_,
    fun v => Alin w (D.host.rdE : ℂ) (N v), fun v x x' p hxx => Alin_shear w _ (hNU v) hrdc x x' p hxx, ?_⟩
  · rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hrd.le]
  intro x n hxn hK v
  funext p

  have hStm : c.grp ρ n ∈ G.St := fun q => by
    obtain ⟨g', hg', he⟩ := hK q
    exact ⟨g', hg'.1.1, he⟩
  obtain ⟨B, hBU, hBf, hBblk⟩ :=
    (GlobalTheory.T.rationalCommonStabiliser_unitriangular_coords D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c).1 _ hStm
  have hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u').A.T_prime.ne_zero
  have hli : LinearIndependent D.host.E G.f' := by
    have e : G.f' = fun a => c.e (frame F'0 a) := funext c.f'_eq
    rw [e]
    exact (Formalism.L2.SG.Pf.TupLift.frame_li F'0 hT').map' _ (LinearEquiv.ker _)
  have hB : GlobalTheory.HL.TraceConjugationCover.stMat G (c.grp ρ n) = B :=
    mat_eq_of_indep hli _ (GlobalTheory.HL.TraceConjugationCover.stMat_spec G _ ⟨B, hBf⟩) hBf
  rw [hB]

  set τ : (VS D).V ≃ₗ[D.host.E] (VS D).V := ρ.symm.trans (n.trans ρ) with hτdef
  have hτ : FM (frame F'0) τ B := by
    intro b
    apply c.e.injective
    have e1 : c.e (τ (frame F'0 b)) = c.grp ρ n (G.f' b) := by
      rw [c.f'_eq]; simp [GCoord.grp, τ]
    rw [e1, hBf b, map_sum]
    simp only [map_smul, c.f'_eq]
  set ψ : (VS D).V ≃ₗ[D.host.E] (VS D).V := t₀.lin.trans ρ with hψdef
  have hψ : ∀ b, ψ ((X.Fu u').fvec b) = ∑ a, U' a b • frame F'0 a := by
    intro b
    show ρ (t₀.lin _) = _
    rw [← Formalism.L2.SG.Pf.FibreCounting.frame_apply]
    exact hρ' b
  have hFMm := fm_conj ψ τ hU'u hψ hτ
  have hFMm' : FM (X.Fu u').fvec (t₀.lin⁻¹ * n * t₀.lin) (U'⁻¹ * B * U') := by
    intro b
    rw [← hFMm b]
    show t₀.lin.symm (n (t₀.lin _)) = _
    simp [ψ, τ]
  have hγx : RatLink X t₀.pt t₀.lin := t₀.rep.2.1
  set zz := t₀.pt⁻¹ * x * t₀.pt with hzz
  have hzL : RatLink X zz (t₀.lin⁻¹ * n * t₀.lin) :=
    Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (Formalism.L2.SG.TermOp.Vanish.ratLink_mul X
      (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hγx) hxn) hγx
  have hgrp : γw⁻¹ * (s⁻¹ * x.1 * s) * γw = s'⁻¹ * zz.1 * s' := by
    have e1 : zz.1 = t₀.pt.1⁻¹ * x.1 * t₀.pt.1 := by simp only [hzz, Prod.fst_mul, Prod.fst_inv]
    have e2 : γw = s⁻¹ * t₀.pt.1 * s' := by rw [hpt]; group
    rw [e1, e2]; group
  have hmi : ∀ a : Formalism.REAL.UJ (X.B.I.ε v), Formalism.MainNotions.S.uMat a * Formalism.MainNotions.S.uMat a⁻¹ = 1 := by
    intro a
    show _ * (((a⁻¹ : Formalism.REAL.UJ (X.B.I.ε v)) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) = 1
    rw [Subgroup.coe_inv, Units.mul_inv]
  have hu : Formalism.MainNotions.S.uMat ((s'⁻¹ * zz.1 * s') v) =
      (Formalism.MainNotions.S.uMat (s' v))⁻¹ * Formalism.MainNotions.S.uMat (zz.1 v) * Formalism.MainNotions.S.uMat (s' v) := by
    have hi : Formalism.MainNotions.S.uMat ((s' v)⁻¹) = (Formalism.MainNotions.S.uMat (s' v))⁻¹ :=
      (Matrix.inv_eq_right_inv (hmi (s' v))).symm
    show Formalism.MainNotions.S.uMat ((s' v)⁻¹ * zz.1 v * s' v) = _
    show Formalism.MainNotions.S.uMat ((s' v)⁻¹) * Formalism.MainNotions.S.uMat (zz.1 v) * Formalism.MainNotions.S.uMat (s' v) = _
    rw [hi]
  have hs'u : IsUnit (Formalism.MainNotions.S.uMat (s' v)).det := by
    have := congrArg Matrix.det (hmi (s' v))
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact isUnit_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one this)
  have hFM : FM (efr X u' v) (fun y => ((Formalism.MainNotions.S.uMat (s' v))⁻¹ * Formalism.MainNotions.S.uMat (zz.1 v) *
      Formalism.MainNotions.S.uMat (s' v)) *ᵥ y) ((S v)⁻¹ * (U'⁻¹ * B * U').map (phiV X v) * S v) :=
    FMm_mul (FMm_mul (FMm_inv hs'u (hS v) (hSu v)) (realFM X hzL hFMm' v)) (hS v)
  have hG : (S v)⁻¹ * (U'⁻¹ * B * U').map (phiV X v) * S v = (N v)⁻¹ * B.map (phiV X v) * N v := by
    have hinv : (U'.map (phiV X v))⁻¹ = (U'⁻¹).map (phiV X v) :=
      Matrix.inv_eq_left_inv (map_inv_mul (phiV X v) hU'u)
    rw [show N v = U'.map (phiV X v) * S v from rfl, Matrix.mul_inv_rev, hinv, Matrix.map_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  have hY : Yhat w (D.host.rdE : ℂ) (fun q => (D.host.rdE : ℂ) ^ (q.1.2.1 - q.1.1.1) *
      phiV X v (B q.1.1 q.1.2)) = B.map (phiV X v) - 1 := by
    ext c' d
    rw [Matrix.sub_apply, Matrix.map_apply]
    simp only [Yhat]
    split_ifs with hcd
    · rw [Matrix.one_apply_ne (ne_of_lt hcd.1), sub_zero]
      field_simp
    · by_cases hlt : c' < d
      · rw [hBblk c' d (fun he => hcd ⟨hlt, he⟩), map_zero, Matrix.one_apply_ne (ne_of_lt hlt), sub_zero]
      · rcases lt_or_eq_of_le (not_lt.1 hlt) with hgt | heq
        · rw [(hBU c' d).1 hgt, map_zero, Matrix.one_apply_ne (ne_of_gt hgt), sub_zero]
        · rw [heq, (hBU c' c').2 rfl, map_one, Matrix.one_apply_eq, sub_self]
  have hab : p.1.1 < p.1.2 := p.2.1
  have har : p.1.1.1 < D.R.rS := lt_of_lt_of_le hab (Nat.lt_succ_iff.1 p.1.2.2)
  show Formalism.L2.SG.RealObj.stCoord X u' w γw _ v p = Alin w (D.host.rdE : ℂ) (N v) _ p
  unfold Formalism.L2.SG.RealObj.stCoord
  rw [hgrp, hu, Alin_apply, hY]
  have hfrm : Formalism.L2.SG.RealObj.frm X u' D.host.rdE v p.1.2 =
      (((D.host.rdE : ℂ)) ^ (D.R.rS - p.1.2.1))⁻¹ • efr X u' v p.1.2 := rfl
  rw [hfrm, coef_efr X u' v hFM ⟨p.1.1.1, har⟩ p.1.2, hG]
  have hcs : (Fin.castSucc (⟨p.1.1.1, har⟩ : Fin D.R.rS)) = p.1.1 := Fin.ext rfl
  rw [hcs, conj_off (hNu v) (ne_of_lt hab)]
  have hpow : (D.host.rdE : ℂ) ^ (D.R.rS - p.1.1.1) =
      (D.host.rdE : ℂ) ^ (D.R.rS - p.1.2.1) * (D.host.rdE : ℂ) ^ (p.1.2.1 - p.1.1.1) := by
    rw [← pow_add]; congr 1
    have : (p.1.2 : ℕ) ≤ D.R.rS := Nat.lt_succ_iff.1 p.1.2.2
    have : (p.1.1 : ℕ) < p.1.2 := hab
    omega
  rw [hpow]
  field_simp

end GlobalTheory.HL.CovDict
