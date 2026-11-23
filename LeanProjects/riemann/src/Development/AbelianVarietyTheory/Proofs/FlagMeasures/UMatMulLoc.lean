import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EquivPf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AmpRelAtPt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaFiniteOfHaar
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellRep

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StabInv

open Formalism.QuantumDeterminants PI.AmpRootCommon PI.AmpRelAtPt

variable {k r : ℕ}

theorem psi_rel (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z') (c : ℂ) (hc : star c = c)
    (p : Point ℂ (r + 1)) (g₀ : MatKR k r) (hg : g₀ ∈ UH (Hpk k r)) (hZ : ZhatO k r z z' g₀ = ptMat p)
    (a : MatKR k r) (ha : a ∈ RStab k r g₀) : psi k r z c a = psi k r z' c (g₀⁻¹ * a * g₀) := by
  have ha' : a ∈ Nset k r ∧ g₀⁻¹ * a * g₀ ∈ Nset k r := ha
  have hsum := sum_super (ptσ_invol p) (zhat_pt hZ) (ptζ_ne p) (fun i i1 h => pt_adj p i i1 h)
    (flagMat_upper (z := z) ha'.1) (flagMat_diag ha'.1) (flagMat_upper (z := z') ha'.2)
    (flagMat_diag ha'.2) (flag_rel hz hz' hg ha)
  have hell : ell k r z' (g₀⁻¹ * a * g₀) = star (ell k r z a) := by
    rw [ell_eq, ell_eq, hsum]
  have hcim : c.im = 0 := Complex.conj_eq_iff_im.mp hc
  have hre : (c * star (ell k r z a)).re = (c * ell k r z a).re := by
    simp [Complex.mul_re, hcim]
  simp only [Formalism.QuantumDeterminants.psi, hell, hre]

theorem psi_conj (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (c : ℂ) {n m : MatKR k r}
    (hn : n ∈ Nset k r) (hm : m ∈ Nset k r) : psi k r z c (n⁻¹ * m * n) = psi k r z c m := by
  obtain ⟨hone, hmulN, hinvN⟩ := Formalism.QuantumDeterminants.unipotent_subgroup_holds k r
  have hni : n⁻¹ ∈ Nset k r := hinvN n hn
  have h1 : psi k r z c 1 = 1 := by
    have hmul := Formalism.FourierDecayAlt.P.PBG.psi_mul_nset z hz c hone hone
    rw [Matrix.one_mul] at hmul
    have hne : psi k r z c 1 ≠ 0 := Complex.exp_ne_zero _
    exact mul_left_cancel₀ hne (hmul.symm.trans (mul_one _).symm)
  have hinv : n⁻¹ * n = 1 := uh_inv_mul hn.1
  have hpair := Formalism.FourierDecayAlt.P.PBG.psi_mul_nset z hz c hni hn
  rw [hinv, h1] at hpair
  rw [Formalism.FourierDecayAlt.P.PBG.psi_mul_nset z hz c (hmulN _ hni _ hm) hn,
    Formalism.FourierDecayAlt.P.PBG.psi_mul_nset z hz c hni hm]
  calc psi k r z c n⁻¹ * psi k r z c m * psi k r z c n
      = psi k r z c m * (psi k r z c n⁻¹ * psi k r z c n) := by ring
    _ = psi k r z c m := by rw [← hpair, mul_one]

theorem psi_cell (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z')
    (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') (c : ℂ) (hc : star c = c) (p : Point ℂ (r + 1)) (γ : MatKR k r)
    (hγ : γ ∈ UH (Hpk k r)) (hcell : IsInCell (ZhatO k r z z' γ) p) {m : MatKR k r} (hm : m ∈ Nset k r)
    (hm' : γ⁻¹ * m * γ ∈ Nset k r) : psi k r z c m = psi k r z' c (γ⁻¹ * m * γ) := by
  obtain ⟨n, hn, n', hn', g₀, hg₀, rfl, hZ⟩ := GlobalTheory.CellRep.cell_rep k r z z' γ p hz hz' hT hT' hγ hcell
  obtain ⟨_, hmulN, hinvN⟩ := Formalism.QuantumDeterminants.unipotent_subgroup_holds k r
  have e1 : n' * n'⁻¹ = 1 := uh_mul_inv hn'.1
  have key : n' * ((n * g₀ * n')⁻¹ * m * (n * g₀ * n')) * n'⁻¹ = g₀⁻¹ * (n⁻¹ * m * n) * g₀ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc n' n'⁻¹, e1, Matrix.one_mul, Matrix.mul_one]
  have hnmn : n⁻¹ * m * n ∈ Nset k r :=
    hmulN _ (hmulN _ (hinvN n hn) _ hm) _ hn
  have ha : n⁻¹ * m * n ∈ RStab k r g₀ := by
    refine ⟨hnmn, ?_⟩
    rw [← key]
    exact hmulN _ (hmulN _ hn' _ hm') _ (hinvN n' hn')
  have hback := psi_conj z' hz' c (hinvN n' hn') hm'
  rw [Matrix.nonsing_inv_nonsing_inv _ (Matrix.isUnit_det_of_right_inverse e1)] at hback
  calc psi k r z c m = psi k r z c (n⁻¹ * m * n) := (psi_conj z hz c hn hm).symm
    _ = psi k r z' c (g₀⁻¹ * (n⁻¹ * m * n) * g₀) := psi_rel z z' hz hz' c hc p g₀ hg₀ hZ _ ha
    _ = psi k r z' c (n' * ((n * g₀ * n')⁻¹ * m * (n * g₀ * n')) * n'⁻¹) := by rw [key]
    _ = psi k r z' c ((n * g₀ * n')⁻¹ * m * (n * g₀ * n')) := hback

end GlobalTheory.StabInv

namespace GlobalTheory.StabInv

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf.WuDec Formalism.L2.SG.Pf.EquivPf Formalism.L2.SG.Pf.Choice

theorem wloc_n {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F)
    (s x : Formalism.REAL.UJ (X.B.I.ε v)) (hs : s ∈ Nloc X u v) :
    X.Wloc u v (s * x) = psiV X u v (uMat s) • X.Wloc u v x := by
  have h1H : (1 : Formalism.REAL.UJ (X.B.I.ε v)) ∈ Hloc X u v := by
    intro y _
    rw [uMat_one', Matrix.one_mulVec]
  have h1N : (1 : Formalism.REAL.UJ (X.B.I.ε v)) ∈ Nloc X u v := by
    refine ⟨?_, ?_⟩
    · rw [uMat_one']
      exact inS_one
    · intro y _
      rw [uMat_one', sub_self, Matrix.zero_mulVec]
      exact Submodule.zero_mem _
  have hA := locEquiv X u v s hs 1 h1H x
  have hB := locEquiv X u v 1 h1N 1 h1H x
  simp only [mul_one] at hA
  simp only [mul_one, one_mul, uMat_one', psiV_one, one_smul] at hB
  rw [hA, ← hB]

theorem uMat_mul_loc {n : ℕ} {ε : Fin n → Bool} (a b : Formalism.REAL.UJ ε) : uMat (a * b) = uMat a * uMat b := rfl

theorem stab_inv : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (p : Point ℂ (D.R.rS + 1)), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → RelPt D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) γ) p → ∀ s ∈ Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε (vOf X τ)) (fun a => rv X.B.I (vOf X τ) (X.eR a)) (rv X.B.I (vOf X τ) (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε (vOf X τ)) (fun a => rv X.B.I (vOf X τ) (X.eR a)) (rv X.B.I (vOf X τ) (X.zR u'))) γ, ∀ x, Formalism.L2.SG.TermOp.rk1 (X.Wloc u (vOf X τ) (s * x)) (X.Wloc u' (vOf X τ) (γ⁻¹ * (s * x))) = Formalism.L2.SG.TermOp.rk1 (X.Wloc u (vOf X τ) x) (X.Wloc u' (vOf X τ) (γ⁻¹ * x)) := by
  intro D X θ C _ u u' τ γ p _ hrel s hs x
  obtain ⟨hQiQ, hQQi, hgram, hcol⟩ := C.isT τ
  have hs1 : s ∈ Nloc X u (vOf X τ) := hs.1
  have hs2 : γ⁻¹ * s * γ ∈ Nloc X u' (vOf X τ) := hs.2
  have hn : X.B.I.n = 2 * D.R.rS + D.R.k + 1 := Formalism.L2.SG.Pf.Choice.n_eq' X
  have hc : ∀ a : Fin D.R.rS, frS D ^ (D.R.rS - (a : ℕ)) ≠ 0 :=
    fun a => pow_ne_zero _ (Formalism.L2.SG.Pf.Choice.frS_ne D)
  have hcolE : ∀ a : Fin D.R.rS, C.Q τ *ᵥ Pi.single (eI D.R.k D.R.rS a) 1 =
      frS D ^ (D.R.rS - (a : ℕ)) • Formalism.L2.SG.HidaSetting.rv X.B.I (vOf X τ) (X.eR a) :=
    fun a => (hcol a a rfl).1
  have hmN : ∀ (w : D.what₂.Word) (t : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))), t ∈ Nloc X w (vOf X τ) →
      C.Qi τ * uMat t * C.Q τ ∈ Nset D.R.k D.R.rS := by
    intro w t ht
    have hU : (uMat t)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat t = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := t.2
    exact nset_loc hn _ _ _ hQiQ hQQi hgram _ _ hc hcolE _ hU ht
  have hpsi : ∀ (w : D.what₂.Word) (t : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))), t ∈ Nloc X w (vOf X τ) →
      psiV X w (vOf X τ) (uMat t) = psiS D (zB X (C.Qi τ) w τ) (C.Qi τ * uMat t * C.Q τ) := by
    intro w t ht
    have hback : C.Q τ * (C.Qi τ * uMat t * C.Q τ) * C.Qi τ = uMat t := by
      simp only [← Matrix.mul_assoc, hQQi, Matrix.one_mul]
      rw [Matrix.mul_assoc, hQQi, Matrix.mul_one]
    have h := Formalism.L2.SG.Pf.psiTr C w τ _ (hmN w t ht)
    rw [hback] at h
    exact h
  set g := Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) γ with hg
  have hginv : g⁻¹ = C.Qi τ * uMat γ⁻¹ * C.Q τ := by
    apply Matrix.inv_eq_left_inv
    rw [hg, Formalism.L2.SG.RealObj.trG]
    calc C.Qi τ * uMat γ⁻¹ * C.Q τ * (C.Qi τ * uMat γ * C.Q τ)
        = C.Qi τ * (uMat γ⁻¹ * (C.Q τ * C.Qi τ) * uMat γ) * C.Q τ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQQi, Matrix.mul_one, uMat_inv_mul, Matrix.mul_one, hQiQ]
  have hconj : C.Qi τ * uMat (γ⁻¹ * s * γ) * C.Q τ = g⁻¹ * (C.Qi τ * uMat s * C.Q τ) * g := by
    rw [hginv, hg, Formalism.L2.SG.RealObj.trG, uMat_mul_loc, uMat_mul_loc]
    calc C.Qi τ * (uMat γ⁻¹ * uMat s * uMat γ) * C.Q τ
        = C.Qi τ * (uMat γ⁻¹ * 1 * uMat s * 1 * uMat γ) * C.Q τ := by
          rw [Matrix.mul_one, Matrix.mul_one]
      _ = C.Qi τ * uMat γ⁻¹ * C.Q τ * (C.Qi τ * uMat s * C.Q τ) * (C.Qi τ * uMat γ * C.Q τ) := by
          rw [← hQQi]
          simp only [Matrix.mul_assoc]
  obtain ⟨hz, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  obtain ⟨hz', hTz'⟩ := Formalism.L2.SG.Pf.zTr C u' τ
  have hT : 0 < Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by
    rw [hTz]; exact Formalism.L2.SG.Pf.Choice.Tr_pos D u
  have hT' : 0 < Tz D.R.k D.R.rS (zB X (C.Qi τ) u' τ) := by
    rw [hTz']; exact Formalism.L2.SG.Pf.Choice.Tr_pos D u'
  have hm' : g⁻¹ * (C.Qi τ * uMat s * C.Q τ) * g ∈ Nset D.R.k D.R.rS := by
    rw [← hconj]; exact hmN u' _ hs2
  have hkey : psiV X u (vOf X τ) (uMat s) = psiV X u' (vOf X τ) (uMat (γ⁻¹ * s * γ)) := by
    rw [hpsi u s hs1, hpsi u' _ hs2, hconj]
    exact psi_cell _ _ hz hz' hT hT' _ (Complex.conj_ofReal _) p g hrel.1 hrel.2.1 (hmN u s hs1) hm'
  have hx : γ⁻¹ * (s * x) = (γ⁻¹ * s * γ) * (γ⁻¹ * x) := by group
  rw [wloc_n X u (vOf X τ) s x hs1, hx, wloc_n X u' (vOf X τ) _ _ hs2, ← hkey]
  have hnorm : ‖psiV X u (vOf X τ) (uMat s)‖ = 1 := norm_psiR _ _ _ _ _ _
  have hcm : (starRingEnd ℂ) (psiV X u (vOf X τ) (uMat s)) * psiV X u (vOf X τ) (uMat s) = 1 := by
    rw [Complex.conj_mul', hnorm]; norm_num
  ext ξ
  rw [Formalism.L2.SG.TermOp.rankOneInnerOperator_apply, Formalism.L2.SG.TermOp.rankOneInnerOperator_apply, inner_smul_left, smul_smul]
  congr 1
  linear_combination (inner ℂ (X.Wloc u' (vOf X τ) (γ⁻¹ * x)) ξ) * hcm

end GlobalTheory.StabInv
