import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CMeasSbox

noncomputable section

open MeasureTheory Matrix NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf
  Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.L2.SG.RealObj.InfCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Inv

variable {r k : ℕ}

def RcInv (y : LsNc5.CIdx r k → ℝ) : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ) :=
  (fun c => (⟨y (eIdx (Sum.inl (c, false))), y (eIdx (Sum.inl (c, true)))⟩ : ℂ), fun a => y (eIdx (Sum.inr a)))

theorem Rc_RcInv (y : LsNc5.CIdx r k → ℝ) : Rc (RcInv y) = y := by
  funext i
  obtain ⟨j, rfl⟩ := eIdx.surjective i
  rcases j with ⟨c, b⟩ | a
  · cases b <;> simp [Rc, RcInv, LsNc5.reim]
  · simp [Rc, RcInv]

theorem measurable_RcInv : Measurable (RcInv (r := r) (k := k)) := by
  apply Continuous.measurable
  unfold RcInv
  have h : Continuous fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ) := Complex.equivRealProdCLM.symm.continuous
  exact Continuous.prodMk (continuous_pi fun c => h.comp'
      (f := fun a : LsNc5.CIdx r k → ℝ => (a (eIdx (Sum.inl (c, false))), a (eIdx (Sum.inl (c, true)))))
      ((continuous_apply _).prodMk (continuous_apply _)))
    (continuous_pi fun a => continuous_apply _)

def dYInv (T : ℝ) (y : LsNc5.CIdx r k → ℝ) : LsNc5.CIdx r k → ℝ := fun i => y i / dY T i

theorem dY_pos {T : ℝ} (hT : 0 < T) (i : LsNc5.CIdx r k) : 0 < dY T i := by
  rcases i with (a | a) | a <;> simp [dY, hT]

theorem LyM_dYInv {T : ℝ} (hT : 0 < T) (y : LsNc5.CIdx r k → ℝ) : LyM T (dYInv T y) = y := by
  funext i
  simp only [LyM, Matrix.toLin'_apply, Matrix.mulVec_diagonal, dYInv]
  field_simp [(dY_pos hT i).ne']

theorem measurable_dYInv (T : ℝ) : Measurable (dYInv (r := r) (k := k) T) := by
  unfold dYInv
  exact measurable_pi_lambda _ fun i => (measurable_pi_apply i).div_const _

end Inv

theorem surjLoc {n r k : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ)
    (w : Fin k → Fin n → ℂ) (z : Fin n → ℂ) {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (w a) = 0) (hfw : ∀ c a, hJ ε (f c) (w a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (w a) = 0) :
    ∃ σL : (LsNc5.CIdx r k → ℝ) → Formalism.REAL.UJ ε, Measurable σL ∧
      ∀ y, σL y ∈ NLoc ε e z ∧ kapL ε e f w z (σL y) = y := by
  subst hn
  have hFJ := isFrameJ_of hT hee hff hef hww hew hfw hez hfz hzz hzw
  have emb := embQ hFJ
  have hQz : Qm e f w (z0v T z) *ᵥ zBv k r T = z := Qm_zB hT z
  set Ψ := cM (ε := ε) (Qi ε e f w (z0v T z)) (Qm e f w (z0v T z)) with hΨ
  let ψ0 : (LsNc5.CIdx r k → ℝ) → (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ) := fun y => RcInv (dYInv T y)
  have hψ0 : Measurable ψ0 := measurable_RcInv.comp (measurable_dYInv T)
  let Φ : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ) → Mt k r := fun t => WlocSk.NB.phi0 t.1 t.2
  have hΦc : Continuous Φ := WlocSk.NB.continuous_nilpotent_chart
  have hΦN : ∀ t : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ), WlocSk.NB.phi0 t.1 t.2 ∈ Nset k r := fun t =>
    WlocSk.NB.test_vector_mem_schwartz_bruhat t.1 t.2
  have hrange : ∀ t, Φ t ∈ Set.range Ψ := fun t => by
    refine ⟨toUJ _ (conjQ_UJ hFJ (hΦN t).1), ?_⟩
    show (Qi ε e f w (z0v T z) * uMat (toUJ _ (conjQ_UJ hFJ (hΦN t).1)) * Qm e f w (z0v T z) :
      Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = WlocSk.NB.phi0 t.1 t.2
    rw [uMat_toUJ, Qi_Qm_conj hFJ]
  let σL : (LsNc5.CIdx r k → ℝ) → Formalism.REAL.UJ ε := fun y => emb.equivRange.symm ⟨Φ (ψ0 y), hrange (ψ0 y)⟩
  have hσΨ : ∀ y, Ψ (σL y) = Φ (ψ0 y) := fun y => by
    have h1 := emb.equivRange.apply_symm_apply ⟨Φ (ψ0 y), hrange (ψ0 y)⟩
    rw [MeasurableEmbedding.equivRange_apply] at h1
    exact congrArg Subtype.val h1
  have hz0 : ∃ t : ℂ, z0v T z = t • (Qm e f w (z0v T z) *ᵥ zBv k r T) :=
    ⟨(((Real.sqrt T)⁻¹ : ℝ) : ℂ), by rw [hQz]; rfl⟩
  refine ⟨σL, ?_, fun y => ⟨?_, ?_⟩⟩
  · exact emb.equivRange.symm.measurable.comp
      ((hΦc.measurable.comp hψ0).subtype_mk)
  · have hN : Qi ε e f w (z0v T z) * uMat (σL y) * Qm e f w (z0v T z) ∈ Nset k r := by
      have : (Qi ε e f w (z0v T z) * uMat (σL y) * Qm e f w (z0v T z) :
          Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = WlocSk.NB.phi0 (ψ0 y).1 (ψ0 y).2 := hσΨ y
      rw [this]; exact hΦN _
    have h1 := inN_of_conj hFJ (inWb_zB T) hN
    rw [hQz] at h1
    exact h1
  · have hN : Qi ε e f w (z0v T z) * uMat (σL y) * Qm e f w (z0v T z) ∈ Nset k r := by
      have : (Qi ε e f w (z0v T z) * uMat (σL y) * Qm e f w (z0v T z) :
          Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = WlocSk.NB.phi0 (ψ0 y).1 (ψ0 y).2 := hσΨ y
      rw [this]; exact hΦN _
    rw [kapL_eq hFJ hT (σL y) hN]
    show Kc T (Ψ (σL y)) = y
    rw [hσΨ y]
    funext i
    rw [chart_kappa_coordinates T (ψ0 y) i, ← LyM_apply]
    show LyM T (Rc (RcInv (dYInv T y))) i = y i
    rw [Rc_RcInv, LyM_dYInv hT]

theorem kapSurj_holds : KapSurj := by
  intro D X u
  have hloc := fun v : InfinitePlace X.B.I.F => surjLoc (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v)
    (ProductExactness.zV X u v) (ProductExactness.Tw_pos u) (fX_ee X v) (fX_ff X v) (fX_ef X v) (fX_ww X u v) (fX_ew X u v)
    (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v)
  choose σL hσm hσ using hloc
  refine ⟨fun t v => σL v (fun i => Φc t (v, i)), ?_, fun t => ⟨fun v => (hσ v _).1, ?_⟩⟩
  · exact measurable_pi_lambda _ fun v => (hσm v).comp
      (measurable_pi_lambda _ fun i => (measurable_pi_apply (v, i)).comp measurable_Φc)
  · have hk : Φc (blk X u (fun v => σL v (fun i => Φc t (v, i)))) = Φc t := by
      rw [← kap_eq_Φc]
      funext p
      have := (hσ p.1 (fun i => Φc t (p.1, i))).2
      have h2 := congrFun (kapV_eq X u p.1 (fun v => σL v (fun i => Φc t (v, i)))) p.2
      exact h2.trans (congrFun this p.2)
    have := congrArg Ψc hk
    rwa [Ψc_Φc, Ψc_Φc] at this

end Formalism.L2.SG.Pf.NcReal.JX
