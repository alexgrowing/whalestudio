import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.FolnerJ2
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubSAsm
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubSH
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubSD

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix

namespace Formalism.L2.S.Pv.HaarSubS

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.EnergyAbs Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.Pf.WFL

theorem isFolner_Sinf_gen {n r k : ℕ} (hn : n = 2 * r + k + 1) {ι : Type} [Fintype ι] {εv : ι → Fin n → Bool}
    (ev fv : ι → Fin r → Fin n → ℂ) (wv : ι → Fin k → Fin n → ℂ) (zv : ι → Fin n → ℂ) (T : ι → ℝ)
    (hT : ∀ v, 0 < T v)
    (hee : ∀ v a b, hJ (εv v) (ev v a) (ev v b) = 0) (hff : ∀ v a b, hJ (εv v) (fv v a) (fv v b) = 0)
    (hef : ∀ v a b, hJ (εv v) (ev v a) (fv v b) = if a = b then 1 else 0)
    (hez : ∀ v a, hJ (εv v) (ev v a) (z0v (T v) (zv v)) = 0)
    (hfz : ∀ v a, hJ (εv v) (fv v a) (z0v (T v) (zv v)) = 0)
    (hzz : ∀ v, hJ (εv v) (z0v (T v) (zv v)) (z0v (T v) (zv v)) = -1)
    (hww : ∀ v a b, hJ (εv v) (wv v a) (wv v b) = if a = b then 1 else 0)
    (hew : ∀ v c a, hJ (εv v) (ev v c) (wv v a) = 0) (hfw : ∀ v c a, hJ (εv v) (fv v c) (wv v a) = 0)
    (hzw : ∀ v a, hJ (εv v) (z0v (T v) (zv v)) (wv v a) = 0)
    (μS : Measure (∀ v, Formalism.REAL.UJ (εv v)))
    (hμ : IsHaarSub {s : ∀ v, Formalism.REAL.UJ (εv v) | ∀ v, InS (ev v) (zv v) (uMat (s v))} μS) :
    IsFolner {s : ∀ v, Formalism.REAL.UJ (εv v) | ∀ v, InS (ev v) (zv v) (uMat (s v))} μS := by
  subst hn
  exact Formalism.L2.S.Pv.FolnerJ.isFolner_Sinf ev fv wv zv T hT
    (fun v => ⟨hee v, hff v, hef v, hez v, hfz v, hzz v, hww v, hew v, hfw v, hzw v⟩) μS hμ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hermitian_scaled_right {n : ℕ} (ε : Fin n → Bool) (T : ℝ) (x z : Fin n → ℂ) :
    hJ ε x (z0v T z) = (((Real.sqrt T)⁻¹ : ℝ) : ℂ) * hJ ε x z := by
  unfold z0v hJ
  simp [Matrix.mulVec_smul, dotProduct_smul]

theorem hermitian_scaled_left {n : ℕ} (ε : Fin n → Bool) (T : ℝ) (x z : Fin n → ℂ) :
    hJ ε (z0v T z) x = (((Real.sqrt T)⁻¹ : ℝ) : ℂ) * hJ ε z x := by
  unfold z0v hJ
  simp [Matrix.mulVec_smul, smul_dotProduct, star_smul]

theorem folner_of_haar {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word)
    (hμ : IsHaarSub (X.SinfU u) (Formalism.L2.SG.RealObj.muS X u)) :
    IsFolner (X.SinfU u) (Formalism.L2.SG.RealObj.muS X u) := by
  have hn : X.B.I.n = 2 * D.R.rS + D.R.k + 1 := X.n_eq.trans (dimS_eq D.R).symm
  have hT : 0 < Tw (D := D) u := ProductExactness.Tw_pos u
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  refine isFolner_Sinf_gen hn (fun v a => rv X.B.I v (X.eR a)) (fun v a => rv X.B.I v (X.fR a))
    (fun v => X.wfr u v) (fun v => rv X.B.I v (X.zR u)) (fun _ => Tw u) (fun _ => hT) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (Formalism.L2.SG.RealObj.muS X u) hμ
  · intro v a b
    exact (ProductExactness.hJ_X X v _ _).trans (by rw [X.ee]; simp)
  · intro v a b
    exact (ProductExactness.hJ_X X v _ _).trans (by rw [X.ff]; simp)
  · intro v a b
    exact (ProductExactness.hJ_X X v _ _).trans (by rw [X.ef]; split_ifs <;> simp)
  · intro v a
    rw [hermitian_scaled_right]
    have : hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) = 0 :=
      (ProductExactness.hJ_X X v _ _).trans (by rw [(X.zu_orth u a).1]; simp)
    rw [this, mul_zero]
  · intro v a
    rw [hermitian_scaled_right]
    have : hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) = 0 :=
      (ProductExactness.hJ_X X v _ _).trans (by rw [(X.zu_orth u a).2]; simp)
    rw [this, mul_zero]
  · intro v
    rw [hermitian_scaled_right, hermitian_scaled_left]
    have h5 : hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u)) = -(Tw (D := D) u : ℂ) :=
      (ProductExactness.hJ_X X v _ _).trans (by rw [X.zu_norm u]; simp [Tw])
    rw [h5]
    have hs : ((Real.sqrt (Tw (D := D) u))⁻¹ : ℝ) * (Real.sqrt (Tw (D := D) u))⁻¹ * Tw (D := D) u = 1 := by
      rw [← mul_inv, Real.mul_self_sqrt hT.le, inv_mul_cancel₀ hT.ne']
    have : (((Real.sqrt (Tw (D := D) u))⁻¹ : ℝ) : ℂ) * ((((Real.sqrt (Tw (D := D) u))⁻¹ : ℝ) : ℂ) *
        -((Tw (D := D) u : ℝ) : ℂ)) = -(((Real.sqrt (Tw (D := D) u))⁻¹ * (Real.sqrt (Tw (D := D) u))⁻¹ *
          Tw (D := D) u : ℝ) : ℂ) := by push_cast; ring
    rw [this, hs]
    simp
  · intro v a b
    exact X.wfr_on u v a b
  · intro v c a
    exact ((X.wfr_perp u v a).1 c).1
  · intro v c a
    exact ((X.wfr_perp u v a).1 c).2
  · intro v a
    rw [hermitian_scaled_left]
    have h0 : hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (X.wfr u v a) = 0 := (X.wfr_perp u v a).2
    rw [h0, mul_zero]

theorem stepSubG_of_MN (hN : MeasN) (hQ : NuQSFinite) : Formalism.L2.SG.RealObj.EnergyInst.StepSubG := by
  exact stepSubG_of sDecomp_holds hN (measH_of sDecomp_holds)
    (fun D X u => folner_of_haar X u (isHaarSub_SinfU sDecomp_holds hN (measH_of sDecomp_holds) X u)) hQ

end Formalism.L2.S.Pv.HaarSubS
