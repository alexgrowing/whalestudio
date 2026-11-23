import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutCVPresFF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WCellMemOmPlus
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QxChain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem tc_hsVec_smul (a : ℂ) (X : Wq →L[ℂ] Wp) : B.hsVec (a • X) = a • B.hsVec X := by
  simp only [B.hsVec, ContinuousLinearMap.smul_apply]
  rw [← WithLp.toLp_smul]
  rfl

theorem tc_hsVec_sum {ι : Type} (s : Finset ι) (X : ι → (Wq →L[ℂ] Wp)) :
    B.hsVec (∑ i ∈ s, X i) = ∑ i ∈ s, B.hsVec (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    simp only [B.hsVec, ContinuousLinearMap.zero_apply]
    exact WithLp.toLp_zero 2
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    simp only [B.hsVec, ContinuousLinearMap.add_apply]
    exact WithLp.toLp_add 2 _ _

theorem tc_gq (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (x : (Fin P.r → ℂ) × ℂ) :
    B.gq Bs x = Q.wCell P.k P.r (Fin.last P.r) x.1 * NF.muZ P.k P.r Bs.μsec x.2 := by
  show bigCell P.k P.r x.1 (Bs.μsec x.2) = _
  rw [(Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization P.k P.r x.1 (Bs.μsec x.2)).1, Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq]
  rfl

theorem tc_sqrt_wq (k r : ℕ) (TT : ℝ) (x : MA.E r) :
    Real.sqrt (MA.wq k x TT) =
      (∏ a : Fin r, (if a.val < (Fin.last r).val then ‖x.1 a‖ ^ (Formalism.QuantumDeterminants.Mdim k r a - 1) else 1)) *
        wR k TT x.2 := by
  unfold MA.wq wR
  rw [Real.sqrt_mul (Finset.prod_nonneg fun l _ => pow_nonneg (Complex.normSq_nonneg _) _)]
  congr 1
  have h : ∏ l : Fin r, Complex.normSq (x.1 l) ^ (MA.Mdim k r l - 1) =
      (∏ a : Fin r, (if a.val < (Fin.last r).val then ‖x.1 a‖ ^ (Formalism.QuantumDeterminants.Mdim k r a - 1) else 1)) ^ 2 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun a _ => ?_
    have hM : MA.Mdim k r a = Formalism.QuantumDeterminants.Mdim k r a := rfl
    rw [if_pos (by simp), Complex.normSq_eq_norm_sq, hM, ← pow_mul, ← pow_mul, mul_comm]
  rw [h, Real.sqrt_sq (Finset.prod_nonneg fun a _ => by split_ifs <;> positivity)]

theorem tc_rawJ (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ρ : M.Ty P) :
    rawJ P Bs e J ρ = rawR P Bs.μsec e (Q.resG P.k P.r (Fin.last P.r) J) ρ := by
  funext q
  simp only [rawJ, rawR, Q.resG, tc_gq, tc_sqrt_wq]
  rw [tc_hsVec_smul, inner_smul_right]
  push_cast
  ring

theorem tc_mu (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (q : MA.Qp P.r P.TT) :
    NF.muZ P.k P.r Bs.μsec q.1.2 ∈ Q.Glev P.k P.r (Fin.last P.r) ∧
      Q.wCell P.k P.r (Fin.last P.r) q.1.1 * NF.muZ P.k P.r Bs.μsec q.1.2 ∈ OmB Bs := by
  have hTT : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1]; rfl
  have hζ : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq q.1.2 := by
    rw [hTT]; exact q.2.2
  have hc : q.1.1 ∈ OmX P.r := q.2.1
  have hG : NF.muZ P.k P.r Bs.μsec q.1.2 ∈ Q.Glev P.k P.r (Fin.last P.r) :=
    Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_uwb Bs.sec hζ)
  have hGG : 0 < Q.GGl P.k P.r Bs.z Bs.z' (NF.muZ P.k P.r Bs.μsec q.1.2) := by
    unfold Q.GGl
    rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ Bs.z_mem Bs.z'_mem Bs.sec hζ]
    linarith
  have h := Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus Bs.z_mem Bs.z'_mem hc hG hGG
  exact ⟨hG, h.2, fun a => h.1 ⟨(a : ℕ) + 1, by omega⟩ (by show (a : ℕ) + 1 ≤ P.r; omega)⟩

theorem tc_famR (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hJ : J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (OmB Bs)) :
    FamR P Bs (fun c => {g | Q.wCell P.k P.r (Fin.last P.r) c * g ∈ OmB Bs})
      (Q.resG P.k P.r (Fin.last P.r) J) := by
  have hD : Q.IsDom P.k P.r Bs.z Bs.z' 0 (OmB Bs) := isDom_omP Bs.z_mem Bs.z'_mem
  refine ⟨?_, ?_, fun q => (tc_mu P Bs hpl q).2, ?_⟩
  · have hw : ContDiffOn ℝ ∞ (fun c : Fin P.r → ℂ => Q.wCell P.k P.r (Fin.last P.r) c) (OmX P.r) :=
      Formalism.FourierDecayAlt.P.Qx3.wlist_smooth _
    have hm : ContDiffOn ℝ ∞ (fun x : (Fin P.r → ℂ) × Q.Mx P.k P.r => Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2)
        {x | x.1 ∈ OmX P.r} :=
      Formalism.FourierDecayAlt.P.Qx3.cdo_mul (hw.comp contDiff_fst.contDiffOn (fun _ h => h)) contDiff_snd.contDiffOn
    exact hm.continuousOn.isOpen_inter_preimage Formalism.FourierDecayAlt.P.Qx3.isOpen_OmXX hD.1
  · intro c hc
    refine ⟨hD.1.preimage (continuous_const.matrix_mul continuous_id), ?_⟩
    rintro g ⟨hgG, hgD⟩ s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
    have hhm : h * m ∈ Q.Glev P.k P.r (Fin.last P.r) :=
      Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.uw_glev _ hh) hm.2
    have hcomm : Q.wCell P.k P.r (Fin.last P.r) c * (h * m) = (h * m) * Q.wCell P.k P.r (Fin.last P.r) c :=
      Formalism.FourierDecayAlt.P.Qx3.wlist_comm (Fin.last P.r) c _ (fun a _ => a.isLt) hhm
    have hwg : Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Q.Glev P.k P.r 0 :=
      Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _)
        (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hgG)
    have e : Q.wCell P.k P.r (Fin.last P.r) c * (h * m * g * (h' * m')) =
        h * m * (Q.wCell P.k P.r (Fin.last P.r) c * g) * (h' * m') := by
      rw [← Matrix.mul_assoc (Q.wCell P.k P.r (Fin.last P.r) c), ← Matrix.mul_assoc (Q.wCell P.k P.r (Fin.last P.r) c),
        hcomm, Matrix.mul_assoc (h * m)]
    show Q.wCell P.k P.r (Fin.last P.r) c * (h * m * g * (h' * m')) ∈ OmB Bs
    rw [e]
    exact hD.2 _ ⟨hwg, hgD⟩ _ ⟨h, hh, m, ⟨hm.1, Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hm.2⟩, rfl⟩ _
      ⟨h', hh', m', ⟨hm'.1, Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hm'.2⟩, rfl⟩
  · exact Formalism.FourierDecayAlt.P.restriction_good_family Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' (OmB Bs) Bs.z_mem Bs.z'_mem hD J hJ
      (Fin.last P.r)

end

theorem gauge_transition_chain_holds : GTrChain := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl _ J hJ
  refine ⟨tc_famR P Bs hpl J hJ, fun e ρ => tc_rawJ P Bs e J ρ, fun e ρ Y => ?_⟩
  rw [tc_rawJ]
  funext q
  have hmu := tc_mu P Bs hpl q
  have hcv := Formalism.FourierDecayAlt.P.capelli_vector_valued_all_levels Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' (Fin.last P.r) (OmB Bs) (Y : ℂ)
    Bs.z_mem Bs.z'_mem (isDom_omP Bs.z_mem Bs.z'_mem) J hJ q.1.1 q.2.1 _ hmu.1 hmu.2
  simp only [rawR, Finset.sum_apply]
  rw [hcv]
  simp only [Finset.sum_apply, tc_hsVec_sum, inner_sum, Finset.mul_sum, Fin.val_last]

end Formalism.FourierDecayAlt.P.CutMP.Gauge
