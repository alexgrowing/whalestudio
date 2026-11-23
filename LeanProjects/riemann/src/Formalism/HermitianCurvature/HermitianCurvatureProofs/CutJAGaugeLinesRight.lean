import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLinesCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeGRawSmooth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeGQLFam
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSConst
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSTr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL

noncomputable section

theorem gauge_right_line_holds : GLRight := by
  intro Wp Wq _ _ _ _ _ _ P Bs e hpl hk he hQQ ζ hζ Fr hFr X hX Y X' hX' ρ
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hT : 0 < Tz P.k P.r Bs.z := Bs.T_pos
  have hT' : 0 < Tz P.k P.r Bs.z' := Bs.T'_pos
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζ
  set c0 : Fin P.r → ℂ := fun _ => 1 with hc0def
  have hq : ((c0, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨fun _ => one_ne_zero, hζ'⟩
  set g := NF.muZ P.k P.r Bs.μsec ζ with hgdef
  let qq : MA.Qp P.r P.TT := ⟨(c0, ζ), ⟨fun _ => one_ne_zero, hζ⟩⟩
  have hw : 0 < Gauge.wR P.k P.TT ζ := Gauge.GC.SSTr.wR_pos P hζ
  set a : M.Ty P → ℂ := fun σ => ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e σ ζ)) (B.hsVec X) with hadef
  obtain ⟨Φs, -, hΦv⟩ := Gauge.GC.SSTr.exists_tr P Bs hpl hk e he (fun σ => algebraMap ℂ (MA.SmQ P.r P.TT) (a σ))
  set Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp) := (Φs : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) with hΦdef
  have hΦ : Φ ∈ Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := Φs.2
  have hval : Φ c0 g = X := by
    have h1 : Φ c0 g = _ := hΦv qq
    rw [h1]
    conv_rhs => rw [(he.2 ζ hζ).2.2 X hX]
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    have hw' : ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
    show (((Gauge.wR P.k P.TT ζ)⁻¹ : ℝ) : ℂ) * ((algebraMap ℂ (MA.SmQ P.r P.TT) (a σ) : MA.SmQ P.r P.TT) :
      MA.Qp P.r P.TT → ℂ) qq = _
    simp only [hadef, Subalgebra.coe_algebraMap, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    push_cast
    field_simp
  have hx : (c0, g) ∈ Q.DomR P.k P.r Bs.z Bs.z' := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq

  set Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r) := fun _ => Formalism.FourierDecayAlt.P.Qx5.Dp P.k P.r Bs.z Bs.z' with hDc
  have hFam : Gauge.FamR P Bs Dc Φ := by
    refine ⟨?_, fun c _ => Formalism.FourierDecayAlt.P.Qx5.Dp_dom P.k P.r Bs.z Bs.z', fun q => ?_, ?_,
      fun c hc => Formalism.FourierDecayAlt.P.Qx5.slice_FF hz hz' hΦ hc⟩
    · have h1 : IsOpen {x : (Fin P.r → ℂ) × Q.Mx P.k P.r | x.1 ∈ OmX P.r} := by
        have : IsOpen (OmX P.r) := by
          have e : OmX P.r = ⋂ l, {x : Fin P.r → ℂ | x l ≠ 0} := by ext x; simp [OmX]
          rw [e]
          exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
        exact this.preimage continuous_fst
      have h2 : IsOpen {x : (Fin P.r → ℂ) × Q.Mx P.k P.r | 0 < Q.GGl P.k P.r Bs.z Bs.z' x.2} :=
        isOpen_lt continuous_const ((Formalism.FourierDecayAlt.P.Qx5.GGl_continuous P.k P.r Bs.z Bs.z').comp continuous_snd)
      exact h1.inter h2
    · have hq' : ((q.1.1, q.1.2) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' :=
        ⟨q.2.1, by rw [hTz, hTz']; exact q.2.2⟩
      exact (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' Bs.sec hq').2.2
    · intro x₀ hx₀ hgl
      exact hΦ.2.1 x₀ ⟨hx₀.1, hgl, hx₀.2⟩
  have hG := hQQ Dc Φ hFam Y 1 1 ρ
  have hs1 := Gauge.raw_gauge_smoothness_holds Wp Wq P Bs hpl hk e he Dc _
    (Gauge.quadratic_local_family_holds Wp Wq P Bs hpl hk Dc Φ hFam Y 1 1) ρ
  have hs0 := Gauge.raw_gauge_smoothness_holds Wp Wq P Bs hpl hk e he Dc Φ hFam ρ

  have hQ11 : MA.QQr P (MA.DQ P) (Y : ℂ) 1 1 = MA.ggA P (MA.DQ P) * MA.xA P (MA.DQ P) (Y : ℂ) := rfl
  rw [hQ11, Gauge.actA_mul, MA.ggA, Gauge.GC.SSC.actA_sc, MA.xA] at hG
  have hev := congrArg (fun s : MA.SmQ P.r P.TT => (s : MA.Qp P.r P.TT → ℂ) qq) hG
  rw [Gauge.GC.toSm_of_mem P hs1, Gauge.GC.actA_kap] at hev
  have hw' : ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  have hGGv : Q.GGl P.k P.r Bs.z Bs.z' g = Complex.normSq ζ - P.TT := by
    unfold Q.GGl
    rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hz hz' Bs.sec hζ', hTz, hTz']
    rfl
  have hGG0 : ((Complex.normSq ζ - P.TT : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Complex.normSq ζ - P.TT := by linarith
    exact_mod_cast this.ne'
  have hsm : ∀ (c : ℂ) (A : Wq →L[ℂ] Wp), B.hsVec (c • A) = c • B.hsVec A := by
    intro c A; ext i; simp [B.hsVec]
  have hQLg : Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) 1 1 Φ c0 g =
      (((Complex.normSq ζ - P.TT : ℝ) : ℂ)) • X' := by
    ext v
    have ht := Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.top_level_pointwise_identity Formalism.FourierDecayAlt.P.capelli_two_by_two Formalism.FourierDecayAlt.P.right_type_action hz hz'
      (Formalism.FourierDecayAlt.P.Qx5.Dp_dom P.k P.r Bs.z Bs.z') Bs.π'_rep Bs.π'_cont
      (Formalism.FourierDecayAlt.P.Qx5.slice_FF hz hz' hΦ (fun _ => one_ne_zero)) ⟨hx.2.1, hx.2.2⟩ (ne_of_gt hx.2.2) Fr hFr (Y : ℂ) v
    show Q.tL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) 1 1 (Φ c0) g v = _
    rw [ht, hval, ← hX', hGGv, ContinuousLinearMap.smul_apply]
  have hL : Gauge.rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (↑Y) 1 1 Φ) ρ qq =
      ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * (((Complex.normSq ζ - P.TT : ℝ) : ℂ) *
        inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X')) := by
    show ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ ζ))
      (B.hsVec (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (↑Y) 1 1 Φ c0 g)) = _
    rw [hQLg, hsm, inner_smul_right]
  have h0 : Gauge.rawR P Bs.μsec e Φ ρ qq = ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X) := by
    show ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (Φ c0 g)) = _
    rw [hval]
  let Gq : MA.SmQ P.r P.TT := (MA.DQ P).gg P.TT
  let sq : MA.SmQ P.r P.TT := M.xC P ρ ↑Y • MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ)
  change _ = ((Gq * sq : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) qq at hev
  rw [Subalgebra.coe_mul, Pi.mul_apply] at hev
  have hgg : (Gq : MA.Qp P.r P.TT → ℂ) qq = ((Complex.normSq ζ - P.TT : ℝ) : ℂ) := by
    show MA.coordE M.vz qq.1 * MA.coordE M.vzb qq.1 - (P.TT : ℂ) = _
    simp [MA.coordE, MA.zE, M.vz, M.vzb, Complex.mul_conj, qq]
  have hsq : (sq : MA.Qp P.r P.TT → ℂ) qq = M.xC P ρ ↑Y * Gauge.rawR P Bs.μsec e Φ ρ qq := by
    show ((M.xC P ρ ↑Y • MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ) : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) qq = _
    rw [Subalgebra.coe_smul, Pi.smul_apply, Gauge.GC.toSm_of_mem P hs0, smul_eq_mul]
  rw [hgg, hsq, hL, h0] at hev
  have h3 : ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * (((Complex.normSq ζ - P.TT : ℝ) : ℂ) *
        inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X')) =
      ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * (((Complex.normSq ζ - P.TT : ℝ) : ℂ) *
        (M.xC P ρ ↑Y * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X))) := by
    rw [hev]; ring
  exact mul_left_cancel₀ hGG0 (mul_left_cancel₀ hw' h3)

end

end Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL
