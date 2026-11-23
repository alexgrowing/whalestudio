import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.QuotTrHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinCut

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal Pointwise

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.LocWSOf Formalism.MainNotions.S

section Gen

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {v : InfinitePlace X.B.I.F} {lam : ℂ}
  {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ} {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ}

theorem trHyp_gen (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi) (u : D.what₂.Word) :
    Formalism.L2.SG.Pf.Bridge.TrHyp (PtRepPf.frU X u v) Q Qi (fun a : Fin D.R.rS => lam ^ (D.R.rS - (a : ℕ))) := by
  obtain ⟨h1, h2, hH, hef⟩ := hT
  exact ⟨h1, h2, hH, fun a => (hef a a rfl).1, fun a => (hef a a rfl).2⟩

theorem trG_mul_g (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi) (a b : Formalism.REAL.UJ (X.B.I.ε v)) :
    trG Q Qi (a * b) = trG Q Qi a * trG Q Qi b := by
  obtain ⟨-, h2, -, -⟩ := hT
  unfold trG
  rw [Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul]
  calc Qi * (uMat a * uMat b) * Q = Qi * uMat a * (Q * Qi) * uMat b * Q := by
        rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem trG_inv_g (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi) (γ : Formalism.REAL.UJ (X.B.I.ε v)) :
    (trG Q Qi γ)⁻¹ = trG Q Qi γ⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [← trG_mul_g hT, mul_inv_cancel]
  obtain ⟨h1, -, -, -⟩ := hT
  show Qi * uMat (1 : Formalism.REAL.UJ (X.B.I.ε v)) * Q = 1
  simp [uMat, h1]

theorem transp_mem_g (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi) {m : Matrix (Fin (2 * D.R.rS + D.R.k + 1))
    (Fin (2 * D.R.rS + D.R.k + 1)) ℂ} (hm : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    Q * m * Qi ∈ UJset (X.B.I.ε v) := by
  obtain ⟨hQiQ, hQQi, hH, _⟩ := hT
  have hm' : mᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * m = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hm
  show (Q * m * Qi)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (Q * m * Qi) = Formalism.REAL.Jm (X.B.I.ε v)
  have e1 : (Q * m * Qi)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (Q * m * Qi) =
      Qiᴴ * (mᴴ * (Qᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Q) * m) * Qi := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e1, hH, hm', ← hH]
  have e2 : Qiᴴ * (Qᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Q) * Qi = (Q * Qi)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (Q * Qi) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e2, hQQi, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

variable (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi) (u u' : D.what₂.Word) (γ : Formalism.REAL.UJ (X.B.I.ε v))
  (μRv : Measure (Formalism.REAL.UJ (X.B.I.ε v)))
include hT

theorem emb_g : Topology.IsClosedEmbedding
    (fun x : Formalism.REAL.UJ (X.B.I.ε v) => (Matrix.of.symm (trG Q Qi x) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
  Formalism.L2.SG.Pf.WuBL.trG_closedEmb' n_eq _ hT.2.1

theorem haar_measure_transport_invariant (hH : IsHaarLoc (StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u v)
      (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' v) γ) μRv) :
    (μRv.map (fun x => Matrix.of.symm (trG Q Qi x))) (Formalism.FourierDecayAlt.C6.Rset (trG Q Qi γ))ᶜ = 0 ∧
    (∀ a ∈ Formalism.FourierDecayAlt.C6.Rset (trG Q Qi γ),
      (μRv.map (fun x => Matrix.of.symm (trG Q Qi x))).map (Formalism.QuantumDeterminants.lmulM a) = μRv.map (fun x => Matrix.of.symm (trG Q Qi x))) ∧
    μRv.map (fun x => Matrix.of.symm (trG Q Qi x)) ≠ 0 := by
  obtain ⟨hσ, hne, hconc, hinv⟩ := hH
  have h1 := hT.1
  have h2 := hT.2.1
  have hTu := trHyp_gen hT u
  have hTu' := trHyp_gen hT u'
  set F : Formalism.REAL.UJ (X.B.I.ε v) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS := fun x => Matrix.of.symm (trG Q Qi x) with hF
  have hme : MeasurableEmbedding F := (emb_g hT).measurableEmbedding
  have hU : ∀ y : Formalism.REAL.UJ (X.B.I.ε v), (uMat y)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * uMat y = Formalism.REAL.Jm (X.B.I.ε v) :=
    fun y => y.2
  have hfwd : ∀ y ∈ StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u v) (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' v) γ,
      trG Q Qi y ∈ Formalism.FourierDecayAlt.C6.Rset (trG Q Qi γ) := by
    rintro y ⟨hy1, hy2⟩
    refine ⟨Formalism.L2.SG.Pf.Bridge.fwd_N hTu (hU y) hy1, ?_⟩
    rw [trG_inv_g hT, ← trG_mul_g hT, ← trG_mul_g hT]
    exact Formalism.L2.SG.Pf.Bridge.fwd_N hTu' (hU _) hy2
  refine ⟨?_, ?_, ?_⟩
  · rw [hme.map_apply]
    refine measure_mono_null (fun y hy => ?_) hconc
    intro hyS
    exact hy (hfwd y hyS)
  · intro s hs
    obtain ⟨hsN, hsN'⟩ := hs
    have hmem := transp_mem_g hT hsN.1
    set y0 := Formalism.L2.SG.Pf.LocJEq.ujOf' (Q * s * Qi) hmem with hy0
    have hy0S : y0 ∈ StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u v) (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' v) γ := by
      refine ⟨Formalism.L2.SG.Pf.Bridge.inN_Q hTu hsN, ?_⟩
      show Formalism.L2.SG.HidaSetting.InN _ _ _ (uMat (γ⁻¹ * y0 * γ))
      have e : uMat (γ⁻¹ * y0 * γ) = Q * ((trG Q Qi γ)⁻¹ * s * trG Q Qi γ) * Qi := by
        rw [trG_inv_g hT]
        show uMat (γ⁻¹ * y0 * γ) = Q * (Qi * uMat γ⁻¹ * Q * s * (Qi * uMat γ * Q)) * Qi
        rw [Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul, Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.uMat_mul]
        show uMat γ⁻¹ * (Q * s * Qi) * uMat γ = _
        simp only [← Matrix.mul_assoc]
        rw [h2, Matrix.one_mul]
        simp only [Matrix.mul_assoc]
        rw [h2, Matrix.mul_one]
      rw [e]
      exact Formalism.L2.SG.Pf.Bridge.inN_Q hTu' hsN'
    have hcomp : (Formalism.QuantumDeterminants.lmulM s) ∘ F = F ∘ (fun x => y0 * x) := by
      funext x
      simp only [Function.comp, hF, Formalism.QuantumDeterminants.lmulM, Matrix.of_symm_apply]
      rw [trG_mul_g hT]
      congr 1
      show s = Qi * (Q * s * Qi) * Q
      simp only [← Matrix.mul_assoc]
      rw [h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
    have hcont_l : Measurable (Formalism.QuantumDeterminants.lmulM (k := D.R.k) (r := D.R.rS) s) := by
      have : Continuous (Formalism.QuantumDeterminants.lmulM (k := D.R.k) (r := D.R.rS) s) := by
        unfold Formalism.QuantumDeterminants.lmulM
        exact continuous_const.matrix_mul continuous_id
      exact this.measurable
    rw [Measure.map_map hcont_l hme.measurable, hcomp,
      ← Measure.map_map hme.measurable (continuous_mul_left y0).measurable, hinv y0 hy0S]
  · intro h0
    apply hne
    have h := congrArg (fun m : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) => m Set.univ) h0
    simp only [Measure.coe_zero, Pi.zero_apply] at h
    rw [hme.map_apply, Set.preimage_univ] at h
    exact Measure.measure_univ_eq_zero.1 h

theorem fin_g (ν : Measure (Formalism.REAL.UJ (X.B.I.ε v))) (hq : IsQuotLoc μRv ν) (K : Set (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS))
    (hK : IsCompact K) : (μRv.map (fun x => Matrix.of.symm (trG Q Qi x))) K < ∞ := by
  have hemb := emb_g hT
  rw [hemb.measurableEmbedding.map_apply]
  set Cc := (fun x : Formalism.REAL.UJ (X.B.I.ε v) => (Matrix.of.symm (trG Q Qi x) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) ⁻¹' K
  have hC : IsCompact Cc := hemb.isCompact_preimage hK

  have hν : ν ≠ 0 := by
    intro h0
    have h := hq (fun _ => 1) measurable_const
    rw [h0] at h
    simp only [lintegral_const, Measure.coe_zero, Pi.zero_apply, mul_zero, lintegral_zero_measure] at h
    have : Formalism.REAL.muG (X.B.I.ε v) Set.univ = 0 := by simpa using h
    exact (isOpen_univ.measure_pos (Formalism.REAL.muG (X.B.I.ε v)) Set.univ_nonempty).ne' this

  obtain ⟨m, hm⟩ : ∃ m, 0 < ν (compactCovering (Formalism.REAL.UJ (X.B.I.ε v)) m) := by
    by_contra hcon
    push_neg at hcon
    apply hν
    rw [← Measure.measure_univ_eq_zero, ← iUnion_compactCovering]
    exact measure_iUnion_null fun m => nonpos_iff_eq_zero.1 (hcon m)
  set V := compactCovering (Formalism.REAL.UJ (X.B.I.ε v)) m
  have hV : IsCompact V := isCompact_compactCovering _ m
  have hCV : IsCompact (Cc * V) := hC.mul hV
  have hfin : Formalism.REAL.muG (X.B.I.ε v) (Cc * V) < ∞ := hCV.measure_lt_top
  have hmeas : MeasurableSet (Cc * V) := hCV.isClosed.measurableSet
  have hW := hq ((Cc * V).indicator 1) (measurable_one.indicator hmeas)
  rw [lintegral_indicator_one hmeas] at hW
  have hlow : μRv Cc * ν V ≤ ∫⁻ x, (∫⁻ s, (Cc * V).indicator 1 (s * x) ∂μRv) ∂ν := by
    rw [← lintegral_indicator_const (hV.isClosed.measurableSet)]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ V
    · rw [Set.indicator_of_mem hx, ← lintegral_indicator_one hC.isClosed.measurableSet]
      refine lintegral_mono fun s => ?_
      by_cases hs : s ∈ Cc
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (Set.mul_mem_mul hs hx)]; exact le_rfl
      · rw [Set.indicator_of_notMem hs]; exact bot_le
    · rw [Set.indicator_of_notMem hx]; exact bot_le
  rw [← hW] at hlow
  by_contra hinf
  rw [not_lt, top_le_iff] at hinf
  rw [hinf, ENNReal.top_mul hm.ne'] at hlow
  exact absurd (lt_of_le_of_lt hlow hfin) (lt_irrefl _)

end Gen

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ)

theorem haarAtC_holds (u u' : D.what₂.Word) (τ : D.what₂.Tau) : HaarAtC C u u' τ := by
  intro γ μRv ν hP
  obtain ⟨-, -, -, hH, hq⟩ := hP
  have hT := Formalism.L2.SG.Pf.BaseOf.transpC X C (vOf X τ)
  obtain ⟨hc, hl, hne⟩ := haar_measure_transport_invariant hT u u' γ μRv hH
  exact ⟨hc, hl, fun K hK => fin_g hT μRv ν hq K hK, hne⟩

end Formalism.L2.SG.Pf.Carrier.CarPinTor
