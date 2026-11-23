import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPtRepTrDat
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.JEqOrbInt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplifierOfHypotheses
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapDimensionFormula
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
noncomputable section

namespace GlobalTheory.AmpTKOne

open GlobalTheory.AmpOrb GlobalTheory.CellOrbInt GlobalTheory.AmpTK

variable {k r : ℕ}

theorem fdeg_ne_zero (H : BranchingSupport.Hyps) (L : LocBessel k r) {μG : Measure (Mt k r)} (hμ : IsHaarOn (UH (Hpk k r)) μG)
    {w : L.Hs} (hw : w ≠ 0) : (PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ) ≠ 0 := by
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.BesselDegree.schur_fdeg H k r L.ε μG hμ
  obtain ⟨hd, -⟩ := hc L.lam (rep L) ⟨L.hlam, L.hσ⟩
  have e : PI.BesselPeriodGGP.fdegH μG L.σ w = c * fdegHC L.lam := hd w hw
  rw [e]
  exact_mod_cast (mul_pos hc0 (GlobalTheory.BesselNorm.fdegHC_pos L.lam L.hlam.1.injective)).ne'

theorem besselIntg_sum (L : LocBessel k r) {ι : Type} (s : Finset ι)
    (F : ι → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (p : PairSp k r) :
    besselIntg L (fun q => ∑ a ∈ s, F a q) g p = ∑ a ∈ s, besselIntg L (F a) g p := by
  ext η
  simp [besselIntg, ContinuousLinearMap.sum_apply, map_sum, Finset.smul_sum]

theorem ampTK_pt (H : BranchingSupport.Hyps) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (l : L.Hs → L.Wp)
    (l' : L.Hs → L.Wq) (hgap : GapAtLeast L.ε L.lam h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h)
    (hμ : IsHaarOn (UH (Hpk k r)) μG) (hBe : BeTK L l l') {w : L.Hs} (hw1 : ‖w‖ = 1)
    (hwK : PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ w)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
    (ν : Measure (PairSp k r)) (hγ : γ ∈ UH (Hpk k r)) (hrel : IsRelStab L γ) (hR : IsHaarOn (RStab k r γ) μR)
    (hQ : IsOrbQuot L γ μR ν)
    (hQG : PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR)
    (b : ℝ) (hb0 : 0 ≤ b) (hb : Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b)
    (hint : Integrable (pairMaj γ b) ν) {v v' : L.Hs} (hv : v ∈ (rep L).TK) (hv' : v' ∈ (rep L).TK)
    (ξ : L.Wp) (ξ' : L.Wq) :
    Integrable (besselIntg L (coefF L v v' ξ ξ') γ) ν ∧
      (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • ampJ νR 1 (fun g => l (L.σ g w)) (fun g => l' (L.σ g w)) γ =
        ((PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ)⁻¹) • OrbInt L (coefF L v v' ξ ξ') γ ν := by
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  have hDS : (rep L).IsDS L.ε L.lam := ⟨L.hlam, hσ⟩
  obtain ⟨hmul, hone, huni, hsmg, hTKsm, -, hKT, -, -⟩ := GlobalTheory.rep_basic_of_isDS H.1.2.2.1 k r L.ε L.lam (rep L) hDS
  have hsm : w ∈ (rep L).sm := hTKsm w (hKT w hwK)
  obtain ⟨C, Ws, -, hC⟩ := GlobalTheory.BesselDecay.decay_TK H k r L.ε L.lam h (rep L) hDS hgap hok v hv
  obtain ⟨C', Ws', -, hC'⟩ := GlobalTheory.BesselDecay.decay_TK H k r L.ε L.lam h (rep L) hDS hgap hok v' hv'
  have hw0 : w ≠ 0 := fun h0 => by simp [h0] at hw1
  obtain ⟨c, -, hc⟩ := GlobalTheory.BesselDegree.schur_fdeg H k r L.ε μG hμ
  obtain ⟨hd, hS⟩ := hc L.lam (rep L) hDS
  have hd' : PI.BesselPeriodGGP.fdegH μG L.σ w = c * fdegHC L.lam := hd w hw0
  have hS' : ∀ y y' : L.Hs, ∫ x, ⟪y, L.σ (Matrix.of x) w⟫_ℂ * star ⟪y', L.σ (Matrix.of x) w⟫_ℂ ∂μG =
      (PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ)⁻¹ * ⟪y, y'⟫_ℂ := fun y y' => by
    refine (hS w y w y').2.trans ?_
    have : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw1]; simp
    rw [hd']
    show ⟪w, w⟫_ℂ * ⟪y, y'⟫_ℂ / _ = _
    rw [this, one_mul, div_eq_inv_mul]
  have hfd := fdeg_ne_zero H L hμ hw0
  haveI : SigmaFinite μG := hμ.1
  haveI : SigmaFinite μR := hR.1
  haveI : SFinite (pairMeas L) := by
    have : SFinite L.μN := by unfold LocBessel.μN haarLie; infer_instance
    have : SigmaFinite L.μW := L.hμW.1.1
    have : SigmaFinite L.μW' := L.hμW'.1.1
    unfold pairMeas; infer_instance
  have aG : ∀ᵐ y ∂μG, Matrix.of y ∈ UH (Hpk k r) := by rw [ae_iff]; exact hμ.2.2.1
  have aR : ∀ᵐ y ∂μR, Matrix.of y ∈ RStab k r γ := by rw [ae_iff]; exact hR.2.2.1
  have aν := ae_quot L hR hQ
  haveI : SFinite ν := sfinite_of_lintegral ν (fun p => ‖pairMaj γ b p‖ₑ) hint.1.enorm
    (aν.mono fun p hp => by
      have : 0 < pairMaj γ b p :=
        Real.rpow_pos_of_pos (one_pos.trans_le (PI.PolynomialProperness.GN.gN_ge_one (point_mem L hγ hp))) _
      simpa using this.ne') hint.2.ne
  have hRc := Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (hG.unit _ hγ)
  have hinv : μR.map GlobalTheory.SgInf.invM = μR :=
    (GlobalTheory.UnipUnimod.isUnimod_of_subset_Nset (S := RStab k r γ)
      ⟨fun a ha => ha.1.1, hRc.closed, hRc.one_mem, hRc.mul_mem, hRc.inv_mem⟩ (fun a ha => ha.1) hR).2
  have mi : Measurable (GlobalTheory.SgInf.invM (k := k) (r := r)) := Formalism.FourierDecayAlt.P.B7.measurable_invM
  let cj : Mt k r → Mt k r := fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j
  have mc : Measurable cj :=
    meas_mul (g := fun _ => γ) (meas_mul (f := fun _ => (γ⁻¹ : MatKR k r)) measurable_const measurable_id)
      measurable_const
  let a₂ : Mt k r → Mt k r → Mt k r := fun a x => Matrix.of.symm (γ⁻¹ * (Matrix.of a)⁻¹ * γ * Matrix.of x)
  have m2 : Measurable fun q : Mt k r × Mt k r => a₂ q.2 q.1 :=
    meas_mul (mc.comp (mi.comp measurable_snd)) measurable_fst
  have hW2 : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ a, f (a₂ a x) ∂μR) ∂νR := by
    intro f hf
    rw [hQG f hf]
    refine lintegral_congr fun x => ?_
    have mf : Measurable fun s : Mt k r => f fun i j => (Matrix.of s * Matrix.of x) i j :=
      hf.comp (meas_mul measurable_id measurable_const)
    rw [lintegral_map mf mc]
    conv_lhs => rw [← hinv]
    rw [lintegral_map (f := fun s => f fun i j => (Matrix.of (cj s) * Matrix.of x) i j) (mf.comp mc) mi]
    rfl
  haveI : SFinite νR := sfinite_of_weil μG νR μR hR.2.1 a₂ m2 hW2
  have m1 : Measurable fun q : PairSp k r × Mt k r => stabAct γ (Matrix.of q.2) q.1 :=
    (measurable_fst.fst.fst.prodMk (meas_mul measurable_snd measurable_fst.fst.snd)).prodMk
      (measurable_fst.snd.fst.prodMk (meas_mul (mc.comp measurable_snd) measurable_fst.snd.snd))
  have hcl : IsClosed {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} := hG.closed
  have aνR : ∀ᵐ x ∂νR, Matrix.of x ∈ UH (Hpk k r) := by
    refine ae_of_weil μG νR μR a₂ _ hcl.measurableSet aG hR.2.1 hW2 ?_
    filter_upwards [aR] with a ha x hx
    have h1 := hG.mul_mem _ (hG.mul_mem _ (hG.inv_mem _ hγ) _ (hG.inv_mem _ ha.1.1)) _ hγ
    have h3 : γ⁻¹ * (Matrix.of a)⁻¹ * γ * Matrix.of x ∈ UH (Hpk k r) := hx
    have h2 := hG.mul_mem _ (hG.inv_mem _ h1) _ h3
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ (hG.unit _ h1)] at h2
    exact h2
  have hI := integrable_ker L hγ w v v' ξ ξ' hμ aν (e := Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1) hb0 (by linarith) hint
    (fun x hx => by rw [neg_sub]; exact hC w hsm x hx) (fun x hx => by rw [neg_sub]; exact hC' w hsm x hx)
  have hgrp : ∀ᵐ p ∂ν, ∫ x, ker L γ w v v' ξ ξ' (p, x) ∂μG =
      (PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ)⁻¹ • besselIntg L (coefF L v v' ξ ξ') γ p := by
    filter_upwards [aν] with p hp
    exact integral_ker_group L hγ hmul hone huni aG hS' v v' ξ ξ' hp
  refine ⟨(hI.integral_prod_left.smul (PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ)).congr ?_, ?_⟩
  · filter_upwards [hgrp] with p hp
    rw [Pi.smul_apply, hp, smul_smul, mul_inv_cancel₀ hfd, one_smul]
  have key := double_weil (pairMeas L) ν μG νR μR (fun a p => stabAct γ (Matrix.of a) p) a₂
    (mp_of_weil _ _ _ (fun a p => stabAct γ (Matrix.of a) p) m1 hQ) (mp_of_weil _ _ _ a₂ m2 hW2)
    (ker L γ w v v' ξ ξ') (aesm_ker L hγ w v v' ξ ξ' _ _ (ae_pairMeas L) aνR) hI (by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae ((Measure.quasiMeasurePreserving_fst.ae aν).and
        (Measure.quasiMeasurePreserving_snd.ae aR))] with t ht
      exact ker_act L hγ hrel w v v' ξ ξ' ht.2 ht.1 t.2)
  unfold ampJ OrbInt
  rw [Complex.ofReal_one, inv_one, one_smul, ← integral_smul, ← integral_smul]
  refine Eq.trans (integral_congr_ae ?_) (key.trans (integral_congr_ae ?_))
  · filter_upwards [aνR] with x hx
    rw [integral_ker_pair L hok.1 hγ hmul w v v' ξ ξ' hx,
      hBe.1 (L.σ (γ * Matrix.of x) w) (hsmg _ (hG.mul_mem _ hγ _ hx) w hsm) v hv,
      hBe.2 (L.σ (Matrix.of x) w) (hsmg _ hx w hsm) v' hv']
    ext η
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul,
      inner_smul_left, inner_conj_symm]
    congr 1
    ring
  · exact hgrp

theorem oneAt : BranchingSupport.Hyps → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ) (μG : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r)) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq), Formalism.QuantumDeterminants.GapAtLeast L.ε L.lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → L.c ≠ 0 → IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → GlobalTheory.AmpTK.BeTK L l l' → ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r)) (ν : MeasureTheory.Measure (Formalism.MainNotions.S.PairSp k r)), γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → Formalism.MainNotions.S.IsRelStab L γ → IsHaarOn (Formalism.MainNotions.S.RStab k r γ) μR → Formalism.MainNotions.S.IsOrbQuot L γ μR ν → PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR → ∀ b : ℝ, 0 ≤ b → Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b → MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj γ b) ν → GlobalTheory.AmpTK.OneAt L l l' γ ν := by
  intro H k r L h μG l l' hgap hok _ hμ hBe γ μR νR ν hγ hrel hR hQ hQG b hb0 hb hint
  obtain ⟨-, -, -, -, -, -, -, ⟨w, hw1, hwK, -⟩, -⟩ :=
    GlobalTheory.rep_basic_of_isDS H.1.2.2.1 k r L.ε L.lam (rep L) ⟨L.hlam, L.hσ⟩
  have hw0 : w ≠ 0 := fun h0 => by simp [h0] at hw1
  have hfd := fdeg_ne_zero H L hμ hw0
  have key : ∀ {v v' : L.Hs}, v ∈ (rep L).TK → v' ∈ (rep L).TK → ∀ (ξ : L.Wp) (ξ' : L.Wq),
      Integrable (besselIntg L (coefF L v v' ξ ξ') γ) ν ∧
      (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • ampJ νR 1 (fun g => l (L.σ g w)) (fun g => l' (L.σ g w)) γ =
        ((PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ)⁻¹) • OrbInt L (coefF L v v' ξ ξ') γ ν :=
    fun hv hv' ξ ξ' =>
      ampTK_pt H L h μG l l' hgap hok hμ hBe hw1 hwK γ μR νR ν hγ hrel hR hQ hQG b hb0 hb hint hv hv' ξ ξ'
  refine ⟨(PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ) •
    ampJ νR 1 (fun g => l (L.σ g w)) (fun g => l' (L.σ g w)) γ, ?_⟩
  rintro F s ⟨m, x, y, X, hxy, hF, rfl⟩
  have hc : ∀ i (ξ : L.Wp) (ξ' : L.Wq), OrbInt L (coefF L (x i) (y i) ξ ξ') γ ν =
      (⟪l (x i), ξ⟫_ℂ * ⟪ξ', l' (y i)⟫_ℂ) • (PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ) •
        ampJ νR 1 (fun g => l (L.σ g w)) (fun g => l' (L.σ g w)) γ := by
    intro i ξ ξ'
    rw [smul_comm, (key (hxy i).1 (hxy i).2 ξ ξ').2, smul_smul, mul_inv_cancel₀ hfd, one_smul]
  let e := stdOrthonormalBasis ℂ L.Wq
  have hX : ∀ T : L.Wq →L[ℂ] L.Wp, T = ∑ j, (innerSL ℂ (e j)).smulRight (T (e j)) := by
    intro T
    ext η
    conv_lhs => rw [← e.sum_repr' η]
    simp [ContinuousLinearMap.sum_apply, map_sum]
  have hFe : ∀ g ∈ UH (Hpk k r), F g = ∑ i, ∑ j, coefF L (x i) (y i) (X i (e j)) (e j) g := by
    intro g hg
    rw [hF g hg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_congr rfl fun j _ => coefF_eq L (x i) (y i) (X i (e j)) (e j) g, ← Finset.smul_sum]
    exact congrArg₂ (· • ·) rfl (hX (X i))
  have hae : ∀ᵐ p ∂ν, besselIntg L F γ p =
      ∑ i, ∑ j, besselIntg L (coefF L (x i) (y i) (X i (e j)) (e j)) γ p := by
    filter_upwards [ae_quot L hR hQ] with p hp
    have e1 : besselIntg L F γ p =
        besselIntg L (fun g => ∑ i, ∑ j, coefF L (x i) (y i) (X i (e j)) (e j) g) γ p := by
      unfold besselIntg
      rw [hFe _ (point_mem L hγ hp)]
    rw [e1]
    exact (besselIntg_sum L Finset.univ (fun i g => ∑ j, coefF L (x i) (y i) (X i (e j)) (e j) g) γ p).trans
      (Finset.sum_congr rfl fun i _ =>
        besselIntg_sum L Finset.univ (fun j g => coefF L (x i) (y i) (X i (e j)) (e j) g) γ p)
  have hi : ∀ i j, Integrable (besselIntg L (coefF L (x i) (y i) (X i (e j)) (e j)) γ) ν :=
    fun i j => (key (hxy i).1 (hxy i).2 _ _).1
  have e2 : OrbInt L F γ ν = ∑ i, ∑ j, OrbInt L (coefF L (x i) (y i) (X i (e j)) (e j)) γ ν := by
    unfold OrbInt
    rw [integral_congr_ae hae, integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hi i j]
    exact Finset.sum_congr rfl fun i _ => integral_finset_sum _ fun j _ => hi i j
  rw [e2, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hc]
  rw [← Finset.sum_smul]
  congr 1
  conv_rhs => rw [← e.sum_repr' (l' (y i)), map_sum, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, inner_smul_right, mul_comm]

end GlobalTheory.AmpTKOne
