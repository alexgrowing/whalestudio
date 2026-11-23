import Formalism.PeriodIntegrals.AmpOrbQ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitQuotientTopology.ContinuousAtInvOfDet

open Matrix MeasureTheory Measure
open scoped ENNReal

noncomputable section

namespace PI.AmpOrbQuot

open Formalism.QuantumDeterminants Formalism.MainNotions.S PI.AmpRootCommon

theorem muN_smul {k r : ℕ} (L : LocBessel k r) : L.μN = L.κN • haarLie (Nset k r) 1 := by
  rw [LocBessel.μN]
  unfold haarLie
  rw [one_smul]

theorem exists_isOrbQuot_of_isHaarOn {k r : ℕ} (L : LocBessel k r) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (μR : Measure (Mt k r)) (hg : g ∈ UH (Hpk k r)) (hμ : IsHaarOn (RStab k r g) μR)
    [SFinite L.μN] (hN : ∀ s ∈ Nset k r, L.μN.map (lmulM s) = L.μN) (hc : L.μN (NS k r)ᶜ = 0) :
    ∃ ν : Measure (PairSp k r), IsOrbQuot L g μR ν := by
  have : SigmaFinite μR := hμ.1
  have : IsFiniteMeasure L.μW := ⟨by rw [L.hμW.2]; exact ENNReal.one_lt_top⟩
  have : IsFiniteMeasure L.μW' := ⟨by rw [L.hμW'.2]; exact ENNReal.one_lt_top⟩
  have : SFinite (pairMeas L) := by unfold pairMeas; infer_instance
  obtain ⟨θ, hθ, hθ1⟩ := cutoff_exists hg hμ
  refine ⟨(pairMeas L).withDensity θ, fun f hf => ?_⟩
  have hJ : Measurable (fun p : Mt k r × PairSp k r => f (stabAct g (Matrix.of p.1) p.2)) :=
    hf.comp (measurable_stabAct g)
  have hin : Measurable (fun x : PairSp k r => ∫⁻ a, f (stabAct g (Matrix.of a) x) ∂μR) :=
    hJ.lintegral_prod_left'
  rw [lintegral_withDensity_eq_lintegral_mul _ hθ hin]
  have step1 : ∀ x : PairSp k r, (θ * fun x => ∫⁻ a, f (stabAct g (Matrix.of a) x) ∂μR) x =
      ∫⁻ a, θ x * f (stabAct g (Matrix.of a) x) ∂μR := by
    intro x
    simp only [Pi.mul_apply]
    have hmx : Measurable fun a : Mt k r => f (stabAct g (Matrix.of a) x) :=
      hJ.comp (f := fun a : Mt k r => (a, x)) (measurable_id.prodMk measurable_const)
    rw [lintegral_const_mul _ hmx]
  simp_rw [step1]
  have hm1 : Measurable (Function.uncurry fun (x : PairSp k r) (a : Mt k r) => θ x * f (stabAct g (Matrix.of a) x)) :=
    (hθ.comp measurable_fst).mul (hJ.comp (f := Prod.swap) measurable_swap)
  rw [lintegral_lintegral_swap hm1.aemeasurable]
  have step2 : ∀ a : Mt k r, Matrix.of a ∈ RStab k r g →
      ∫⁻ x, θ x * f (stabAct g (Matrix.of a) x) ∂(pairMeas L) =
        ∫⁻ y, θ (stabAct g (Matrix.of a)⁻¹ y) * f y ∂(pairMeas L) := by
    intro a ha
    have hh : Measurable fun y : PairSp k r => θ (stabAct g (Matrix.of a)⁻¹ y) * f y :=
      (hθ.comp (measurable_stabAct_one g _)).mul hf
    conv_rhs => rw [← pairMeas_inv L hN ha]
    rw [lintegral_map hh (measurable_stabAct_one g _)]
    refine lintegral_congr fun x => ?_
    rw [stabAct_inv_cancel hg ha.1.1]
  have hR : ∀ᵐ a ∂μR, Matrix.of a ∈ RStab k r g := ae_iff.2 hμ.2.2.1
  rw [lintegral_congr_ae (hR.mono step2)]
  have hm2 : Measurable (Function.uncurry fun (a : Mt k r) (y : PairSp k r) => θ (stabAct g (Matrix.of a)⁻¹ y) * f y) :=
    (hθ.comp (measurable_stabAct_inv g)).mul (hf.comp measurable_snd)
  rw [lintegral_lintegral_swap hm2.aemeasurable]
  have hNae : ∀ᵐ y ∂(pairMeas L), y.1.2 ∈ NS k r := ae_iff.2 (by
    have := pairMeas_null L hc
    simpa using this)
  refine lintegral_congr_ae (hNae.mono fun y hy => ?_)
  have hmy : Measurable fun a : Mt k r => θ (stabAct g (Matrix.of a)⁻¹ y) :=
    hθ.comp ((measurable_stabAct_inv g).comp (f := fun a : Mt k r => (a, y)) (measurable_id.prodMk measurable_const))
  show f y = ∫⁻ a, θ (stabAct g (Matrix.of a)⁻¹ y) * f y ∂μR
  rw [lintegral_mul_const _ hmy, hθ1 y hy, one_mul]

end PI.AmpOrbQuot

open Formalism.QuantumDeterminants Formalism.MainNotions.S PI.AmpRootCommon PI.AmpOrbQuot in
theorem orbQuotEx_of_haarLieN (h : PI.AmpOrbQ.HaarLieN) : PI.AmpOrbQ.OrbQuotEx := by
  intro k r L p g₀ μR hpt _ hμ
  obtain ⟨hsf, _, hnull, hinv⟩ := h k r 1 one_ne_zero ENNReal.one_ne_top
  have e := muN_smul L
  haveI := hsf
  haveI : SFinite L.μN := by rw [e]; infer_instance
  refine exists_isOrbQuot_of_isHaarOn L g₀ μR hpt.1 hμ ?_ ?_
  · intro s hs
    rw [e, Measure.map_smul, hinv s hs]
  · rw [e, Measure.smul_apply]
    have h0 : haarLie (Nset k r) 1 (NS k r)ᶜ = 0 := hnull
    rw [h0, smul_eq_mul, mul_zero]
