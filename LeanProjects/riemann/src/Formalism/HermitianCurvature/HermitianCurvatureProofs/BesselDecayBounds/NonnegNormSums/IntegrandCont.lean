import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.NonnegNormSums.SumNonnegNorms
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvMeas
import Formalism.SharpRestriction.CuspSpanNormBounds.KfinOfMemLowKSub

open MeasureTheory Matrix Finset Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.Cv.BeC

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL PI.WBL.Cv

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

def DecInf (σ : Mx k r → (H →L[ℂ] H)) (a : ℝ) : Prop := PtDec σ a (fun v => IsKFinHpk (k := k) (r := r) σ v)

def VDK (σ : Mx k r → (H →L[ℂ] H)) (w0 v : H) : Prop :=
  v ∈ Formalism.MainNotions.BridgeLemma₄.DDsp σ w0 ∨ IsKFinHpk (k := k) (r := r) σ v

def BeConvAt (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)) (w0 : H) : Prop :=
  (∀ u ∈ smoothVecs (k := k) (r := r) σ, ∀ v : H, VDK σ w0 v → Integrable (beF z c π σ u v) (μW.prod μN)) ∧
  (∀ v : H, VDK σ w0 v → ∀ x : Wp, IsCWCont (k := k) (r := r) σ (fun u => be z c π μW μN σ u v x)) ∧
  (∀ h ∈ UWset k r z, ∀ m ∈ Nset k r, ∀ u ∈ smoothVecs (k := k) (r := r) σ, ∀ v : H, VDK σ w0 v →
    be z c π μW μN σ (σ (h * m) u) v = (psi k r z c m • π h).comp (be z c π μW μN σ u v)) ∧
  (∀ h ∈ UWset k r z, ∀ m ∈ Nset k r, ∀ u : H, VDK σ w0 u → ∀ v ∈ smoothVecs (k := k) (r := r) σ,
    be z c π μW μN σ u (σ (h * m) v) =
      (be z c π μW μN σ u v).comp (ContinuousLinearMap.adjoint (psi k r z c m • π h))) ∧
  (∀ u : H, VDK σ w0 u → ∀ v ∈ smoothVecs (k := k) (r := r) σ,
    ContinuousLinearMap.adjoint (be z c π μW μN σ u v) = be z c π μW μN σ v u) ∧
  (∀ u ∈ smoothVecs (k := k) (r := r) σ, ∀ v : H, VDK σ w0 v →
    ContinuousOn (fun x => be z c π μW μN σ (σ x u) v) (UH (Hpk k r)))

theorem coef_aesm (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)) (hG : GrpF k r z) (hM : MeasF z π μW μN)
    (hcont : ∀ w : H, ContinuousOn (fun g => σ g w) (UH (Hpk k r))) (v w : H) :
    AEStronglyMeasurable (fun p : Mt k r × Mt k r => ⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ) (μW.prod μN) := by
  have hmem : ∀ᵐ p ∂(μW.prod μN), p ∈ (fun p : Mt k r × Mt k r => (Matrix.of p.1 * Matrix.of p.2 : Mx k r)) ⁻¹'
      UH (Hpk k r) := by
    filter_upwards [hM.1] with p hp
    exact hG.1 _ hp.1.1 _ hp.2.1
  have hT : MeasurableSet ((fun p : Mt k r × Mt k r => (Matrix.of p.1 * Matrix.of p.2 : Mx k r)) ⁻¹'
      UH (Hpk k r)) := (isClosed_UH.preimage continuous_matrix_mul).measurableSet
  have hcoT : ContinuousOn (fun p : Mt k r × Mt k r => ⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ)
      ((fun p : Mt k r × Mt k r => (Matrix.of p.1 * Matrix.of p.2 : Mx k r)) ⁻¹' UH (Hpk k r)) :=
    continuousOn_const.inner ((hcont w).comp continuous_matrix_mul.continuousOn (fun p hp => hp))
  have h := hcoT.aestronglyMeasurable (μ := μW.prod μN) hT
  rwa [Measure.restrict_eq_self_of_ae_mem hmem] at h

theorem gN_rpow_le {a : ℝ} (ha : 1 ≤ a) {P Q R : Mx k r} (hP : 0 < Formalism.FourierDecayAlt.B.gN P) (hQ : 0 < Formalism.FourierDecayAlt.B.gN Q)
    (hR : 0 < Formalism.FourierDecayAlt.B.gN R) (hle : Formalism.FourierDecayAlt.B.gN R ≤ Formalism.FourierDecayAlt.B.gN P * Formalism.FourierDecayAlt.B.gN Q) :
    Formalism.FourierDecayAlt.B.gN Q ^ (1 - a) ≤ Formalism.FourierDecayAlt.B.gN P ^ (a - 1) * Formalism.FourierDecayAlt.B.gN R ^ (1 - a) := by
  have h1 : (Formalism.FourierDecayAlt.B.gN P * Formalism.FourierDecayAlt.B.gN Q) ^ (1 - a) ≤ Formalism.FourierDecayAlt.B.gN R ^ (1 - a) :=
    Real.rpow_le_rpow_of_nonpos hR hle (by linarith)
  rw [Real.mul_rpow hP.le hQ.le] at h1
  have h2 : Formalism.FourierDecayAlt.B.gN P ^ (a - 1) * Formalism.FourierDecayAlt.B.gN P ^ (1 - a) = 1 := by
    rw [← Real.rpow_add hP]
    ring_nf
    simp
  calc Formalism.FourierDecayAlt.B.gN Q ^ (1 - a)
      = Formalism.FourierDecayAlt.B.gN P ^ (a - 1) * (Formalism.FourierDecayAlt.B.gN P ^ (1 - a) * Formalism.FourierDecayAlt.B.gN Q ^ (1 - a)) := by
        rw [← mul_assoc, h2, one_mul]
    _ ≤ Formalism.FourierDecayAlt.B.gN P ^ (a - 1) * Formalism.FourierDecayAlt.B.gN R ^ (1 - a) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hP.le _)

instance fcMx : FirstCountableTopology (Mx k r) :=
  inferInstanceAs (FirstCountableTopology (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))

def finv (k r : ℕ) (a : ℝ) (x : Mx k r) : ℝ := Formalism.FourierDecayAlt.B.gN (Hpk k r * xᴴ * Hpk k r) ^ (a - 1)

theorem finv_cont (a : ℝ) (ha : 1 ≤ a) : Continuous (finv k r a) := by
  have hc : Continuous (fun x : Mx k r => Hpk k r * xᴴ * Hpk k r) :=
    (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
  exact (Formalism.FourierDecayAlt.P.B6.gN_continuous.comp hc).rpow_const (fun _ => Or.inr (by linarith))

theorem finv_eq (a : ℝ) {x : Mx k r} (hx : x ∈ UH (Hpk k r)) : Formalism.FourierDecayAlt.B.gN x⁻¹ ^ (a - 1) = finv k r a x := by
  unfold finv
  rw [uh_inv_eq hx]

theorem bound_trans (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (σ : Mx k r → (H →L[ℂ] H)) (a : ℝ) (hG : GrpF k r z) (hσ : SigU σ) (hπ : PiU z π) (ha : 1 ≤ a)
    {u v : H} (hu : u ∈ smoothVecs (k := k) (r := r) σ) {C : ℝ} {Ws : List (List (Mx k r))} (hC : 0 ≤ C)
    (hb : ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ x ∈ UH (Hpk k r),
      ‖⟪v, σ x w⟫_ℂ‖ ≤ C * (Ws.map fun W => ‖dsigW σ W w‖).sum * Formalism.FourierDecayAlt.B.gN x ^ (1 - a))
    {x : Mx k r} (hxG : x ∈ UH (Hpk k r)) (p : Mt k r × Mt k r)
    (hp : Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r) :
    ‖beF z c π σ (σ x u) v p‖ ≤ C * (Ws.map fun W => ‖dsigW σ W u‖).sum * finv k r a x *
      Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (1 - a) := by
  have hS := sum_nonneg_norms σ Ws u
  have hs : Matrix.of p.1 * Matrix.of p.2 ∈ UH (Hpk k r) := hG.1 _ hp.1.1 _ hp.2.1
  have hsx : Matrix.of p.1 * Matrix.of p.2 * x ∈ UH (Hpk k r) := hG.1 _ hs _ hxG
  obtain ⟨hxi1, -, hxi⟩ := hG.2.1 x hxG
  have hle : Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ≤
      Formalism.FourierDecayAlt.B.gN x⁻¹ * Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2 * x) := by
    have := Formalism.FourierDecayAlt.P.B6.gN_mul_le (k := k) (r := r) (Matrix.of p.1 * Matrix.of p.2 * x) x⁻¹
    rw [Matrix.mul_assoc _ x, hxi1, Matrix.mul_one] at this
    linarith
  have ht := gN_rpow_le ha (Formalism.FourierDecayAlt.P.B6.gN_pos (k := k) (r := r) hxi)
    (Formalism.FourierDecayAlt.P.B6.gN_pos (k := k) (r := r) hsx) (Formalism.FourierDecayAlt.P.B6.gN_pos (k := k) (r := r) hs) hle
  rw [finv_eq a hxG] at ht
  have h1 : ‖beF z c π σ (σ x u) v p‖ ≤ ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2) (σ x u)⟫_ℂ‖ :=
    norm_beF_le z c π σ (σ x u) v hG hπ p hp.1
  have h2 : σ (Matrix.of p.1 * Matrix.of p.2) (σ x u) = σ (Matrix.of p.1 * Matrix.of p.2 * x) u := by
    rw [hσ.2.1 _ hs _ hxG]; rfl
  rw [h2] at h1
  have h3 := hb u hu _ hsx
  have h4 := mul_le_mul_of_nonneg_left ht (mul_nonneg hC hS)
  calc ‖beF z c π σ (σ x u) v p‖ ≤ _ := h1.trans (h3.trans h4)
    _ = _ := by ring

theorem integrand_cont (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (σ : Mx k r → (H →L[ℂ] H)) (hG : GrpF k r z) (hσ : SigU σ)
    (hcont : ∀ w : H, ContinuousOn (fun g => σ g w) (UH (Hpk k r))) (u v : H) (p : Mt k r × Mt k r)
    (hp : Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r) :
    ContinuousOn (fun x => beF z c π σ (σ x u) v p) (UH (Hpk k r)) := by
  have hs : Matrix.of p.1 * Matrix.of p.2 ∈ UH (Hpk k r) := hG.1 _ hp.1.1 _ hp.2.1
  have hg : ContinuousOn (fun x : Mx k r => (⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * x) u⟫_ℂ *
      star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹) (UH (Hpk k r)) := by
    have hm' : Continuous (fun x : Mx k r => Matrix.of p.1 * Matrix.of p.2 * x) :=
      continuous_const.matrix_mul continuous_id
    have hm : ContinuousOn (fun x : Mx k r => Matrix.of p.1 * Matrix.of p.2 * x) (UH (Hpk k r)) :=
      hm'.continuousOn
    have hin : ContinuousOn (fun x : Mx k r => σ (Matrix.of p.1 * Matrix.of p.2 * x) u) (UH (Hpk k r)) :=
      (hcont u).comp hm (fun x hx => hG.1 _ hs _ hx)
    have hv : ContinuousOn (fun _ : Mx k r => v) (UH (Hpk k r)) := continuousOn_const
    have h1 : ContinuousOn (fun x : Mx k r => ⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * x) u⟫_ℂ) (UH (Hpk k r)) :=
      hv.inner hin
    have h2 : ContinuousOn (fun _ : Mx k r => star (psi k r z c (Matrix.of p.2))) (UH (Hpk k r)) :=
      continuousOn_const
    have h3 : ContinuousOn (fun _ : Mx k r => π (Matrix.of p.1)⁻¹) (UH (Hpk k r)) := continuousOn_const
    exact (h1.mul h2).smul h3
  refine hg.congr (fun y hy => ?_)
  unfold beF
  beta_reduce
  rw [hσ.2.1 _ hs _ hy]
  rfl

theorem cont_trans (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Mt k r)) [SFinite μN] (σ : Mx k r → (H →L[ℂ] H)) (a : ℝ)
    (hG : GrpF k r z) (hσ : SigU σ) (hπ : PiU z π) (hM : MeasF z π μW μN)
    (hcont : ∀ w : H, ContinuousOn (fun g => σ g w) (UH (Hpk k r)))
    (hgr : Integrable (fun p : Mt k r × Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (1 - a))
      (μW.prod μN)) (ha : 1 ≤ a)
    {u v : H} (hu : u ∈ smoothVecs (k := k) (r := r) σ) (hv : PtB σ a v) :
    ContinuousOn (fun x => be z c π μW μN σ (σ x u) v) (UH (Hpk k r)) := by
  intro x0 hx0
  obtain ⟨C, Ws, hC, -, hb⟩ := ptB_nonneg hv
  have hS := sum_nonneg_norms σ Ws u
  have hev : ∀ᶠ x in 𝓝[UH (Hpk k r)] x0, finv k r a x < finv k r a x0 + 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      ((finv_cont a ha).continuousAt.eventually_lt continuousAt_const (lt_add_one _))
  have key := continuousWithinAt_of_dominated (μ := μW.prod μN) (s := UH (Hpk k r)) (x₀ := x0)
    (F := fun x p => beF z c π σ (σ x u) v p)
    (bound := fun p => C * (Ws.map fun W => ‖dsigW σ W u‖).sum * (finv k r a x0 + 1) *
      Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (1 - a))
    (Filter.Eventually.of_forall fun x =>
      beF_aesm z c π μW μN σ (σ x u) v hM.2.2.2 (coef_aesm z π μW μN σ hG hM hcont v (σ x u)))
    (by
      filter_upwards [hev, self_mem_nhdsWithin] with x hx hxG
      filter_upwards [hM.1] with p hp
      refine (bound_trans z c π σ a hG hσ hπ ha hu hC hb hxG p hp).trans ?_
      have hg0 : 0 ≤ Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (1 - a) :=
        Real.rpow_nonneg (Formalism.FourierDecayAlt.P.B6.gN_nonneg _) _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx.le (mul_nonneg hC hS)) hg0)
    (hgr.const_mul _)
    (by
      filter_upwards [hM.1] with p hp
      exact integrand_cont z c π σ hG hσ hcont u v p hp x0 hx0)
  exact key

theorem beConv_of (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Mt k r)) [SFinite μN] (σ : Mx k r → (H →L[ℂ] H)) (a : ℝ) {w0 : H}
    (hG : GrpF k r z) (hσ : SigU σ) (hπ : PiU z π) (hψ : PsiF k r z c) (hM : MeasF z π μW μN)
    (hcont : ∀ w : H, ContinuousOn (fun g => σ g w) (UH (Hpk k r))) (ha : 1 ≤ a)
    (hgr : Integrable (fun p : Mt k r × Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (1 - a))
      (μW.prod μN))
    (hI3 : DecInf σ a) (hw0 : IsKFinHpk (k := k) (r := r) σ w0) : BeConvAt z c π μW μN σ w0 := by
  have hP : PtDec σ a (VDK σ w0) := by
    intro v hv
    rcases hv with hv | hv
    · exact ptDec_DD hG hσ ha (hI3 w0 hw0) v hv
    · exact hI3 v hv
  have hD : DecayOn μW μN σ (VDK σ w0) := decayOn_of_pt z π μW μN σ a hG hM hcont hgr hP
  have hst : ∀ g ∈ UH (Hpk k r), ∀ v ∈ smoothVecs (k := k) (r := r) σ, σ g v ∈ smoothVecs (k := k) (r := r) σ :=
    fun g hg v hv => Formalism.MainNotions.LeviCoordinates.smooth_vectors_translate_unitary hσ.2.1 hv hg
  refine ⟨int_on z c π μW μN σ hG hπ hM hD, cont_on z c π μW μN σ hG hπ hM hD,
    equiv_on z c π μW μN σ hG hσ hπ hψ hM hD, ?_, herm_on z c π μW μN σ hG hσ hπ hψ hM hD,
    fun u hu v hv => cont_trans z c π μW μN σ a hG hσ hπ hM hcont hgr ha hu (hP v hv)⟩
  intro h hh m hm u hu v hv
  have hhm : h * m ∈ UH (Hpk k r) := hG.1 _ hh.1 _ hm.1
  have e1 := herm_on z c π μW μN σ hG hσ hπ hψ hM hD u hu (σ (h * m) v) (hst _ hhm v hv)
  have e2 := equiv_on z c π μW μN σ hG hσ hπ hψ hM hD h hh m hm v hv u hu
  have e3 := herm_on z c π μW μN σ hG hσ hπ hψ hM hD u hu v hv
  rw [e2, ← e3] at e1
  have e4 := congrArg ContinuousLinearMap.adjoint e1
  rw [ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint] at e4
  exact e4

theorem beConv_of_low (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Mt k r)) [SFinite μN] (σ : Mx k r → (H →L[ℂ] H)) (a : ℝ) {w0 : H}
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    (hG : GrpF k r z) (hσ : SigU σ) (hπ : PiU z π) (hψ : PsiF k r z c) (hM : MeasF z π μW μN)
    (hcont : ∀ w : H, ContinuousOn (fun g => σ g w) (UH (Hpk k r))) (ha : 1 ≤ a)
    (hgr : Integrable (fun p : Mt k r × Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (1 - a))
      (μW.prod μN))
    (hI3 : DecInf σ a) (hw0 : IsLowUnitH k r ε lam σ w0) : BeConvAt z c π μW μN σ w0 :=
  beConv_of z c π μW μN σ a hG hσ hπ hψ hM hcont ha hgr hI3 (Formalism.MainNotions.DoubleDerivativeSmoothness.kfinHpk_of_lowUnitH hw0)

end PI.WBL.Cv.BeC
