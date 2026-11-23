import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.PsiMulStar
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselBoundFamilyOfDoubleCoset
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.Cv.BeC

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL PI.WBL.Cv

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

def DecayOn (μW μN : Measure (Mt k r)) (σ : Mx k r → (H →L[ℂ] H)) (V : H → Prop) : Prop :=
  ∀ v : H, V v → ∃ (C : ℝ) (Ws : List (List (Mx k r))),
    (∀ W ∈ Ws, ∀ X ∈ W, InLieHpk k r X) ∧
    ∀ w ∈ smoothVecs (k := k) (r := r) σ,
      Integrable (fun p : Mt k r × Mt k r => ⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ) (μW.prod μN) ∧
      ∫ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ‖ ∂(μW.prod μN) ≤
        C * (Ws.map fun W => ‖dsigW σ W w‖).sum

theorem int_on (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Mt k r)) [SFinite μN] (σ : Mx k r → (H →L[ℂ] H)) {V : H → Prop}
    (hG : GrpF k r z) (hπ : PiU z π) (hM : MeasF z π μW μN) (hD : DecayOn μW μN σ V) :
    ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ v : H, V v → Integrable (beF z c π σ w v) (μW.prod μN) := by
  intro w hw v hv
  obtain ⟨C, Ws, -, hb⟩ := hD v hv
  have hi := (hb w hw).1
  refine Integrable.mono' hi.norm (beF_aesm z c π μW μN σ w v hM.2.2.2 hi.aestronglyMeasurable) ?_
  filter_upwards [hM.1] with p hp
  exact norm_beF_le z c π σ w v hG hπ p hp.1

theorem cont_on (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Mt k r)) [SFinite μN] (σ : Mx k r → (H →L[ℂ] H)) {V : H → Prop}
    (hG : GrpF k r z) (hπ : PiU z π) (hM : MeasF z π μW μN) (hD : DecayOn μW μN σ V) :
    ∀ v : H, V v → ∀ x : Wp, IsCWCont (k := k) (r := r) σ (fun w => be z c π μW μN σ w v x) := by
  intro v hv x
  obtain ⟨C, Ws, hWs, hb⟩ := hD v hv
  refine ⟨‖x‖ * C, Ws, hWs, fun w hw => ?_⟩
  have hi := (hb w hw).1
  have hI : ‖be z c π μW μN σ w v‖ ≤ ∫ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ‖ ∂(μW.prod μN) := by
    calc ‖be z c π μW μN σ w v‖ ≤ ∫ p, ‖beF z c π σ w v p‖ ∂(μW.prod μN) :=
          norm_integral_le_integral_norm _
      _ ≤ _ := by
          refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hi.norm ?_
          filter_upwards [hM.1] with p hp
          exact norm_beF_le z c π σ w v hG hπ p hp.1
  calc ‖be z c π μW μN σ w v x‖ ≤ ‖be z c π μW μN σ w v‖ * ‖x‖ := (be z c π μW μN σ w v).le_opNorm x
    _ ≤ (C * (Ws.map fun W => ‖dsigW σ W w‖).sum) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (hI.trans (hb w hw).2) (norm_nonneg _)
    _ = ‖x‖ * C * (Ws.map fun W => ‖dsigW σ W w‖).sum := by ring

theorem equiv_on (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Mt k r)) [SFinite μN] (σ : Mx k r → (H →L[ℂ] H)) {V : H → Prop}
    (hG : GrpF k r z) (hσ : SigU σ) (hπ : PiU z π) (hψ : PsiF k r z c) (hM : MeasF z π μW μN)
    (hD : DecayOn μW μN σ V) :
    ∀ h ∈ UWset k r z, ∀ m ∈ Nset k r, ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ v : H, V v →
      be z c π μW μN σ (σ (h * m) w) v = (psi k r z c m • π h).comp (be z c π μW μN σ w v) := by
  intro h hh m hm w hw v hv
  have hint := int_on z c π μW μN σ hG hπ hM hD w hw v hv
  have hT := hM.2.1 h hh m hm
  let L : (Wp →L[ℂ] Wp) →L[ℂ] (Wp →L[ℂ] Wp) :=
    ContinuousLinearMap.compL ℂ Wp Wp Wp (psi k r z c m • π h)
  have key : ∀ᵐ p ∂(μW.prod μN), beF z c π σ (σ (h * m) w) v p = L (beF z c π σ w v (tEq h m p)) := by
    filter_upwards [hM.1] with p hp
    exact beF_tEq z c π σ hG hσ hπ hψ h m hh hm w v p hp
  have hint2 : Integrable (fun p => beF z c π σ w v (tEq h m p)) (μW.prod μN) :=
    hT.integrable_comp_of_integrable hint
  have hmap : ∫ p, beF z c π σ w v (tEq h m p) ∂(μW.prod μN) = be z c π μW μN σ w v := by
    rw [← integral_map hT.measurable.aemeasurable (by rw [hT.map_eq]; exact hint.aestronglyMeasurable),
      hT.map_eq]
    rfl
  show ∫ p, beF z c π σ (σ (h * m) w) v p ∂(μW.prod μN) = L (be z c π μW μN σ w v)
  rw [integral_congr_ae key, L.integral_comp_comm hint2, hmap]

theorem herm_of_aesm (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Mt k r)) [SFinite μN] (σ : Mx k r → (H →L[ℂ] H))
    (hG : GrpF k r z) (hσ : SigU σ) (hπ : PiU z π) (hψ : PsiF k r z c) (hM : MeasF z π μW μN) (w v : H)
    (hm : AEStronglyMeasurable (beF z c π σ v w) (μW.prod μN)) :
    ContinuousLinearMap.adjoint (be z c π μW μN σ w v) = be z c π μW μN σ v w := by
  have hT := hM.2.2.1
  have key : ∀ᵐ p ∂(μW.prod μN), adjR Wp (beF z c π σ w v p) = beF z c π σ v w (tInv p) := by
    filter_upwards [hM.1] with p hp
    exact (beF_tInv z c π σ hG hσ hπ hψ w v p hp).symm
  have hmap : ∫ p, beF z c π σ v w (tInv p) ∂(μW.prod μN) = be z c π μW μN σ v w := by
    rw [← integral_map hT.measurable.aemeasurable (by rw [hT.map_eq]; exact hm), hT.map_eq]
    rfl
  show adjR Wp (∫ p, beF z c π σ w v p ∂(μW.prod μN)) = _
  rw [← (adjR Wp).integral_comp_comm, integral_congr_ae key, hmap]

theorem herm_on (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Mt k r)) [SFinite μN] (σ : Mx k r → (H →L[ℂ] H)) {V : H → Prop}
    (hG : GrpF k r z) (hσ : SigU σ) (hπ : PiU z π) (hψ : PsiF k r z c) (hM : MeasF z π μW μN)
    (hD : DecayOn μW μN σ V) :
    ∀ w : H, V w → ∀ v ∈ smoothVecs (k := k) (r := r) σ,
      ContinuousLinearMap.adjoint (be z c π μW μN σ w v) = be z c π μW μN σ v w := fun w hw v hv =>
  herm_of_aesm z c π μW μN σ hG hσ hπ hψ hM w v
    (int_on z c π μW μN σ hG hπ hM hD v hv w hw).aestronglyMeasurable

def PtB (σ : Mx k r → (H →L[ℂ] H)) (a : ℝ) (v : H) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ W ∈ Ws, ∀ X ∈ W, InLieHpk k r X) ∧
    ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ x ∈ UH (Hpk k r),
      ‖⟪v, σ x w⟫_ℂ‖ ≤ C * (Ws.map fun W => ‖dsigW σ W w‖).sum * Formalism.FourierDecayAlt.B.gN x ^ (1 - a)

def PtDec (σ : Mx k r → (H →L[ℂ] H)) (a : ℝ) (V : H → Prop) : Prop := ∀ v : H, V v → PtB σ a v

theorem sum_nonneg_norms (σ : Mx k r → (H →L[ℂ] H)) (Ws : List (List (Mx k r))) (w : H) :
    0 ≤ (Ws.map fun W => ‖dsigW σ W w‖).sum :=
  List.sum_nonneg (fun x hx => by
    obtain ⟨W, _, rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg _)

theorem ptB_nonneg {σ : Mx k r → (H →L[ℂ] H)} {a : ℝ} {v : H} (h : PtB σ a v) :
    ∃ (C : ℝ) (Ws : List (List (Mx k r))), 0 ≤ C ∧ (∀ W ∈ Ws, ∀ X ∈ W, InLieHpk k r X) ∧
      ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ x ∈ UH (Hpk k r),
        ‖⟪v, σ x w⟫_ℂ‖ ≤ C * (Ws.map fun W => ‖dsigW σ W w‖).sum * Formalism.FourierDecayAlt.B.gN x ^ (1 - a) := by
  obtain ⟨C, Ws, hWs, hb⟩ := h
  refine ⟨max C 0, Ws, le_max_right _ _, hWs, fun w hw x hx => (hb w hw x hx).trans ?_⟩
  have h1 := sum_nonneg_norms σ Ws w
  have h2 : 0 ≤ Formalism.FourierDecayAlt.B.gN x ^ (1 - a) := Real.rpow_nonneg (Formalism.FourierDecayAlt.P.B6.gN_nonneg x) _
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left C 0) h1) h2
  exact this

theorem isClosed_UH : IsClosed (UH (Hpk k r) : Set (Mx k r)) := by
  have hc : Continuous (fun g : Mx k r => gᴴ * Hpk k r * g) :=
    ((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_id
  exact isClosed_eq hc continuous_const

theorem continuous_matrix_mul : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 * Matrix.of p.2 : Mx k r)) := by
  have h1 : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mx k r)) := continuous_fst
  have h2 : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.2 : Mx k r)) := continuous_snd
  exact h1.matrix_mul h2

theorem decayOn_of_pt (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Mt k r)) [SFinite μN] (σ : Mx k r → (H →L[ℂ] H)) (a : ℝ) {V : H → Prop}
    (hG : GrpF k r z) (hM : MeasF z π μW μN)
    (hcont : ∀ w : H, ContinuousOn (fun g => σ g w) (UH (Hpk k r)))
    (hgr : Integrable (fun p : Mt k r × Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (1 - a))
      (μW.prod μN))
    (hP : PtDec σ a V) : DecayOn μW μN σ V := by
  intro v hv
  obtain ⟨C, Ws, hWs, hb⟩ := hP v hv
  refine ⟨C * ∫ p, Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (1 - a) ∂(μW.prod μN), Ws, hWs,
    fun w hw => ?_⟩
  have hmem : ∀ᵐ p ∂(μW.prod μN), p ∈ (fun p : Mt k r × Mt k r => (Matrix.of p.1 * Matrix.of p.2 : Mx k r)) ⁻¹'
      UH (Hpk k r) := by
    filter_upwards [hM.1] with p hp
    exact hG.1 _ hp.1.1 _ hp.2.1
  have hT : MeasurableSet ((fun p : Mt k r × Mt k r => (Matrix.of p.1 * Matrix.of p.2 : Mx k r)) ⁻¹'
      UH (Hpk k r)) := (isClosed_UH.preimage continuous_matrix_mul).measurableSet
  have hcoT : ContinuousOn (fun p : Mt k r × Mt k r => ⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ)
      ((fun p : Mt k r × Mt k r => (Matrix.of p.1 * Matrix.of p.2 : Mx k r)) ⁻¹' UH (Hpk k r)) :=
    continuousOn_const.inner ((hcont w).comp continuous_matrix_mul.continuousOn (fun p hp => hp))
  have hae : AEStronglyMeasurable (fun p : Mt k r × Mt k r => ⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ)
      (μW.prod μN) := by
    have h := hcoT.aestronglyMeasurable (μ := μW.prod μN) hT
    rwa [Measure.restrict_eq_self_of_ae_mem hmem] at h
  have hbd : ∀ᵐ p ∂(μW.prod μN), ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ‖ ≤
      C * (Ws.map fun W => ‖dsigW σ W w‖).sum * Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (1 - a) := by
    filter_upwards [hmem] with p hp
    exact hb w hw _ hp
  have hint := Integrable.mono' (hgr.const_mul (C * (Ws.map fun W => ‖dsigW σ W w‖).sum)) hae hbd
  refine ⟨hint, ?_⟩
  calc ∫ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ‖ ∂(μW.prod μN)
      ≤ ∫ p, C * (Ws.map fun W => ‖dsigW σ W w‖).sum *
          Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (1 - a) ∂(μW.prod μN) :=
        integral_mono_ae hint.norm (hgr.const_mul _) hbd
    _ = C * (Ws.map fun W => ‖dsigW σ W w‖).sum *
          ∫ p, Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (1 - a) ∂(μW.prod μN) :=
        integral_const_mul _ _
    _ = _ := by ring

theorem inner_sig {σ : Mx k r → (H →L[ℂ] H)} (hσ : SigU σ) {y : Mx k r} (hy : y ∈ UH (Hpk k r)) (u u' : H) :
    ⟪σ y u, σ y u'⟫_ℂ = ⟪u, u'⟫_ℂ :=
  (LinearMap.norm_map_iff_inner_map_map (σ y)).1 (hσ.2.2 y hy) u u'

theorem gN_rpow_trans {a : ℝ} (ha : 1 ≤ a) {x y : Mx k r} (hx : x ∈ UH (Hpk k r)) (hy : y ∈ UH (Hpk k r))
    (hyx : y⁻¹ * x ∈ UH (Hpk k r)) (he : y * (y⁻¹ * x) = x) :
    Formalism.FourierDecayAlt.B.gN (y⁻¹ * x) ^ (1 - a) ≤ Formalism.FourierDecayAlt.B.gN y ^ (a - 1) * Formalism.FourierDecayAlt.B.gN x ^ (1 - a) := by
  have py := Formalism.FourierDecayAlt.P.B6.gN_pos (k := k) (r := r) hy
  have pyx := Formalism.FourierDecayAlt.P.B6.gN_pos (k := k) (r := r) hyx
  have px := Formalism.FourierDecayAlt.P.B6.gN_pos (k := k) (r := r) hx
  have hle : Formalism.FourierDecayAlt.B.gN x ≤ Formalism.FourierDecayAlt.B.gN y * Formalism.FourierDecayAlt.B.gN (y⁻¹ * x) := by
    have := Formalism.FourierDecayAlt.P.B6.gN_mul_le (k := k) (r := r) y (y⁻¹ * x)
    rwa [he] at this
  have h1 : (Formalism.FourierDecayAlt.B.gN y * Formalism.FourierDecayAlt.B.gN (y⁻¹ * x)) ^ (1 - a) ≤ Formalism.FourierDecayAlt.B.gN x ^ (1 - a) :=
    Real.rpow_le_rpow_of_nonpos px hle (by linarith)
  rw [Real.mul_rpow py.le pyx.le] at h1
  have h2 : Formalism.FourierDecayAlt.B.gN y ^ (a - 1) * Formalism.FourierDecayAlt.B.gN y ^ (1 - a) = 1 := by
    rw [← Real.rpow_add py]; simp
  have h3 : 0 ≤ Formalism.FourierDecayAlt.B.gN y ^ (a - 1) := Real.rpow_nonneg py.le _
  calc Formalism.FourierDecayAlt.B.gN (y⁻¹ * x) ^ (1 - a)
      = Formalism.FourierDecayAlt.B.gN y ^ (a - 1) * (Formalism.FourierDecayAlt.B.gN y ^ (1 - a) * Formalism.FourierDecayAlt.B.gN (y⁻¹ * x) ^ (1 - a)) := by
        rw [← mul_assoc, h2, one_mul]
    _ ≤ Formalism.FourierDecayAlt.B.gN y ^ (a - 1) * Formalism.FourierDecayAlt.B.gN x ^ (1 - a) := mul_le_mul_of_nonneg_left h1 h3

theorem ptB_trans {z : Fin (2 * r + k + 1) → ℂ} {σ : Mx k r → (H →L[ℂ] H)} {a : ℝ} (hG : GrpF k r z)
    (hσ : SigU σ) (ha : 1 ≤ a) {w0 : H} (h0 : PtB σ a w0) {y : Mx k r} (hy : y ∈ UH (Hpk k r)) :
    PtB σ a (σ y w0) := by
  obtain ⟨C, Ws, hC, hWs, hb⟩ := ptB_nonneg h0
  refine ⟨C * Formalism.FourierDecayAlt.B.gN y ^ (a - 1), Ws, hWs, fun w hw x hx => ?_⟩
  obtain ⟨hyi1, hyi2, hyi⟩ := hG.2.1 y hy
  have hyx : y⁻¹ * x ∈ UH (Hpk k r) := hG.1 _ hyi _ hx
  have he : y * (y⁻¹ * x) = x := by rw [← Matrix.mul_assoc, hyi1, Matrix.one_mul]
  have hsx : σ x w = σ y (σ (y⁻¹ * x) w) := by
    conv_lhs => rw [← he]
    rw [hσ.2.1 _ hy _ hyx]
    rfl
  rw [hsx, inner_sig hσ hy]
  have hS := sum_nonneg_norms σ Ws w
  have hb' := hb w hw _ hyx
  have ht := gN_rpow_trans ha hx hy hyx he
  calc ‖⟪w0, σ (y⁻¹ * x) w⟫_ℂ‖ ≤ C * (Ws.map fun W => ‖dsigW σ W w‖).sum * Formalism.FourierDecayAlt.B.gN (y⁻¹ * x) ^ (1 - a) := hb'
    _ ≤ C * (Ws.map fun W => ‖dsigW σ W w‖).sum * (Formalism.FourierDecayAlt.B.gN y ^ (a - 1) * Formalism.FourierDecayAlt.B.gN x ^ (1 - a)) :=
        mul_le_mul_of_nonneg_left ht (mul_nonneg hC hS)
    _ = C * Formalism.FourierDecayAlt.B.gN y ^ (a - 1) * (Ws.map fun W => ‖dsigW σ W w‖).sum * Formalism.FourierDecayAlt.B.gN x ^ (1 - a) := by
        ring

theorem ptB_zero (σ : Mx k r → (H →L[ℂ] H)) (a : ℝ) : PtB σ a (0 : H) :=
  ⟨0, [], by simp, fun w _ x _ => by simp⟩

theorem ptB_add {σ : Mx k r → (H →L[ℂ] H)} {a : ℝ} {v1 v2 : H} (h1 : PtB σ a v1) (h2 : PtB σ a v2) :
    PtB σ a (v1 + v2) := by
  obtain ⟨C1, W1, hC1, hW1, hb1⟩ := ptB_nonneg h1
  obtain ⟨C2, W2, hC2, hW2, hb2⟩ := ptB_nonneg h2
  refine ⟨C1 + C2, W1 ++ W2, fun W hW => (List.mem_append.1 hW).elim (hW1 W) (hW2 W), fun w hw x hx => ?_⟩
  have s1 := sum_nonneg_norms σ W1 w
  have s2 := sum_nonneg_norms σ W2 w
  have hg : 0 ≤ Formalism.FourierDecayAlt.B.gN x ^ (1 - a) := Real.rpow_nonneg (Formalism.FourierDecayAlt.P.B6.gN_nonneg x) _
  rw [List.map_append, List.sum_append, inner_add_left]
  calc ‖⟪v1, σ x w⟫_ℂ + ⟪v2, σ x w⟫_ℂ‖ ≤ ‖⟪v1, σ x w⟫_ℂ‖ + ‖⟪v2, σ x w⟫_ℂ‖ := norm_add_le _ _
    _ ≤ C1 * (W1.map fun W => ‖dsigW σ W w‖).sum * Formalism.FourierDecayAlt.B.gN x ^ (1 - a) +
        C2 * (W2.map fun W => ‖dsigW σ W w‖).sum * Formalism.FourierDecayAlt.B.gN x ^ (1 - a) :=
        add_le_add (hb1 w hw x hx) (hb2 w hw x hx)
    _ ≤ _ := by nlinarith [mul_nonneg hC1 s2, mul_nonneg hC2 s1, mul_nonneg (mul_nonneg hC1 s2) hg,
          mul_nonneg (mul_nonneg hC2 s1) hg]

theorem ptB_smul {σ : Mx k r → (H →L[ℂ] H)} {a : ℝ} (c : ℂ) {v : H} (h : PtB σ a v) : PtB σ a (c • v) := by
  obtain ⟨C, Ws, hWs, hb⟩ := h
  refine ⟨‖c‖ * C, Ws, hWs, fun w hw x hx => ?_⟩
  rw [inner_smul_left, norm_mul, RCLike.norm_conj, mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (by rw [← mul_assoc]; exact hb w hw x hx) (norm_nonneg c)

theorem ptDec_DD {z : Fin (2 * r + k + 1) → ℂ} {σ : Mx k r → (H →L[ℂ] H)} {a : ℝ} (hG : GrpF k r z)
    (hσ : SigU σ) (ha : 1 ≤ a) {w0 : H} (h0 : PtB σ a w0) :
    PtDec σ a (fun v => v ∈ Formalism.MainNotions.BridgeLemma₄.DDsp σ w0) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    exact ptB_trans hG hσ ha h0 hy
  | zero => exact ptB_zero σ a
  | add x y _ _ hx hy => exact ptB_add hx hy
  | smul c x _ hx => exact ptB_smul c hx

end PI.WBL.Cv.BeC
