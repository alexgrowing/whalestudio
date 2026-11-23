import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.PartAIff

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.Cv

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

def GrpF (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Prop :=
  (∀ a ∈ UH (Hpk k r), ∀ b ∈ UH (Hpk k r), a * b ∈ UH (Hpk k r)) ∧
  (∀ a ∈ UH (Hpk k r), a * a⁻¹ = 1 ∧ a⁻¹ * a = 1 ∧ a⁻¹ ∈ UH (Hpk k r)) ∧
  (∀ a ∈ UWset k r z, a⁻¹ ∈ UWset k r z) ∧ (∀ a ∈ Nset k r, a⁻¹ ∈ Nset k r) ∧
  (∀ h ∈ UWset k r z, ∀ n ∈ Nset k r, h⁻¹ * n * h ∈ Nset k r) ∧
  (∀ h ∈ UWset k r z, ∀ n ∈ Nset k r, h * n * h⁻¹ ∈ Nset k r) ∧
  (∀ a ∈ UWset k r z, ∀ b ∈ UWset k r z, a * b ∈ UWset k r z)

def SigU {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx k r → (H →L[ℂ] H)) : Prop :=
  σ 1 = 1 ∧ (∀ a ∈ UH (Hpk k r), ∀ b ∈ UH (Hpk k r), σ (a * b) = (σ a).comp (σ b)) ∧
    ∀ a ∈ UH (Hpk k r), ∀ x : H, ‖σ a x‖ = ‖x‖

def PiU {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) : Prop :=
  π 1 = 1 ∧ (∀ a ∈ UWset k r z, ∀ b ∈ UWset k r z, π (a * b) = (π a).comp (π b)) ∧
    ∀ a ∈ UWset k r z, ∀ x : Wp, ‖π a x‖ = ‖x‖

def PsiF (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) : Prop :=
  (∀ n ∈ Nset k r, ∀ m ∈ Nset k r, psi k r z c (n * m) = psi k r z c n * psi k r z c m) ∧
  (∀ h ∈ UWset k r z, ∀ n ∈ Nset k r, psi k r z c (h⁻¹ * n * h) = psi k r z c n) ∧
  (∀ h ∈ UWset k r z, ∀ n ∈ Nset k r, psi k r z c (h * n * h⁻¹) = psi k r z c n) ∧
  (∀ n ∈ Nset k r, psi k r z c n⁻¹ = star (psi k r z c n))

def tEq {k r : ℕ} (h m : Mx k r) (p : Mt k r × Mt k r) : Mt k r × Mt k r :=
  (fun i j => (Matrix.of p.1 * h) i j, fun i j => (h⁻¹ * Matrix.of p.2 * h * m) i j)

def tInv {k r : ℕ} (p : Mt k r × Mt k r) : Mt k r × Mt k r :=
  (fun i j => (Matrix.of p.1)⁻¹ i j, fun i j => (Matrix.of p.1 * (Matrix.of p.2)⁻¹ * (Matrix.of p.1)⁻¹) i j)

def MeasF {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN : Measure (Mt k r)) : Prop :=
  (∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r) ∧
  (∀ h ∈ UWset k r z, ∀ m ∈ Nset k r, MeasurePreserving (tEq h m) (μW.prod μN) (μW.prod μN)) ∧
  MeasurePreserving tInv (μW.prod μN) (μW.prod μN) ∧
  AEStronglyMeasurable (fun x : Mt k r => π (Matrix.of x)⁻¹) μW

def DecayAt {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μW μN : Measure (Mt k r)) (σ : Mx k r → (H →L[ℂ] H)) : Prop :=
  ∀ v : H, IsKFinHpk (k := k) (r := r) σ v → ∃ (C : ℝ) (Ws : List (List (Mx k r))),
    (∀ W ∈ Ws, ∀ X ∈ W, InLieHpk k r X) ∧
    ∀ w ∈ smoothVecs (k := k) (r := r) σ,
      Integrable (fun p : Mt k r × Mt k r => ⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ) (μW.prod μN) ∧
      ∫ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ‖ ∂(μW.prod μN) ≤
        C * (Ws.map fun W => ‖dsigW σ W w‖).sum

section Lemmas

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

theorem opNorm_le_one_of_iso {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (A : E →L[ℂ] E)
    (h : ∀ x, ‖A x‖ = ‖x‖) : ‖A‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound A zero_le_one (fun x => by rw [h, one_mul])

theorem norm_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Mx k r) : ‖psi k r z c g‖ = 1 := by
  unfold psi
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem ell_cont (z : Fin (2 * r + k + 1) → ℂ) : Continuous (ell k r z) := by
  unfold ell
  refine continuous_finset_sum _ (fun a _ => ?_)
  split_ifs
  · exact continuous_id.matrix_elem _ _
  · first
      | fun_prop
      | (simp only [dotProduct]
         exact continuous_finset_sum _ (fun j _ => (continuous_id.matrix_elem _ _).mul continuous_const))

theorem psi_cont (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) : Continuous (psi k r z c) := by
  unfold psi
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_const.mul (ell_cont z))))).cexp

theorem adjoint_eq_of_iso {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A B : E →L[ℂ] E) (hA : ∀ x, ‖A x‖ = ‖x‖) (hAB : A.comp B = 1) : ContinuousLinearMap.adjoint A = B := by
  have h1 : (ContinuousLinearMap.adjoint A).comp A = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self A).1 hA
  ext x
  have e1 : A (B x) = x := by
    rw [← ContinuousLinearMap.comp_apply, hAB, ContinuousLinearMap.one_apply]
  calc ContinuousLinearMap.adjoint A x = ContinuousLinearMap.adjoint A (A (B x)) := by rw [e1]
    _ = ((ContinuousLinearMap.adjoint A).comp A) (B x) := rfl
    _ = B x := by rw [h1, ContinuousLinearMap.one_apply]

theorem beF_aesm (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Mt k r)) [SFinite μN] (σ : Mx k r → (H →L[ℂ] H)) (w v : H)
    (hπm : AEStronglyMeasurable (fun x : Mt k r => π (Matrix.of x)⁻¹) μW)
    (hco : AEStronglyMeasurable (fun p : Mt k r × Mt k r => ⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ)
      (μW.prod μN)) :
    AEStronglyMeasurable (beF z c π σ w v) (μW.prod μN) := by
  have hps : Continuous fun p : Mt k r × Mt k r => star (psi k r z c (Matrix.of p.2)) :=
    (continuous_star.comp (psi_cont z c)).comp continuous_snd
  have hπ2 : AEStronglyMeasurable (fun p : Mt k r × Mt k r => π (Matrix.of p.1)⁻¹) (μW.prod μN) := by
    first
      | exact hπm.comp_fst
      | exact hπm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
      | exact hπm.prod_fst
  exact (hco.mul hps.aestronglyMeasurable).smul hπ2

theorem norm_beF_le (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (σ : Mx k r → (H →L[ℂ] H)) (w v : H) (hG : GrpF k r z) (hπ : PiU z π) (p : Mt k r × Mt k r)
    (hp : Matrix.of p.1 ∈ UWset k r z) :
    ‖beF z c π σ w v p‖ ≤ ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ‖ := by
  have hinv : (Matrix.of p.1)⁻¹ ∈ UWset k r z := hG.2.2.1 _ hp
  have hπn : ‖π (Matrix.of p.1)⁻¹‖ ≤ 1 := opNorm_le_one_of_iso _ (hπ.2.2 _ hinv)
  unfold beF
  rw [norm_smul, norm_mul, norm_star, norm_psi, mul_one]
  exact mul_le_of_le_one_right (norm_nonneg _) hπn

theorem conv_int (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Mt k r)) [SFinite μN] (σ : Mx k r → (H →L[ℂ] H))
    (hG : GrpF k r z) (hπ : PiU z π) (hM : MeasF z π μW μN) (hD : DecayAt μW μN σ) :
    ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ v : H, IsKFinHpk (k := k) (r := r) σ v →
      Integrable (beF z c π σ w v) (μW.prod μN) := by
  intro w hw v hv
  obtain ⟨C, Ws, -, hb⟩ := hD v hv
  have hint := (hb w hw).1
  refine Integrable.mono' hint.norm (beF_aesm z c π μW μN σ w v hM.2.2.2 hint.aestronglyMeasurable) ?_
  exact hM.1.mono (fun p hp => norm_beF_le z c π σ w v hG hπ p hp.1)

theorem conv_cont (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Mt k r)) [SFinite μN] (σ : Mx k r → (H →L[ℂ] H))
    (hG : GrpF k r z) (hπ : PiU z π) (hM : MeasF z π μW μN) (hD : DecayAt μW μN σ) :
    ∀ v : H, IsKFinHpk (k := k) (r := r) σ v → ∀ x : Wp,
      IsCWCont (k := k) (r := r) σ (fun w => be z c π μW μN σ w v x) := by
  intro v hv x
  obtain ⟨C, Ws, hWs, hb⟩ := hD v hv
  refine ⟨C * ‖x‖, Ws, hWs, fun w hw => ?_⟩
  have hint := (hb w hw).1
  have hF := conv_int z c π μW μN σ hG hπ hM hD w hw v hv
  have h1 : ‖be z c π μW μN σ w v x‖ ≤ ‖be z c π μW μN σ w v‖ * ‖x‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have h2 : ‖be z c π μW μN σ w v‖ ≤ ∫ p, ‖beF z c π σ w v p‖ ∂(μW.prod μN) :=
    norm_integral_le_integral_norm _
  have h3 : ∫ p, ‖beF z c π σ w v p‖ ∂(μW.prod μN) ≤
      ∫ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ‖ ∂(μW.prod μN) :=
    integral_mono_ae hF.norm hint.norm (hM.1.mono (fun p hp => norm_beF_le z c π σ w v hG hπ p hp.1))
  have h4 := (hb w hw).2
  calc ‖be z c π μW μN σ w v x‖ ≤ ‖be z c π μW μN σ w v‖ * ‖x‖ := h1
    _ ≤ (C * (Ws.map fun W => ‖dsigW σ W w‖).sum) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (h2.trans (h3.trans h4)) (norm_nonneg _)
    _ = C * ‖x‖ * (Ws.map fun W => ‖dsigW σ W w‖).sum := by ring

end Lemmas

end PI.WBL.Cv
