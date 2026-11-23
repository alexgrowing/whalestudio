import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootMeasureTransportDoubleCosetStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselAmplitudeIndependentOfQuotientMeasureStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselRootMeasureIndependentOfChoicesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HcTypeWIrreducibleAndSchurAverage
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCharactersAgreeCommonStabiliser
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselCharacterUnipotentRadicalProperties
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GroupFactorizationHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentLevelZeroEqOne

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.AmpCoset

variable {k r : ℕ}

theorem exists_blocks (bs : List (ℂ × ℕ)) (h : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) :
    ∃ cs : List (ℂˣ × ℕ+), (cs.map (fun b => (b.2 : ℕ))).sum = (bs.map Prod.snd).sum ∧
      ∀ i j, Loc.ptEntryL cs i j = ptEntry bs i j := by
  induction bs with
  | nil => exact ⟨[], rfl, fun _ _ => rfl⟩
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    obtain ⟨cs, h1, h2⟩ := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    obtain ⟨h3, h4⟩ := h (t, s) List.mem_cons_self
    refine ⟨(Units.mk0 t h3, ⟨s, h4⟩) :: cs, by simp [h1], fun i j => ?_⟩
    simp only [Loc.ptEntryL, ptEntry, h2]
    rfl

theorem ell_eq (z : Fin (2 * r + k + 1) → ℂ) (m : Mat k r) :
    ell k r z m = ∑ j : Fin r, Uof k r z m j.castSucc j.succ := by
  unfold ell
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold Uof
  rw [dif_pos (show (j.castSucc).val < r from j.2)]
  split_ifs with h
  · exact (mF_col z m _ j.succ h).symm
  · have h' : ¬ (j.succ).val < r := h
    simp [Matrix.mul_apply, Fm, fvec, h, Matrix.mulVec, dotProduct]

theorem psi_exact {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (c : ℝ) {g : Mat k r}
    (hg : g ∈ GG k r) {p : Point ℂ (r + 1)} (hp : ZhatO k r z z' g = ptMat p) {ρ : Mat k r} (hρ : ρ ∈ Rset k r g) :
    psi k r z c (g * ρ * g⁻¹) = psi k r z' c ρ := by
  obtain ⟨cs, h1, h2⟩ := exists_blocks p.1 p.2.1
  obtain ⟨hm', hs⟩ := (GlobalTheory.BesselPsi.psi_character k r z c hz).2.2.1 _ hρ.2
  have hgu := isUnit_det_of_mem_GG hg
  have hmu := isUnit_det_of_mem_GG hρ.2.1
  set m := g * ρ * g⁻¹ with hm
  have hU : (m⁻¹)ᴴ * Hpk k r * m⁻¹ = Hpk k r := hm'.1
  have e1 : m * g = g * ρ := by rw [hm, Matrix.nonsing_inv_mul_cancel_right _ _ hgu]
  have key : (Uof k r z m⁻¹)ᴴ * Zhat k r z z' g = Zhat k r z z' g * Uof k r z' ρ := by
    rw [Zhat_eq]
    calc (Uof k r z m⁻¹)ᴴ * ((Fm k r z)ᴴ * Hpk k r * g * Fm k r z')
        = (Fm k r z * Uof k r z m⁻¹)ᴴ * Hpk k r * (m⁻¹ * (m * g)) * Fm k r z' := by
          rw [conjTranspose_mul, Matrix.nonsing_inv_mul_cancel_left _ _ hmu]; simp only [Matrix.mul_assoc]
      _ = (Fm k r z)ᴴ * ((m⁻¹)ᴴ * Hpk k r * m⁻¹) * g * (ρ * Fm k r z') := by
          rw [← N_F hz hm', e1, conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, N_F hz' hρ.1]; simp only [Matrix.mul_assoc]
  have main := GlobalTheory.HL.CharAgree.simple_sum (⟨cs, h1.trans p.2.2⟩ : Loc.Pt ℂ (r + 1)) (Zhat k r z z' g)
    (Uof k r z m⁻¹)ᴴ (Uof k r z' ρ) (fun a b => by
      have := congrFun (congrFun hp a) b
      simp only [ZhatO, ptMat] at this
      simp only [Loc.Pt.mat, h2, ← this]
      rw [mul_comm, ← mul_assoc, ← mul_pow]; simp)
    (fun i j h => by rw [conjTranspose_apply, Uof_lower_zero hm' j i h, star_zero])
    (fun i j h => Uof_lower_zero hρ.1 i j h) (fun a b => congrFun (congrFun key a) b)
  simp only [conjTranspose_apply] at main
  rw [← star_sum, ← ell_eq, ← ell_eq] at main
  rw [← star_star (psi k r z c m), ← hs]
  have e2 : ell k r z' ρ = - star (ell k r z m⁻¹) := by rw [main, neg_neg]
  unfold psi
  rw [e2, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp

theorem psi_cell {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (c : ℝ) {n n' g : Mat k r}
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) (hγ : n * g * n' ∈ GG k r) {p : Point ℂ (r + 1)}
    (hp : ZhatO k r z z' g = ptMat p) {ρ : Mat k r} (hρ : ρ ∈ Rset k r (n * g * n')) :
    psi k r z c (n * g * n' * ρ * (n * g * n')⁻¹) = psi k r z' c ρ := by
  obtain ⟨-, -, -, gm, gi⟩ := isClosedSub_GG (k := k) (r := r)
  obtain ⟨-, -, -, nm, ni⟩ := isClosedSub_Nset (k := k) (r := r)
  have hu := isUnit_det_of_mem_GG hn.1
  have hu' := isUnit_det_of_mem_GG hn'.1
  have hg : g ∈ GG k r := by
    have := gm _ (gm _ (gi _ hn.1) _ hγ) _ (gi _ hn'.1)
    rwa [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hu', Matrix.nonsing_inv_mul_cancel_left _ _ hu] at this
  have conj : ∀ w, inWb k r w → ∀ a ∈ Nset k r, ∀ x ∈ Nset k r, psi k r w c (a * x * a⁻¹) = psi k r w c x := by
    intro w hw a ha x hx
    obtain ⟨q1, q2, q3, -⟩ := GlobalTheory.BesselPsi.psi_character k r w c hw
    rw [(q2 _ (nm _ ha _ hx) _ (ni _ ha)).2, (q2 _ ha _ hx).2, (q3 _ ha).2, mul_right_comm, Complex.star_def,
      Complex.mul_conj, Complex.normSq_eq_norm_sq, q1]
    simp
  have e : n * g * n' * ρ * (n * g * n')⁻¹ = n * (g * (n' * ρ * n'⁻¹) * g⁻¹) * n⁻¹ := by
    simp only [Matrix.mul_inv_rev, Matrix.mul_assoc]
  have h2 : g * (n' * ρ * n'⁻¹) * g⁻¹ ∈ Nset k r := by
    have := nm _ (nm _ (ni _ hn) _ hρ.2) _ hn
    rw [e] at this
    simpa only [Matrix.mul_assoc, Matrix.nonsing_inv_mul n hu, Matrix.mul_one,
      Matrix.nonsing_inv_mul_cancel_left n _ hu] using this
  rw [e, conj z hz n hn _ h2, psi_exact hz hz' c hg hp ⟨nm _ (nm _ hn' _ hρ.1) _ (ni _ hn'), h2⟩,
    conj z' hz' n' hn' _ hρ.1]

theorem cont_lmul (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) :=
  continuous_const.matrix_mul (continuous_id (X := Mat k r))

theorem cont_conj (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) :=
  (continuous_const.matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const

noncomputable def lmulE {a : Mat k r} (ha : IsUnit a.det) : Mt k r ≃ᵐ Mt k r where
  toFun := lmulM a
  invFun := lmulM a⁻¹
  left_inv x := Matrix.nonsing_inv_mul_cancel_left a (Matrix.of x) ha
  right_inv x := Matrix.mul_nonsing_inv_cancel_left a (Matrix.of x) ha
  measurable_toFun := (cont_lmul a).measurable
  measurable_invFun := (cont_lmul a⁻¹).measurable

theorem quot_translate {μG μR ν : Measure (Mt k r)} {a : Mat k r} (ha : IsUnit a.det)
    (hG : μG.map (lmulM a) = μG) (h : IsQuotMeas μG μR ν) :
    IsQuotMeas μG (μR.map (conjM a)) (ν.map (lmulM a)) := by
  intro f hf
  have mL := (cont_lmul a).measurable
  have mC := (cont_conj a).measurable
  have e1 : ∫⁻ x, f x ∂μG = ∫⁻ x, f (lmulM a x) ∂μG := by
    conv_lhs => rw [← hG]
    rw [lintegral_map hf mL]
  rw [e1, h (fun x => f (lmulM a x)) (hf.comp mL)]
  refine Eq.trans ?_ ((lmulE ha).measurableEmbedding.lintegral_map _).symm
  refine lintegral_congr fun x => ?_
  have c2 : Continuous fun s : Mt k r => (fun i j => (Matrix.of s * Matrix.of (lmulE ha x)) i j : Mt k r) :=
    (continuous_id (X := Mat k r)).matrix_mul continuous_const
  have m2 : Measurable fun s : Mt k r => f (fun i j => (Matrix.of s * Matrix.of (lmulE ha x)) i j) :=
    hf.comp c2.measurable
  rw [lintegral_map m2 mC]
  refine lintegral_congr fun s => congrArg f ?_
  show a * (Matrix.of s * Matrix.of x) = a * Matrix.of s * a⁻¹ * (a * Matrix.of x)
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ ha]

theorem ae_mem_of_quot {μG μR ν : Measure (Mt k r)} {R : Set (Mat k r)} (hR : R ⊆ GG k r)
    (hG : IsHaarOn (GG k r) μG) (hμ : IsHaarOn R μR) (h : IsQuotMeas μG μR ν) :
    ∀ᵐ x ∂ν, Matrix.of x ∈ GG k r := by
  obtain ⟨-, gc, -, gm, gi⟩ := isClosedSub_GG (k := k) (r := r)
  set B : Set (Mt k r) := {x | Matrix.of x ∉ GG k r} with hB
  have hof : Continuous (fun y : Mt k r => (Matrix.of y : Mat k r)) := continuous_id
  have mB : MeasurableSet B := (gc.preimage hof).measurableSet.compl
  have h1 := h (B.indicator 1) (measurable_one.indicator mB)
  rw [lintegral_indicator_one mB, hG.2.2.1] at h1
  have h2 : ∫⁻ x, B.indicator (fun _ => μR Set.univ) x ∂ν ≤ 0 := by
    rw [h1]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, ← lintegral_one]
      refine (lintegral_congr_ae ?_).le
      filter_upwards [(ae_iff.2 hμ.2.2.1 : ∀ᵐ s ∂μR, Matrix.of s ∈ R)] with s hs
      rw [Set.indicator_of_mem]
      · rfl
      · intro hsx
        have := gm _ (gi _ (hR hs)) _ hsx
        exact hx (Matrix.nonsing_inv_mul_cancel_left (Matrix.of s) (Matrix.of x) (isUnit_det_of_mem_GG (hR hs)) ▸ this)
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  rw [lintegral_indicator_const mB, nonpos_iff_eq_zero, mul_eq_zero, Measure.measure_univ_eq_zero] at h2
  exact ae_iff.2 (h2.resolve_left hμ.2.1)

section
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem exists_isometry {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mat k r → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)}
    {Φ : Mat k r → Wp} (hπ : IsURepOn (UWset k r z) π) (hψ : ∀ n, ‖ψ n‖ = 1) (hΦ : IsSPsiEquiv z ψ π Φ)
    {a : Mat k r} (ha : a ∈ Sset k r z) : ∃ U : Wp ≃ₗᵢ[ℂ] Wp, ∀ g ∈ GG k r, Φ (a * g) = U (Φ g) := by
  obtain ⟨h, hh, m, hm, rfl⟩ := ha
  refine ⟨LinearIsometry.toLinearIsometryEquiv ⟨(ψ m • π h).toLinearMap, fun v => ?_⟩ rfl, fun g hg => hΦ h hh m hm g hg⟩
  show ‖ψ m • π h v‖ = ‖v‖
  rw [norm_smul, hψ, one_mul, hπ.2.1 h hh]

theorem hsNormSq_arrow (U : Wp ≃ₗᵢ[ℂ] Wp) (V : Wq ≃ₗᵢ[ℂ] Wq) (A : Wq →L[ℂ] Wp) :
    hsNormSq (V.toContinuousLinearEquiv.arrowCongr U.toContinuousLinearEquiv A) = hsNormSq A := by
  have e : V.toContinuousLinearEquiv.arrowCongr U.toContinuousLinearEquiv A =
      (U.toContinuousLinearEquiv : Wp →L[ℂ] Wp).comp (A.comp (V.symm.toContinuousLinearEquiv : Wq →L[ℂ] Wq)) := by
    ext v; simp
  have e2 : ∀ X Y : Wq →L[ℂ] Wp, hsInner X Y = Formalism.FourierDecayAlt.B.hsInner X Y := fun X Y =>
    (Formalism.FourierDecayAlt.P.Topx1.hsInner_eq X Y).symm
  unfold hsNormSq
  rw [e, e2, e2, Formalism.FourierDecayAlt.P.PBI.hsInner_comp_left _ (by simp), Formalism.FourierDecayAlt.P.PBI.hsInner_comp_right _ (by simp)]

theorem hsNormSq_ampJ_translate [CompleteSpace Wp] {ν : Measure (Mt k r)} (hν : ∀ᵐ x ∂ν, Matrix.of x ∈ GG k r) (c : ℝ)
    {Φ : Mat k r → Wp} {Φ' : Mat k r → Wq} {γ a a' : Mat k r} (hγ : γ ∈ GG k r) (ha' : IsUnit a'.det)
    (U : Wp ≃ₗᵢ[ℂ] Wp) (V : Wq ≃ₗᵢ[ℂ] Wq) (hU : ∀ g ∈ GG k r, Φ (a * g) = U (Φ g))
    (hV : ∀ g ∈ GG k r, Φ' (a' * g) = V (Φ' g)) :
    hsNormSq (ampJ (ν.map (lmulM a')) c Φ Φ' (a * γ * a'⁻¹)) = hsNormSq (ampJ ν c Φ Φ' γ) := by
  rw [← hsNormSq_arrow U V (ampJ ν c Φ Φ' γ)]
  congr 1
  unfold ampJ
  rw [map_smul, ← ContinuousLinearEquiv.integral_comp_comm]
  congr 1
  refine ((lmulE ha').measurableEmbedding.integral_map _).trans (integral_congr_ae ?_)
  filter_upwards [hν] with x hx
  have e : a * γ * a'⁻¹ * (a' * Matrix.of x) = a * (γ * Matrix.of x) := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ ha']
  show (innerSL ℂ (Φ' (a' * Matrix.of x))).smulRight (Φ (a * γ * a'⁻¹ * (a' * Matrix.of x))) = _
  rw [e, hV _ hx, hU _ (isClosedSub_GG.2.2.2.1 _ hγ _ hx)]
  ext v
  simp [← V.inner_map_map (Φ' (Matrix.of x)) (V.symm v)]

end

theorem ka_pos (D : D7) : 0 < D.host.ka := by
  refine div_pos Real.pi_pos ?_
  unfold Host.v Host.rdE
  have h : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
    abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero D.host.E))
  have := Real.rpow_pos_of_pos h ((1 : ℝ) / (Module.finrank ℚ D.host.E : ℝ))
  linarith

theorem hsNormSq_amp_doubleCoset : ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (A : LocS W), GoodW D τ w w' θ W → 0 < Tr D w → 0 < Tr D w' → IsSPsiEquiv W.z (psiS D W.z) W.π A.Φ → IsSPsiEquiv W.z' (psiS D W.z') W.π' A.Φ' → ContinuousOn A.Φ (UH (Hpk D.R.k D.R.rS)) → ContinuousOn A.Φ' (UH (Hpk D.R.k D.R.rS)) → ∀ (γ a a' : MatKR D.R.k D.R.rS) (p : Point ℂ (D.R.rS + 1)) (ν ν' : Measure (Mt D.R.k D.R.rS)), RelPt D W.z W.z' γ p → a ∈ Sset D.R.k D.R.rS W.z → a' ∈ Sset D.R.k D.R.rS W.z' → RMeas D W γ 1 ν → RMeas D W (a * γ * a'⁻¹) 1 ν' → hsNormSq (A.J ν' (a * γ * a'⁻¹)) = hsNormSq (A.J ν γ) := by
  rintro D τ w w' θ W A ⟨t1, t2, hz, hz', hT, hT', hG, -⟩ hw hw' hΦ hΦ' cΦ cΦ' γ a a' p ν ν' ⟨hγ, -, hGf⟩ ha ha'
    ⟨q, μ, hμ, hν⟩ ⟨q', μ', hμ', hν'⟩
  rw [← hT] at hw
  rw [← hT'] at hw'
  rw [ENNReal.ofReal_one, one_smul] at hν
  obtain ⟨s1, -⟩ := isClosedSub_Sset hz hw
  obtain ⟨s1', -, -, -, si'⟩ := isClosedSub_Sset hz' hw'
  obtain ⟨-, -, -, gm, gi⟩ := isClosedSub_GG (k := D.R.k) (r := D.R.rS)
  have hγ' : a * γ * a'⁻¹ ∈ GG D.R.k D.R.rS := gm _ (gm _ (s1 ha) _ hγ) _ (gi _ (s1' ha'))
  have hGf' : Gf D.R.k D.R.rS W.z W.z' (a * γ * a'⁻¹) ≠ 0 := by
    rwa [group_inverse_holds _ _ _ _ hz hz' a ha _ (si' _ ha') γ]
  have hπ := (GlobalTheory.Amp.Schur.type_irred hw t1).2.1
  have hπ' := (GlobalTheory.Amp.Schur.type_irred hw' t2).2.1
  have hψ : ∀ n, ‖psiS D W.z n‖ = 1 := (GlobalTheory.BesselPsi.psi_character _ _ _ _ hz).1
  have hψ' : ∀ n, ‖psiS D W.z' n‖ = 1 := (GlobalTheory.BesselPsi.psi_character _ _ _ _ hz').1
  have hH := (GlobalTheory.T.besselRootMeasure_independent_of_choices D W.z W.z' γ q q μ μ hz hz' hw hw' hγ hGf (ka_pos D) hμ hμ).2.2
  have hmv := GlobalTheory.T.rootMeasure_transport_doubleCoset D W.z W.z' q γ a a' μ hz hz' hw hw' hγ ha ha' hμ
  obtain ⟨-, e, hH'⟩ := GlobalTheory.T.besselRootMeasure_independent_of_choices D W.z W.z' _ q' q μ' _ hz hz' hw hw' hγ' hGf' (ka_pos D) hμ' hmv
  have hu := isUnit_det_of_mem_GG (s1' ha')
  have hq : IsQuotMeas W.μG μ' (ν.map (lmulM a')) := by
    rw [e]
    exact quot_translate hu (hG.2.2.2 _ (s1' ha')) hν
  have hrel : ∀ ρ ∈ Rset D.R.k D.R.rS (a * γ * a'⁻¹),
      psiS D W.z (a * γ * a'⁻¹ * ρ * (a * γ * a'⁻¹)⁻¹) = psiS D W.z' ρ := by
    obtain ⟨n, hn, n', hn', g, e1, e2, -⟩ := hμ'
    rw [e1] at hγ' ⊢
    exact fun ρ hρ => psi_cell hz hz' _ hn hn' hγ' e2 hρ
  have key := GlobalTheory.T.besselAmplitude_eq_smul_of_rescaled_stabilizerHaar _ _ W.Wp W.Wq W.z W.z' _ _ W.π W.π' A.Φ A.Φ' A.cN hz hz' hw hw' hπ hπ'
    (fun n _ => ⟨hψ n, hψ' n⟩) hΦ hΦ' cΦ cΦ' _ W.μG μ' _ ν' 1 hγ' hrel hG hH' one_pos hq hν'
  rw [Complex.ofReal_one, one_smul] at key
  obtain ⟨U, hU⟩ := exists_isometry hπ hψ hΦ ha
  obtain ⟨V, hV⟩ := exists_isometry hπ' hψ' hΦ' ha'
  unfold LocS.J
  rw [← key]
  exact hsNormSq_ampJ_translate (ae_mem_of_quot (fun x hx => hx.1.1) hG hH hν) _ hγ hu U V hU hV

end GlobalTheory.AmpCoset
