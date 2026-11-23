import CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.TorusMovesCharacter
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.DDFormC
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.AtFormC
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.AtFormAdmC
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.JacquetFunctionalNormalization
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SecondCountableQuotients.ModExists

open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.Upq.BesselFunctionalConstruction

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.S3dx6

variable {k r : ℕ}

theorem exists_move {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {c : ℂ} (hc : c ≠ 0) :
    ∃ b ∈ UH (Hpk k r), (∀ h ∈ UWset k r z, b * h = h * b) ∧ ∀ m ∈ Nset k r,
      b * m * b⁻¹ ∈ Nset k r ∧ b⁻¹ * m * b ∈ Nset k r ∧
        psi k r z cStd (b * m * b⁻¹) = psi k r z c m := by
  obtain ⟨a, ha, hac, haN⟩ := GlobalTheory.CompanionTheory.Bes.torus_moves_character k r z (fun _ => c) hz fun _ => hc
  obtain ⟨e, he, hec, heN⟩ := GlobalTheory.CompanionTheory.Bes.torus_moves_character k r z (fun _ => cStd) hz
    fun _ => by simp [cStd]
  have hi : (e⁻¹ * a)⁻¹ = a⁻¹ * e := by rw [Matrix.mul_inv_rev, inv_inv_uh he]
  have he1 := unit_of_uh he
  refine ⟨e⁻¹ * a, WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv he) ha, fun h hh => ?_, fun m hm => ?_⟩
  · have : e⁻¹ * h = h * e⁻¹ := by
      calc e⁻¹ * h = e⁻¹ * (h * e) * e⁻¹ := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, he1.1, Matrix.mul_one]
        _ = h * e⁻¹ := by rw [← hec h hh, ← Matrix.mul_assoc, he1.2, Matrix.one_mul]
    rw [Matrix.mul_assoc, hac h hh, ← Matrix.mul_assoc, this, Matrix.mul_assoc]
  · obtain ⟨h1, -, h3⟩ := haN m hm
    obtain ⟨-, h5, -⟩ := heN _ h1
    have e1 : e⁻¹ * a * m * (e⁻¹ * a)⁻¹ = e⁻¹ * (a * m * a⁻¹) * e := by
      rw [hi]; simp only [Matrix.mul_assoc]
    have e2 : (e⁻¹ * a)⁻¹ * m * (e⁻¹ * a) = a⁻¹ * (e * m * e⁻¹) * a := by
      rw [hi]; simp only [Matrix.mul_assoc]
    refine ⟨e1 ▸ h5, e2 ▸ (haN _ (heN m hm).1).2.1, ?_⟩
    have h6 := (heN _ h5).2.2
    have e3 : e * (e⁻¹ * (a * m * a⁻¹) * e) * e⁻¹ = a * m * a⁻¹ := by
      rw [show e * (e⁻¹ * (a * m * a⁻¹) * e) * e⁻¹ = (e * e⁻¹) * (a * m * a⁻¹) * (e * e⁻¹) by
        simp only [Matrix.mul_assoc], he1.1, Matrix.one_mul, Matrix.mul_one]
    rw [e3, h3] at h6
    rw [e1, psi_constant, psi_constant]
    exact h6.symm

def cjE {b : Mx k r} (hb : b ∈ UH (Hpk k r)) : Mt k r ≃ₜ Mt k r where
  toFun x := b * Matrix.of x * b⁻¹
  invFun x := b⁻¹ * Matrix.of x * b
  left_inv x := by
    change b⁻¹ * (b * Matrix.of x * b⁻¹) * b = Matrix.of x
    rw [show b⁻¹ * (b * Matrix.of x * b⁻¹) * b = (b⁻¹ * b) * Matrix.of x * (b⁻¹ * b) by
      simp only [Matrix.mul_assoc], (unit_of_uh hb).2, Matrix.one_mul, Matrix.mul_one]
  right_inv x := by
    change b * (b⁻¹ * Matrix.of x * b) * b⁻¹ = Matrix.of x
    rw [show b * (b⁻¹ * Matrix.of x * b) * b⁻¹ = (b * b⁻¹) * Matrix.of x * (b * b⁻¹) by
      simp only [Matrix.mul_assoc], (unit_of_uh hb).1, Matrix.one_mul, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem isHaarOn_map_cjE {b : Mx k r} (hb : b ∈ UH (Hpk k r)) {N : Set (Mx k r)}
    (hN : ∀ m ∈ N, b * m * b⁻¹ ∈ N ∧ b⁻¹ * m * b ∈ N) {μ : Measure (Mt k r)}
    (hμ : PI.BesselPeriodGGP.IsHaarOn N μ) : PI.BesselPeriodGGP.IsHaarOn N (μ.map (cjE hb)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hμ
  have hE := (cjE hb).measurableEmbedding
  refine ⟨(cjE hb).toMeasurableEquiv.sigmaFinite_map, fun h0 => h2 ?_, ?_, fun s hs => ?_⟩
  · rwa [Measure.map_eq_zero_iff hE.measurable.aemeasurable] at h0
  · rw [hE.map_apply]
    exact measure_mono_null (fun x hx hx' => hx (hN _ hx').1) h3
  · have hl : ∀ a : Mx k r, Measurable (lmulM (k := k) (r := r) a) := fun a =>
      ModEx.measurable_lmulQ a
    have e : lmulM s ∘ cjE hb = cjE hb ∘ lmulM (b⁻¹ * s * b) := by
      ext1 x
      change s * (b * Matrix.of x * b⁻¹) = b * (b⁻¹ * s * b * Matrix.of x) * b⁻¹
      rw [show b * (b⁻¹ * s * b * Matrix.of x) * b⁻¹ = (b * b⁻¹) * (s * (b * Matrix.of x * b⁻¹)) by
        simp only [Matrix.mul_assoc], (unit_of_uh hb).1, Matrix.one_mul]
    rw [Measure.map_map (hl s) hE.measurable, e, ← Measure.map_map hE.measurable (hl _),
      h4 _ (hN s hs).2]

section One

variable {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx k r → (H →L[ℂ] H)} {w0 : H} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [CompleteSpace Wp] [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ}
  {π : Mx k r → (Wp →L[ℂ] Wp)} {μW μN μG νq : Measure (Mt k r)}

theorem be_rank_one_scale (hS : Side k r ε lam h σ w0 z c u π μW μN μG νq) :
    ∃ L : H → Wp, ∀ w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
        be z c π σ μW μN w v = (innerSL ℂ (L v)).smulRight (L w) := by
  obtain ⟨hl, hσ, hg, hok, -, hz, hT, hc, hπ, hW, hN, -⟩ := hS
  obtain ⟨b, hb, hbW, hbN⟩ := exists_move hz hc
  have hN' := isHaarOn_map_cjE hb (fun m hm => ⟨(hbN m hm).1, (hbN m hm).2.1⟩) hN
  obtain ⟨L, hL⟩ := CompanionTheory.FamilyDerivativeExpansion.M1.be_rank_one hok.1 hl hσ hg hok.2.1 hz hT hπ hW hN'
  have hU : PI.WBL.Cv.SigU σ := PI.WBL.Cv.sigAll k r ε lam H σ hσ
  refine ⟨fun w => L (σ b w), fun w hw v hv => ?_⟩
  rw [← (hL _ (TranslationBesselVanishing.smooth_translate hσ hw hb) _ (TranslationBesselVanishing.smooth_translate hσ hv hb)).2]
  haveI := hW.1
  haveI := hN.1
  have hE := ((Homeomorph.refl (Mt k r)).prodCongr (cjE hb)).measurableEmbedding
  have hp : μW.prod (μN.map (cjE hb)) =
      (μW.prod μN).map ((Homeomorph.refl (Mt k r)).prodCongr (cjE hb)) := by
    conv_lhs => rw [← Measure.map_id (μ := μW)]
    exact Measure.map_prod_map _ _ measurable_id (cjE hb).measurable
  unfold be
  rw [hp, hE.integral_map]
  refine integral_congr_ae ?_
  have h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := hW.2.2.1
  have h2 : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r := hN.2.2.1
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae h1, Measure.quasiMeasurePreserving_snd.ae h2]
    with p hp1 hp2
  change _ = (⟪σ b v, σ (Matrix.of p.1 * (b * Matrix.of p.2 * b⁻¹)) (σ b w)⟫_ℂ *
    star (psi k r z cStd (b * Matrix.of p.2 * b⁻¹))) • π (Matrix.of p.1)⁻¹
  have hx : Matrix.of p.1 * (b * Matrix.of p.2 * b⁻¹) ∈ UH (Hpk k r) :=
    WeylGroupFacts.uh_mul hp1.1 (hbN _ hp2).1.1
  have e1 : b⁻¹ * (Matrix.of p.1 * (b * Matrix.of p.2 * b⁻¹) * b) =
      Matrix.of p.1 * Matrix.of p.2 := by
    rw [show b⁻¹ * (Matrix.of p.1 * (b * Matrix.of p.2 * b⁻¹) * b) =
      b⁻¹ * (Matrix.of p.1 * b) * Matrix.of p.2 * (b⁻¹ * b) by simp only [Matrix.mul_assoc],
      ← hbW _ hp1, ← Matrix.mul_assoc b⁻¹, (unit_of_uh hb).2, Matrix.one_mul, Matrix.mul_one]
  rw [(hbN _ hp2).2.2, inner_sig hU hb, ← ContinuousLinearMap.comp_apply (σ _) (σ b),
    ← hU.2.1 _ hx _ hb, ← ContinuousLinearMap.comp_apply (σ b⁻¹),
    ← hU.2.1 _ (WeylGroupFacts.uh_inv hb) _ (WeylGroupFacts.uh_mul hx hb), e1]
  rfl

end One

theorem shapeC : C.Shape := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS ⟨x0, hx0, y0, hy0, hne⟩
  have hsm := DDSmoothness.DD_smooth hIn.2.2.1 hS.1 hS.2.1 hS.2.2.2.2.1
  obtain ⟨L, hL⟩ := be_rank_one_scale hS
  rw [hL x0 (hsm x0 hx0) y0 (hsm y0 hy0)] at hne
  have hLx : L x0 ≠ 0 := fun h0 => hne (by ext ξ; simp [h0])
  have hLy : L y0 ≠ 0 := fun h0 => hne (by ext ξ; simp [h0])
  have hn : ⟪L y0, L y0⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hLy
  have hB := DDSmoothness.bessel_smul
    (beBessel hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS y0 (Or.inl hy0) (L y0))
    (⟪L y0, L y0⟫_ℂ)⁻¹
  have he : ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      (⟪L y0, L y0⟫_ℂ)⁻¹ • be z c π σ μW μN x y0 (L y0) = L x := fun x hx => by
    rw [hL x hx y0 (hsm y0 hy0), ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul,
      inv_mul_cancel₀ hn, one_smul]
  refine ⟨_, hB, ⟨x0, hx0, by rw [he x0 (hsm x0 hx0)]; exact hLx⟩, fun x hx v hv => ?_⟩
  rw [he x hx, he v (hsm v hv), hL x hx v (hsm v hv)]

section Forms

variable {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx k r → (H →L[ℂ] H)} {w0 : H} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [CompleteSpace Wp] [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ}
  {π : Mx k r → (Wp →L[ℂ] Wp)} {μW μN μG νq : Measure (Mt k r)}

theorem dDForm_scale (hS : Side k r ε lam h σ w0 z c u π μW μN μG νq) :
    DDForm z c π μW μN μG νq σ w0 :=
  DDSmoothness.GC.discrete_form_one_side psi_constant schur_hermitian norm_inverse_bound
    growth_spherical_bound growth_group_bound decDD beConv normIdSm beBessel shapeC inputs_holds
    k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS

theorem atForm_scale (hS : Side k r ε lam h σ w0 z c u π μW μN μG νq) :
    AtForm z c π μW μN μG νq σ :=
  DDSmoothness.GC.smooth_K_finite_form_one_side schur_hermitian beConv normIdSm beBessel shapeC kFinForm zeroCase
    inputs_holds k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS

theorem atFormAdm_scale (hS : Side k r ε lam h σ w0 z c u π μW μN μG νq) :
    AtFormAdm z c π μW μN μG νq σ w0 :=
  UnipotentHaarMeasurability.GC.smooth_admissible_form_one_side schur_hermitian beConv normIdSm beBessel shapeC kFinForm
    zeroCase zeroCaseDD inputs_holds k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS

end Forms

end CompanionTheory.D.Upq.BesselFunctionalConstruction

end
