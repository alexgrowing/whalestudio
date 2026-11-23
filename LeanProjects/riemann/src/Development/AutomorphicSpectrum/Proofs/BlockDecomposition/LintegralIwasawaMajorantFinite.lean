import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Aq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaIntegralRightTranslateInvariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralDetSecondVectorFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralBoundedModulusPowerFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactTranslateEntriesBounded
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestVectorNonvanishingLocal
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.ZetaIntegralBound

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def Af (B e : ℝ) (a : Fˣ) : ENNReal :=
  Set.indicator {a : Fˣ | (modulus (a : F) : ℝ) ≤ B} (fun a => ENNReal.ofReal ((modulus (a : F) : ℝ) ^ e)) a

def ball2 (R : ℝ) : Set (GL (Fin 2) F) := {g | ∀ i j, (modulus (g.val i j) : ℝ) ≤ R}

def Ck (R ε : ℝ) (g k : GL (Fin 2) F) : ENNReal :=
  Set.indicator (ball2 R) (fun g => ENNReal.ofReal
    (((modulus (g.val).det : ℝ) / mx (e2r (k * g)) ^ 2) ^ (1 / 2 - ε))) g

omit [MeasurableSpace F] [BorelSpace F] in
theorem mx_pos (g : GL (Fin 2) F) : 0 < mx (e2r g) := by
  by_contra h
  have h' : mx (e2r g) ≤ 0 := not_lt.1 h
  have h0 : (modulus (g.val 1 0) : ℝ) ≤ 0 := (le_max_left _ _).trans h'
  have h1 : (modulus (g.val 1 1) : ℝ) ≤ 0 := (le_max_right _ _).trans h'
  have e0 : g.val 1 0 = 0 := by
    by_contra hne
    have : (0 : ℝ) < (modulus (g.val 1 0) : ℝ) := by exact_mod_cast modulus_pos hne
    linarith
  have e1 : g.val 1 1 = 0 := by
    by_contra hne
    have : (0 : ℝ) < (modulus (g.val 1 1) : ℝ) := by exact_mod_cast modulus_pos hne
    linarith
  have hd : (g.val).det = 0 := by rw [Matrix.det_fin_two, e0, e1]; ring
  have hu : IsUnit (g.val).det := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  exact hu.ne_zero hd

omit [MeasurableSpace F] [BorelSpace F] in
theorem det_pos (g : GL (Fin 2) F) : 0 < (modulus (g.val).det : ℝ) := by
  have hu : IsUnit (g.val).det := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  exact_mod_cast modulus_pos hu.ne_zero

omit [MeasurableSpace F] [BorelSpace F] in
theorem cont_entry (i j : Fin 2) : Continuous fun g : GL (Fin 2) F => (modulus (g.val i j) : ℝ) :=
  NNReal.continuous_coe.comp (continuous_modulus.comp
    (Continuous.matrix_elem Units.continuous_val i j))

omit [MeasurableSpace F] [BorelSpace F] in
theorem cont_mx : Continuous fun g : GL (Fin 2) F => mx (e2r g) := by
  have : (fun g : GL (Fin 2) F => mx (e2r g)) =
      fun g => max (modulus (g.val 1 0) : ℝ) (modulus (g.val 1 1) : ℝ) := by
    funext g; simp [mx, e2r]
  rw [this]
  exact (cont_entry 1 0).max (cont_entry 1 1)

omit [MeasurableSpace F] [BorelSpace F] in
theorem cont_det : Continuous fun g : GL (Fin 2) F => (modulus (g.val).det : ℝ) :=
  NNReal.continuous_coe.comp (continuous_modulus.comp
    (Continuous.matrix_det Units.continuous_val))

theorem rpow_alg {d m σ ε : ℝ} (hd : 0 < d) (hm : 0 < m) :
    d ^ (σ + 1 / 2) * (d / m ^ 2) ^ (1 / 2 - ε) = d ^ (σ + 1 - ε) * m ^ (-(1 - 2 * ε)) := by
  have e1 : (m ^ 2) ^ (1 / 2 - ε) = m ^ (1 - 2 * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm.le]
    congr 1
    push_cast
    ring
  have e2 : d ^ (σ + 1 - ε) = d ^ (σ + 1 / 2) * d ^ (1 / 2 - ε) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  rw [Real.div_rpow hd.le (by positivity), e1, e2, Real.rpow_neg hm.le, div_eq_mul_inv]
  ring

theorem measurable_Af (B e : ℝ) : Measurable (Af (F := F) B e) := by
  have hm : Continuous fun a : Fˣ => (modulus (a : F) : ℝ) :=
    NNReal.continuous_coe.comp (continuous_modulus.comp Units.continuous_val)
  exact Measurable.indicator (ENNReal.measurable_ofReal.comp (hm.measurable.pow_const e))
    (measurableSet_le hm.measurable measurable_const)

omit [MeasurableSpace F] [BorelSpace F] in
theorem isClosed_ball2 (R : ℝ) : IsClosed (ball2 (F := F) R) := by
  simp only [ball2, Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_le (cont_entry i j) continuous_const

theorem measurable_Ck (R ε : ℝ) :
    Measurable fun q : GL (Fin 2) F × GL (Fin 2) F => Ck R ε q.1 q.2 := by
  haveI : SecondCountableTopology (GL (Fin 2) F) := GlobalTheory.CompanionTheory.LocalTestVectors.secondCountable_GL2
  have e : (fun q : GL (Fin 2) F × GL (Fin 2) F => Ck R ε q.1 q.2) =
      Set.indicator (Prod.fst ⁻¹' ball2 R) (fun q => ENNReal.ofReal
        (((modulus (q.1.val).det : ℝ) / mx (e2r (q.2 * q.1)) ^ 2) ^ (1 / 2 - ε))) := by
    funext q
    rfl
  rw [e]
  have h1 : Continuous fun q : GL (Fin 2) F × GL (Fin 2) F => (modulus (q.1.val).det : ℝ) :=
    cont_det.comp continuous_fst
  have h2 : Continuous fun q : GL (Fin 2) F × GL (Fin 2) F => mx (e2r (q.2 * q.1)) :=
    cont_mx.comp (continuous_snd.mul continuous_fst)
  exact Measurable.indicator (ENNReal.measurable_ofReal.comp
    ((h1.measurable.div (h2.measurable.pow_const 2)).pow_const _))
    (measurable_fst (isClosed_ball2 R).measurableSet)

theorem measurable_Ck_right (R ε : ℝ) (g : GL (Fin 2) F) : Measurable (Ck (F := F) R ε g) :=
  Measurable.comp (g := fun q : GL (Fin 2) F × GL (Fin 2) F => Ck R ε q.1 q.2)
    (f := fun k : GL (Fin 2) F => (g, k)) (measurable_Ck R ε) measurable_prodMk_left

theorem integrand_eq (R B σ ε : ℝ) (g : GL (Fin 2) F) (p : Fˣ × Fˣ × GL (Fin 2) F) :
    ENNReal.ofReal (wR p) * ENNReal.ofReal (Mj R B σ ε g p) =
      Af B (σ - 2 * ε) p.1 * (Af R (2 * σ) p.2.1 * Ck R ε g p.2.2) := by
  obtain ⟨a, b, k⟩ := p
  have ha : (0 : ℝ) < (modulus (a : F) : ℝ) := by exact_mod_cast modulus_pos a.ne_zero
  have hb : (0 : ℝ) < (modulus (b : F) : ℝ) := by exact_mod_cast modulus_pos b.ne_zero
  have hE : 0 ≤ ((modulus (g.val).det : ℝ) / mx (e2r (k * g)) ^ 2) ^ (1 / 2 - ε) :=
    Real.rpow_nonneg (div_nonneg (det_pos g).le (by positivity)) _
  simp only [Mj, wR]
  by_cases h : (∀ i j, (modulus (g.val i j) : ℝ) ≤ R) ∧ (modulus (b : F) : ℝ) ≤ R ∧ (modulus (a : F) : ℝ) ≤ B
  · rw [if_pos h]
    obtain ⟨h1, h2, h3⟩ := h
    have m1 : g ∈ ball2 R := h1
    have m2 : b ∈ {a : Fˣ | (modulus (a : F) : ℝ) ≤ R} := h2
    have m3 : a ∈ {a : Fˣ | (modulus (a : F) : ℝ) ≤ B} := h3
    rw [Af, Af, Ck, Set.indicator_of_mem m1, Set.indicator_of_mem m2, Set.indicator_of_mem m3,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have e : (modulus (a : F) : ℝ) ^ (σ + 1 - 2 * ε) =
        (modulus (a : F) : ℝ) ^ (σ - 2 * ε) * (modulus (a : F) : ℝ) := by
      rw [show σ + 1 - 2 * ε = (σ - 2 * ε) + 1 by ring, Real.rpow_add ha, Real.rpow_one]
    rw [e]
    field_simp
  · rw [if_neg h, ENNReal.ofReal_zero, mul_zero]
    by_cases h1 : g ∈ ball2 R
    · by_cases h2 : (modulus (b : F) : ℝ) ≤ R
      · have h3 : ¬ (modulus (a : F) : ℝ) ≤ B := fun h3 => h ⟨h1, h2, h3⟩
        have m3 : a ∉ {a : Fˣ | (modulus (a : F) : ℝ) ≤ B} := h3
        simp only [Af]
        rw [Set.indicator_of_notMem m3, zero_mul]
      · have m2 : b ∉ {a : Fˣ | (modulus (a : F) : ℝ) ≤ R} := h2
        simp only [Af]
        rw [Set.indicator_of_notMem m2, zero_mul, mul_zero]
    · simp only [Ck]
      rw [Set.indicator_of_notMem h1, mul_zero, mul_zero]

theorem inner_eq (ψ : AddChar F Circle) [SFinite (LFS.hG ψ)] (R B σ ε : ℝ) (g : GL (Fin 2) F) :
    ∫⁻ p, ENNReal.ofReal (wR p) * ENNReal.ofReal (Mj R B σ ε g p) ∂mIw ψ =
      (∫⁻ a, Af B (σ - 2 * ε) a ∂multHaar F) * ((∫⁻ b, Af R (2 * σ) b ∂multHaar F) *
        ∫⁻ k, Ck R ε g k ∂(LFS.hG ψ).restrict (K2 F)) := by
  have hC : Measurable (Ck (F := F) R ε g) := measurable_Ck_right R ε g
  simp_rw [integrand_eq]
  unfold mIw
  rw [lintegral_prod_mul (f := Af B (σ - 2 * ε))
      (g := fun q : Fˣ × GL (Fin 2) F => Af R (2 * σ) q.1 * Ck R ε g q.2)
      (measurable_Af _ _).aemeasurable
      (((measurable_Af _ _).comp measurable_fst).mul (hC.comp measurable_snd)).aemeasurable,
    lintegral_prod_mul (f := Af R (2 * σ)) (g := Ck R ε g)
      (measurable_Af _ _).aemeasurable hC.aemeasurable]

theorem factor_le {R σ ε : ℝ} {k : GL (Fin 2) F} (hk : k ∈ K2 F) (g : GL (Fin 2) F) :
    ENNReal.ofReal ((modulus (g.val).det : ℝ) ^ (σ + 1 / 2)) * Ck R ε g k ≤
      Set.indicator (ball2 R) (fun g : GL (Fin 2) F => ENNReal.ofReal
        ((modulus (g.val).det : ℝ) ^ (σ + 1 - ε) * mx (e2r g) ^ (-(1 - 2 * ε)))) (k * g) := by
  by_cases hg : g ∈ ball2 R
  · have hkg : k * g ∈ ball2 R := fun i j => by
      have := GlobalTheory.CompanionTheory.LFCoords.modulus_mul_entry_le (κ := k.val) (k := g.val)
        ((GLnLocal.mem_integralGL_iff F 2).1 hk).1 hg i j
      simpa [Units.val_mul] using this
    have hd : modulus ((k * g).val).det = modulus (g.val).det := by
      rw [Units.val_mul, Matrix.det_mul, modulus_mul, GlobalTheory.CompanionTheory.KHBound.modulus_det_integralGL hk, one_mul]
    rw [Ck, Set.indicator_of_mem hg, Set.indicator_of_mem hkg,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (det_pos g).le _), hd,
      rpow_alg (det_pos g) (mx_pos (k * g))]
  · rw [Ck, Set.indicator_of_notMem hg, mul_zero]
    exact zero_le

theorem outer_finite : ForS fun F _ _ _ _ _ _ ψ => ∀ R B σ ε : ℝ, 0 < ε → 2 * ε < σ → ε < 1 / 2 →
  ∫⁻ g, ENNReal.ofReal ((modulus (g.val).det : ℝ) ^ (σ + 1 / 2)) *
    ∫⁻ p, ENNReal.ofReal (wR p) * ENNReal.ofReal (Mj R B σ ε g p) ∂mIw ψ ∂LFS.hG ψ < ⊤ := by
  intro F _ _ _ _ _ _ ψ hψ R B σ ε h0 h1 h2
  haveI : (LFS.hG ψ).IsHaarMeasure := by unfold LFS.hG; infer_instance
  haveI : SFinite (LFS.hG ψ) := by unfold LFS.hG; infer_instance
  have hKc : IsCompact (K2 F) := GLnLocal.isCompact_integralGL F 2
  have hKm : MeasurableSet (K2 F) := hKc.isClosed.measurableSet
  have hA₁ : (∫⁻ a, Af B (σ - 2 * ε) a ∂multHaar F) < ⊤ :=
    GlobalTheory.T.lintegral_bounded_modulus_power_finite F ψ hψ B (σ - 2 * ε) (by linarith)
  have hA₂ : (∫⁻ b, Af R (2 * σ) b ∂multHaar F) < ⊤ :=
    GlobalTheory.T.lintegral_bounded_modulus_power_finite F ψ hψ R (2 * σ) (by linarith)
  have hT : (∫⁻ g, Set.indicator (ball2 R) (fun g : GL (Fin 2) F => ENNReal.ofReal
      ((modulus (g.val).det : ℝ) ^ (σ + 1 - ε) * mx (e2r g) ^ (-(1 - 2 * ε)))) g ∂LFS.hG ψ) < ⊤ :=
    GlobalTheory.T.lintegral_det_second_vector_finite F ψ hψ R (σ + 1 - ε) (1 - 2 * ε) (by linarith) (by linarith) (by linarith)
  set A₁ := ∫⁻ a, Af B (σ - 2 * ε) a ∂multHaar F
  set A₂ := ∫⁻ b, Af R (2 * σ) b ∂multHaar F
  set H := Set.indicator (ball2 R) (fun g : GL (Fin 2) F => ENNReal.ofReal
      ((modulus (g.val).det : ℝ) ^ (σ + 1 - ε) * mx (e2r g) ^ (-(1 - 2 * ε))))
  set T := ∫⁻ g, H g ∂LFS.hG ψ
  set D := fun g : GL (Fin 2) F => ENNReal.ofReal ((modulus (g.val).det : ℝ) ^ (σ + 1 / 2))
  have hD : Measurable D := ENNReal.measurable_ofReal.comp
    (cont_det.measurable.pow_const _)
  have hJ : Measurable (Function.uncurry fun (g k : GL (Fin 2) F) => D g * Ck R ε g k) :=
    (hD.comp measurable_fst).mul (measurable_Ck R ε)
  have hAA : A₁ * A₂ ≠ ⊤ := (ENNReal.mul_lt_top hA₁ hA₂).ne
  have step : ∀ g : GL (Fin 2) F, D g *
      ∫⁻ p, ENNReal.ofReal (wR p) * ENNReal.ofReal (Mj R B σ ε g p) ∂mIw ψ =
      (A₁ * A₂) * ∫⁻ k, D g * Ck R ε g k ∂(LFS.hG ψ).restrict (K2 F) := by
    intro g
    have hC : Measurable (Ck (F := F) R ε g) := measurable_Ck_right R ε g
    rw [inner_eq, lintegral_const_mul _ hC]
    ring
  have hin : ∀ k ∈ K2 F, ∫⁻ g, D g * Ck R ε g k ∂LFS.hG ψ ≤ T := by
    intro k hk
    calc ∫⁻ g, D g * Ck R ε g k ∂LFS.hG ψ ≤ ∫⁻ g, H (k * g) ∂LFS.hG ψ :=
          lintegral_mono fun g => factor_le hk g
      _ = T := lintegral_mul_left_eq_self H k
  have hfin : (LFS.hG ψ).restrict (K2 F) Set.univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact hKc.measure_lt_top
  calc ∫⁻ g, D g * ∫⁻ p, ENNReal.ofReal (wR p) * ENNReal.ofReal (Mj R B σ ε g p) ∂mIw ψ ∂LFS.hG ψ
      = ∫⁻ g, (A₁ * A₂) * ∫⁻ k, D g * Ck R ε g k ∂(LFS.hG ψ).restrict (K2 F) ∂LFS.hG ψ :=
        lintegral_congr step
    _ = (A₁ * A₂) * ∫⁻ g, ∫⁻ k, D g * Ck R ε g k ∂(LFS.hG ψ).restrict (K2 F) ∂LFS.hG ψ :=
        lintegral_const_mul' _ _ hAA
    _ = (A₁ * A₂) * ∫⁻ k, ∫⁻ g, D g * Ck R ε g k ∂LFS.hG ψ ∂(LFS.hG ψ).restrict (K2 F) := by
        rw [lintegral_lintegral_swap hJ.aemeasurable]
    _ ≤ (A₁ * A₂) * ∫⁻ _k, T ∂(LFS.hG ψ).restrict (K2 F) := by
        exact mul_le_mul' le_rfl (setLIntegral_mono' hKm hin)
    _ = (A₁ * A₂) * (T * (LFS.hG ψ).restrict (K2 F) Set.univ) := by rw [lintegral_const]
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hA₁ hA₂) (ENNReal.mul_lt_top hT hfin)

end GlobalTheory.CompanionTheory.ZetaIntegralBound
