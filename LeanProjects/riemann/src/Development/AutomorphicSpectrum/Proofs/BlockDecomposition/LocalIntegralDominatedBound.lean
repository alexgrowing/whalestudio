import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Th
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Gauge
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaHaarMeasureDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalZetaOfAnnulusFunction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerBoundOnBoundedRows
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2ZetaUnfolding
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2ZetaUnfolding.MajLg

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def fL (W₂ : GL (Fin 2) F → ℂ) (τ R : ℝ) (a : Fˣ) (g : GL (Fin 2) F) : ENNReal :=
  (box2 R).indicator (fun _ => (1 : ENNReal)) g.val *
    ENNReal.ofReal (‖W₂ (dg2 a 1 * g)‖ * (modulus ((g.val).det) : ℝ) ^ (τ + 1 / 2))

def ballS (R : ℝ) : Set F := {x | (modulus x : ℝ) ≤ R}

def Gset (R B : ℝ) (a : Fˣ) : Set (Fˣ × Fˣ) :=
  {q | (modulus (q.2 : F) : ℝ) ≤ R ∧ (modulus ((q.1 * q.2 : Fˣ) : F) : ℝ) ≤ R ∧
    (modulus ((a * q.1 : Fˣ) : F) : ℝ) ≤ B}

def Gm (τ R B δ : ℝ) (a : Fˣ) (q : Fˣ × Fˣ) : ENNReal :=
  (Gset R B a).indicator (fun q => ENNReal.ofReal ((modulus ((a * q.1 : Fˣ) : F) : ℝ) ^ δ *
    (modulus (q.1 : F) : ℝ) ^ (τ - 1 / 2) * (modulus (q.2 : F) : ℝ) ^ (2 * τ))) q

omit [MeasurableSpace F] [BorelSpace F] in
theorem norm_reduce (W₂ : GL (Fin 2) F → ℂ)
    (hN : ∀ x g, ‖W₂ (uni2 x * g)‖ = ‖W₂ g‖) (hZ : ∀ (a : Fˣ) g, ‖W₂ (dg2 a a * g)‖ = ‖W₂ g‖)
    (a a' b' : Fˣ) (k : GL (Fin 2) F) (x : F) :
    ‖W₂ (dg2 a 1 * (uni2 x * hI (a', b', k)))‖ = ‖W₂ (dg2 (a * a') 1 * k)‖ := by
  have e : dg2 a 1 * (uni2 x * hI (a', b', k)) =
      uni2 (((a * 1⁻¹ : Fˣ) : F) * x) * (dg2 b' b' * (dg2 (a * a') 1 * k)) := by
    simp only [hI]
    rw [← mul_assoc, GlobalTheory.CompanionTheory.IwaHaar.diagonal_mul_unipotent, mul_assoc, ← mul_assoc (dg2 a 1),
      GlobalTheory.CompanionTheory.IwaHaar.diagonal_mul_diagonal_alt, ← mul_assoc (dg2 b' b'), GlobalTheory.CompanionTheory.IwaHaar.diagonal_mul_diagonal_alt]
    have h : a * (a' * b') = b' * (a * a') := by ac_rfl
    simp only [one_mul, mul_one, h]
  rw [e, hN, hZ]

omit [MeasurableSpace F] [BorelSpace F] in
theorem box_mul {R : ℝ} (hR : 0 ≤ R) {A k : Matrix (Fin 2) (Fin 2) F} (hA : A ∈ box2 R)
    (hk : ∀ i j, k i j ∈ 𝒪[F]) : A * k ∈ box2 R := by
  intro i j
  have hm : ∀ l, (modulus (A i l * k l j) : ℝ) ≤ R := by
    intro l
    have h1 : (modulus (k l j) : ℝ) ≤ 1 := by exact_mod_cast modulus_le_one_iff.2 (hk l j)
    rw [modulus_mul, NNReal.coe_mul]
    calc (modulus (A i l) : ℝ) * modulus (k l j) ≤ R * 1 :=
          mul_le_mul (hA i l) h1 (NNReal.coe_nonneg _) hR
      _ = R := mul_one R
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  have h := GlobalTheory.CompanionTheory.GJTwo.WhitBound.modulus_add_le_max (A i 0 * k 0 j) (A i 1 * k 1 j)
  have h' : (modulus (A i 0 * k 0 j + A i 1 * k 1 j) : ℝ) ≤
      max (modulus (A i 0 * k 0 j) : ℝ) (modulus (A i 1 * k 1 j) : ℝ) := by exact_mod_cast h
  exact h'.trans (max_le (hm 0) (hm 1))

omit [MeasurableSpace F] [BorelSpace F] in
theorem box_coords {R : ℝ} (hR : 0 ≤ R) {a' b' : Fˣ} {k : GL (Fin 2) F}
    (hk : k ∈ GLnLocal.integralGL F 2) {x : F} (h : (uni2 x * hI (a', b', k)).val ∈ box2 R) :
    (modulus (b' : F) : ℝ) ≤ R ∧ (modulus ((a' * b' : Fˣ) : F) : ℝ) ≤ R ∧
      (modulus ((b' : F) * x) : ℝ) ≤ R := by
  have h2 := box_mul hR h ((GLnLocal.mem_integralGL_iff F 2).1 hk).2
  have e : (uni2 x * hI (a', b', k)).val * (k⁻¹).val = !![((a' * b' : Fˣ) : F), x * b'; 0, b'] := by
    rw [← Units.val_mul]
    simp only [hI, mul_assoc, mul_inv_cancel, mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two]
  rw [e] at h2
  refine ⟨by simpa using h2 1 1, by simpa using h2 0 0, ?_⟩
  have h3 := h2 0 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h3
  rwa [mul_comm]

omit [MeasurableSpace F] [BorelSpace F] in
theorem modulus_det_K {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) :
    modulus (k.val).det = 1 := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hk
  have d1 : (k.val).det ∈ 𝒪[F] := by
    rw [Matrix.det_fin_two]
    exact sub_mem (mul_mem (h1 0 0) (h1 1 1)) (mul_mem (h1 0 1) (h1 1 0))
  have d2 : ((k⁻¹).val).det ∈ 𝒪[F] := by
    rw [Matrix.det_fin_two]
    exact sub_mem (mul_mem (h2 0 0) (h2 1 1)) (mul_mem (h2 0 1) (h2 1 0))
  have m1 : modulus (k.val).det ≤ 1 := modulus_le_one_iff.2 d1
  have m2 : modulus ((k⁻¹).val).det ≤ 1 := modulus_le_one_iff.2 d2
  have e : modulus (k.val).det * modulus ((k⁻¹).val).det = 1 := by
    rw [← modulus_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel]
    simp [modulus_one]
  refine le_antisymm m1 ?_
  calc (1 : NNReal) = modulus (k.val).det * modulus ((k⁻¹).val).det := e.symm
    _ ≤ modulus (k.val).det * 1 := mul_le_mul_of_nonneg_left m2 zero_le
    _ = modulus (k.val).det := mul_one _

omit [MeasurableSpace F] [BorelSpace F] in
theorem modulus_det_iw {a' b' : Fˣ} {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) (x : F) :
    (modulus ((uni2 x * hI (a', b', k)).val).det : ℝ) =
      (modulus (a' : F) : ℝ) * (modulus (b' : F) : ℝ) ^ 2 := by
  have e : ((uni2 x * hI (a', b', k)).val).det = (a' : F) * b' * b' * (k.val).det := by
    simp only [hI, Units.val_mul, Matrix.det_mul]
    simp [uni2, dg2, Matrix.det_fin_two]
  rw [e, modulus_mul, modulus_mul, modulus_mul, modulus_det_K hk]
  push_cast
  ring

theorem real_bound {u v m w C τ δ : ℝ} (hu : 0 < u) (hv : 0 < v) (hw : w ≤ C * m ^ δ) :
    u⁻¹ * (w * (u * v ^ 2) ^ (τ + 1 / 2)) ≤ v * C * (m ^ δ * u ^ (τ - 1 / 2) * v ^ (2 * τ)) := by
  have e1 : (u * v ^ 2) ^ (τ + 1 / 2) = u ^ (τ - 1 / 2) * u * (v ^ (2 * τ) * v) := by
    rw [Real.mul_rpow hu.le (by positivity), ← Real.rpow_natCast v 2, ← Real.rpow_mul hv.le]
    have a1 : u ^ (τ + 1 / 2) = u ^ (τ - 1 / 2) * u := by
      rw [← Real.rpow_add_one hu.ne']; congr 1; ring
    have a2 : v ^ (((2 : ℕ) : ℝ) * (τ + 1 / 2)) = v ^ (2 * τ) * v := by
      rw [← Real.rpow_add_one hv.ne']; congr 1; push_cast; ring
    rw [a1, a2]
  have hP : 0 ≤ u ^ (τ - 1 / 2) * (v ^ (2 * τ) * v) := by positivity
  have e2 : u⁻¹ * (w * (u * v ^ 2) ^ (τ + 1 / 2)) = w * (u ^ (τ - 1 / 2) * (v ^ (2 * τ) * v)) := by
    rw [e1]; field_simp
  have e3 : v * C * (m ^ δ * u ^ (τ - 1 / 2) * v ^ (2 * τ)) =
      C * m ^ δ * (u ^ (τ - 1 / 2) * (v ^ (2 * τ) * v)) := by ring
  rw [e2, e3]
  exact mul_le_mul_of_nonneg_right hw hP

theorem pointwise (W₂ : GL (Fin 2) F → ℂ)
    (hN : ∀ x g, ‖W₂ (uni2 x * g)‖ = ‖W₂ g‖) (hZ : ∀ (a : Fˣ) g, ‖W₂ (dg2 a a * g)‖ = ‖W₂ g‖)
    {τ R C B δ : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hB : ∀ (a : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2, ‖W₂ (dg2 a 1 * k)‖ ≤ C * (modulus (a : F) : ℝ) ^ δ ∧
      (W₂ (dg2 a 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B))
    (a a' b' : Fˣ) {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) (x : F) :
    ENNReal.ofReal (wR ((a', b', k) : Fˣ × Fˣ × GL (Fin 2) F)) *
        fL W₂ τ R a (uni2 x * hI (a', b', k)) ≤
      ((modulus (b' : F) : ENNReal) * ENNReal.ofReal C * Gm τ R B δ a (a', b')) *
        (ballS R : Set F).indicator 1 ((b' : F) * x) := by
  by_cases hb : (uni2 x * hI (a', b', k)).val ∈ box2 R
  swap
  · rw [fL, Set.indicator_of_notMem hb]
    simp
  have hnorm := norm_reduce W₂ hN hZ a a' b' k x
  by_cases hw : W₂ (dg2 (a * a') 1 * k) = 0
  · have h0 : ‖W₂ (dg2 a 1 * (uni2 x * hI (a', b', k)))‖ = 0 := by rw [hnorm, hw, norm_zero]
    simp [fL, h0]
  obtain ⟨h1, h2, h3⟩ := box_coords hR.le hk hb
  obtain ⟨hb1, hb2⟩ := hB (a * a') k hk
  have hS : ((a', b') : Fˣ × Fˣ) ∈ Gset R B a := ⟨h1, h2, hb2 hw⟩
  have hT : (b' : F) * x ∈ (ballS R : Set F) := h3
  have hu : (0 : ℝ) < (modulus (a' : F) : ℝ) := by exact_mod_cast modulus_pos a'.ne_zero
  have hv : (0 : ℝ) < (modulus (b' : F) : ℝ) := by exact_mod_cast modulus_pos b'.ne_zero
  rw [Gm, Set.indicator_of_mem hS, Set.indicator_of_mem hT, fL, Set.indicator_of_mem hb]
  simp only [Pi.one_apply, one_mul, mul_one]
  rw [hnorm, modulus_det_iw hk x, ← ENNReal.ofReal_coe_nnreal (p := modulus (b' : F)),
    ← ENNReal.ofReal_mul hv.le, ← ENNReal.ofReal_mul (mul_nonneg hv.le hC),
    ← ENNReal.ofReal_mul (by simp only [wR]; positivity)]
  exact ENNReal.ofReal_le_ofReal (real_bound hu hv hb1)

omit [MeasurableSpace F] [BorelSpace F] in
theorem isClosed_ballS (R : ℝ) : IsClosed (ballS R : Set F) :=
  isClosed_le (NNReal.continuous_coe.comp continuous_modulus) continuous_const

theorem measurable_fL {W₂ : GL (Fin 2) F → ℂ} (hW : Continuous W₂) (τ R : ℝ) (a : Fˣ) :
    Measurable (fL W₂ τ R a) := by
  have hcl : IsClosed {g : GL (Fin 2) F | g.val ∈ box2 R} := by
    have e : {g : GL (Fin 2) F | g.val ∈ box2 R} =
        ⋂ i, ⋂ j, {g : GL (Fin 2) F | (modulus (g.val i j) : ℝ) ≤ R} := by
      ext g
      simp [box2]
    rw [e]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_le
      (NNReal.continuous_coe.comp (continuous_modulus.comp
        (Continuous.matrix_elem (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) F)) i j))) continuous_const
  have e : fL W₂ τ R a = fun g => {g : GL (Fin 2) F | g.val ∈ box2 R}.indicator (fun _ => (1 : ENNReal)) g *
      ENNReal.ofReal (‖W₂ (dg2 a 1 * g)‖ * (modulus ((g.val).det) : ℝ) ^ (τ + 1 / 2)) := by
    funext g
    by_cases h : g.val ∈ box2 R
    · rw [fL, Set.indicator_of_mem h, Set.indicator_of_mem (show g ∈ {g : GL (Fin 2) F | g.val ∈ box2 R} from h)]
    · rw [fL, Set.indicator_of_notMem h, Set.indicator_of_notMem (show g ∉ {g : GL (Fin 2) F | g.val ∈ box2 R} from h)]
  rw [e]
  have hd : Measurable fun g : GL (Fin 2) F => (modulus ((g.val).det) : ℝ) ^ (τ + 1 / 2) :=
    ((NNReal.continuous_coe.comp (continuous_modulus.comp
      (Continuous.matrix_det Units.continuous_val))).measurable).pow_const _
  have hn : Measurable fun g : GL (Fin 2) F => ‖W₂ (dg2 a 1 * g)‖ :=
    (hW.comp (continuous_const.mul continuous_id)).norm.measurable
  exact (measurable_const.indicator hcl.measurableSet).mul (hn.mul hd).ennreal_ofReal

theorem measurable_Gm (τ R B δ : ℝ) (a : Fˣ) : Measurable (Gm (F := F) τ R B δ a) := by
  have hm : Measurable fun u : Fˣ => (modulus (u : F) : ℝ) :=
    (NNReal.continuous_coe.comp (continuous_modulus.comp Units.continuous_val)).measurable
  have h1 : Measurable fun q : Fˣ × Fˣ => (modulus (q.1 : F) : ℝ) := hm.comp measurable_fst
  have h2 : Measurable fun q : Fˣ × Fˣ => (modulus (q.2 : F) : ℝ) := hm.comp measurable_snd
  have e3 : ∀ (c : Fˣ) (u : Fˣ), (modulus ((c * u : Fˣ) : F) : ℝ) = (modulus (c : F) : ℝ) * modulus (u : F) := by
    intro c u
    rw [Units.val_mul, modulus_mul, NNReal.coe_mul]
  have h3 : Measurable fun q : Fˣ × Fˣ => (modulus ((a * q.1 : Fˣ) : F) : ℝ) := by
    simp only [e3]
    exact measurable_const.mul h1
  have h4 : Measurable fun q : Fˣ × Fˣ => (modulus ((q.1 * q.2 : Fˣ) : F) : ℝ) := by
    simp only [e3]
    exact h1.mul h2
  have hS : MeasurableSet (Gset (F := F) R B a) :=
    (measurableSet_le h2 measurable_const).inter
      ((measurableSet_le h4 measurable_const).inter (measurableSet_le h3 measurable_const))
  have hG : Measurable fun q : Fˣ × Fˣ => ENNReal.ofReal ((modulus ((a * q.1 : Fˣ) : F) : ℝ) ^ δ *
      (modulus (q.1 : F) : ℝ) ^ (τ - 1 / 2) * (modulus (q.2 : F) : ℝ) ^ (2 * τ)) :=
    (((h3.pow_const _).mul (h1.pow_const _)).mul (h2.pow_const _)).ennreal_ofReal
  exact hG.indicator hS

theorem inner_le (ψ : AddChar F Circle) (W₂ : GL (Fin 2) F → ℂ)
    (hN : ∀ x g, ‖W₂ (uni2 x * g)‖ = ‖W₂ g‖) (hZ : ∀ (a : Fˣ) g, ‖W₂ (dg2 a a * g)‖ = ‖W₂ g‖)
    {τ R C B δ : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hB : ∀ (a : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2, ‖W₂ (dg2 a 1 * k)‖ ≤ C * (modulus (a : F) : ℝ) ^ δ ∧
      (W₂ (dg2 a 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B))
    (a a' b' : Fˣ) {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) :
    ∫⁻ x, ENNReal.ofReal (wR ((a', b', k) : Fˣ × Fˣ × GL (Fin 2) F)) *
        fL W₂ τ R a (uni2 x * hI (a', b', k)) ∂selfDualMeasure ψ ≤
      ENNReal.ofReal C * selfDualMeasure ψ (ballS R : Set F) * Gm τ R B δ a (a', b') := by
  have hT := (isClosed_ballS (F := F) R).measurableSet
  have hv0 : (modulus (b' : F) : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.2 (modulus_ne_zero b'.ne_zero)
  have hm : Measurable fun x : F => (ballS R : Set F).indicator (1 : F → ENNReal) ((b' : F) * x) :=
    (measurable_one.indicator hT).comp (measurable_const_mul _)
  calc _ ≤ ∫⁻ x, ((modulus (b' : F) : ENNReal) * ENNReal.ofReal C * Gm τ R B δ a (a', b')) *
        (ballS R : Set F).indicator 1 ((b' : F) * x) ∂selfDualMeasure ψ :=
        lintegral_mono fun x => pointwise W₂ hN hZ hC hR hB a a' b' hk x
    _ = ((modulus (b' : F) : ENNReal) * ENNReal.ofReal C * Gm τ R B δ a (a', b')) *
        (((modulus (b' : F) : ENNReal))⁻¹ * selfDualMeasure ψ (ballS R : Set F)) := by
        rw [lintegral_const_mul _ hm,
          lintegral_comp_mul_left (selfDualMeasure ψ) b'.ne_zero ((ballS R : Set F).indicator 1),
          lintegral_indicator_one hT]
    _ = _ := by
        have h1 : (modulus (b' : F) : ENNReal) * ((modulus (b' : F) : ENNReal))⁻¹ = 1 :=
          ENNReal.mul_inv_cancel hv0 ENNReal.coe_ne_top
        calc _ = ((modulus (b' : F) : ENNReal) * ((modulus (b' : F) : ENNReal))⁻¹) *
              (ENNReal.ofReal C * selfDualMeasure ψ (ballS R : Set F) * Gm τ R B δ a (a', b')) := by ring
          _ = _ := by rw [h1, one_mul]

theorem outer_eq (ψ : AddChar F Circle) {G : Fˣ × Fˣ → ENNReal} (hG : Measurable G) :
    ∫⁻ p, G (p.1, p.2.1) ∂mIw ψ =
      LFS.hG ψ (K2 F) * ∫⁻ a' : Fˣ, ∫⁻ b' : Fˣ, G (a', b') ∂multHaar F ∂multHaar F := by
  haveI := GlobalTheory.CompanionTheory.IwaHaar.finite_restrict ψ
  have hm : Measurable fun p : Fˣ × Fˣ × GL (Fin 2) F => G (p.1, p.2.1) :=
    hG.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hH : LFS.hG ψ (K2 F) ≠ ⊤ := by
    haveI := GlobalTheory.CompanionTheory.IwaHaar.haar_inst ψ
    exact (GLnLocal.isCompact_integralGL F 2).measure_lt_top.ne
  have hin : ∀ a' : Fˣ, ∫⁻ y, G (a', y.1) ∂((multHaar F).prod ((LFS.hG ψ).restrict (K2 F))) =
      LFS.hG ψ (K2 F) * ∫⁻ b', G (a', b') ∂multHaar F := by
    intro a'
    have hm' : Measurable fun y : Fˣ × GL (Fin 2) F => G (a', y.1) :=
      hG.comp (measurable_const.prodMk measurable_fst)
    rw [lintegral_prod _ hm'.aemeasurable]
    simp only [lintegral_const, Measure.restrict_apply_univ]
    rw [lintegral_mul_const' _ _ hH, mul_comm]
  unfold mIw
  rw [lintegral_prod _ hm.aemeasurable]
  refine (lintegral_congr fun a' => hin a').trans ?_
  rw [lintegral_const_mul' _ _ hH]

end D

end GlobalTheory.CompanionTheory.GL2ZetaUnfolding.MajLg

open GlobalTheory.CompanionTheory.GL2ZetaUnfolding.MajLg in

theorem GlobalTheory.CompanionTheory.GL2ZetaUnfolding.MajLg.main : ForS fun F _ _ _ _ _ _ ψ => ∀ (W₂ : GL (Fin 2) F → ℂ), Continuous W₂ →
  (∀ x g, ‖W₂ (uni2 x * g)‖ = ‖W₂ g‖) → (∀ (a : Fˣ) g, ‖W₂ (dg2 a a * g)‖ = ‖W₂ g‖) →
  ∀ (τ R C B δ : ℝ), 0 ≤ C → 0 < R →
  (∀ (a : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2, ‖W₂ (dg2 a 1 * k)‖ ≤ C * (modulus (a : F) : ℝ) ^ δ ∧
    (W₂ (dg2 a 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B)) →
  ∃ D : ENNReal, D ≠ ⊤ ∧ ∀ a : Fˣ, large₂ ψ W₂ τ R a ≤ D * ∫⁻ a' : Fˣ, ∫⁻ b' : Fˣ,
    {q : Fˣ × Fˣ | (modulus (q.2 : F) : ℝ) ≤ R ∧ (modulus ((q.1 * q.2 : Fˣ) : F) : ℝ) ≤ R ∧
        (modulus ((a * q.1 : Fˣ) : F) : ℝ) ≤ B}.indicator
      (fun q => ENNReal.ofReal ((modulus ((a * q.1 : Fˣ) : F) : ℝ) ^ δ * (modulus (q.1 : F) : ℝ) ^ (τ - 1 / 2) *
        (modulus (q.2 : F) : ℝ) ^ (2 * τ))) (a', b') ∂multHaar F ∂multHaar F := by
  intro F _ _ _ _ _ _ ψ hψ W₂ hW hN hZ τ R C B δ hC hR hB
  obtain ⟨c, hc0, hcT, hc⟩ := GlobalTheory.CompanionTheory.IwaHaar.main F ψ hψ
  haveI := GlobalTheory.CompanionTheory.IwaHaar.haar_inst ψ
  have hV : selfDualMeasure ψ (ballS R : Set F) ≠ ⊤ :=
    (GlobalTheory.CompanionTheory.LFDual.ZRho.isCompact_modulus_le (F := F) R).measure_lt_top.ne
  have hH : LFS.hG ψ (K2 F) ≠ ⊤ := (GLnLocal.isCompact_integralGL F 2).measure_lt_top.ne
  refine ⟨c⁻¹ * (ENNReal.ofReal C * selfDualMeasure ψ (ballS R : Set F) * LFS.hG ψ (K2 F)),
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc0)
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV) hH), fun a => ?_⟩
  have hL : large₂ ψ W₂ τ R a = c⁻¹ * ∫⁻ p, ∫⁻ x, ENNReal.ofReal (wR p) *
      fL W₂ τ R a (uni2 x * hI p) ∂selfDualMeasure ψ ∂mIw ψ := by
    rw [hc _ (measurable_fL hW τ R a), ← mul_assoc, ENNReal.inv_mul_cancel hc0 hcT, one_mul]
    rfl
  have hle : ∫⁻ p, ∫⁻ x, ENNReal.ofReal (wR p) * fL W₂ τ R a (uni2 x * hI p) ∂selfDualMeasure ψ ∂mIw ψ ≤
      ∫⁻ p, ENNReal.ofReal C * selfDualMeasure ψ (ballS R : Set F) * Gm τ R B δ a (p.1, p.2.1) ∂mIw ψ := by
    refine lintegral_mono_ae ?_
    filter_upwards [GlobalTheory.CompanionTheory.LocalTestVectors.ae_mem_maximal_compact ψ] with p hk
    obtain ⟨a', b', k⟩ := p
    exact inner_le ψ W₂ hN hZ hC hR hB a a' b' hk
  have hout := outer_eq ψ (measurable_Gm (F := F) τ R B δ a)
  have hmG : Measurable fun p : Fˣ × Fˣ × GL (Fin 2) F => Gm τ R B δ a (p.1, p.2.1) :=
    (measurable_Gm (F := F) τ R B δ a).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  rw [lintegral_const_mul _ hmG, hout] at hle
  rw [hL]
  calc _ ≤ c⁻¹ * (ENNReal.ofReal C * selfDualMeasure ψ (ballS R : Set F) * (LFS.hG ψ (K2 F) *
        ∫⁻ a' : Fˣ, ∫⁻ b' : Fˣ, Gm τ R B δ a (a', b') ∂multHaar F ∂multHaar F)) := by gcongr
    _ = _ := by
      simp only [Gm, Gset]
      ring
