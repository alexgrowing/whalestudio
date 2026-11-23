import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.UnipotentTateFunctionalEquation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MajorantScaled
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralKernelUniformBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MajorantLeSumSwap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateLocalL1
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AestronglyMeasurableWhittakerDiagUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Ga
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralUnitPowDecayLeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableWhittakerInnerQuotientInvStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralMajorantTorusLtTopStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MajorantLeConstMulTorusStatement

noncomputable section
open MeasureTheory Matrix Filter Topology Ad3 Ad3.K Ad3.K.LC Ad3.K.LC.C
namespace GlobalTheory.CompanionTheory.PerUC

def rtEquiv (g : GL (Fin 3) ℂ) : M23 ≃L[ℝ] M23 :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun X => Matrix.of.symm (Matrix.of X * (g : Matrix (Fin 3) (Fin 3) ℂ))
      invFun := fun X => Matrix.of.symm (Matrix.of X * ((g⁻¹ : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ))
      map_add' := fun X Y => by
        show Matrix.of.symm ((Matrix.of X + Matrix.of Y) * (g : Matrix (Fin 3) (Fin 3) ℂ)) = _
        rw [Matrix.add_mul]
        rfl
      map_smul' := fun c X => by
        show Matrix.of.symm ((c • Matrix.of X) * (g : Matrix (Fin 3) (Fin 3) ℂ)) = _
        rw [Matrix.smul_mul]
        rfl
      left_inv := fun X => by
        simp [Matrix.mul_assoc]
      right_inv := fun X => by
        simp [Matrix.mul_assoc] }

def rtS (g : GL (Fin 3) ℂ) (Ψ : Sw) : Sw :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((rtEquiv g).prodCongr (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℂ))) Ψ

theorem rtS_apply (g : GL (Fin 3) ℂ) (Ψ : Sw) (X : M23) (q : Fin 2 → ℂ) :
    rtS g Ψ (X, q) = Ψ (Matrix.of.symm (Matrix.of X * (g : Matrix (Fin 3) (Fin 3) ℂ)), q) := by
  simp [rtS, rtEquiv]

theorem innQ_rt (Ψ : Sw) (g : GL (Fin 3) ℂ) (h : M22) (β : ℂ) :
    innQ Ψ g h β = innQ (rtS g Ψ) 1 h β := by
  funext q
  unfold innQ
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [rtS_apply]

theorem pS_nonneg {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (N : ℕ)
    (f : SchwartzMap E ℂ) : 0 ≤ pS N f :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => apply_nonneg _ _

theorem pS_mono {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℕ} (hab : a ≤ b)
    (f : SchwartzMap E ℂ) : pS a f ≤ pS b f := by
  unfold pS
  have hs : Finset.range (a + 1) ⊆ Finset.range (b + 1) :=
    Finset.range_subset_range.2 (by omega)
  refine (Finset.sum_le_sum fun i _ => ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hs fun i _ _ => Finset.sum_nonneg fun _ _ => apply_nonneg _ _)
  exact Finset.sum_le_sum_of_subset_of_nonneg hs fun _ _ _ => apply_nonneg _ _

theorem eta_entries (h : M22) : eta h 0 = (Matrix.of h).det⁻¹ * (-h 1 0) ∧
    eta h 1 = (Matrix.of h).det⁻¹ * h 0 0 := by
  constructor <;> simp [eta, Matrix.inv_def, Matrix.adjugate_fin_two]

theorem norm_eta (h : M22) (hd : (Matrix.of h).det ≠ 0) :
    ‖eta h‖ = GlobalTheory.CompanionTheory.MajC.col h / GlobalTheory.CompanionTheory.MajC.dt h := by
  have := (GlobalTheory.CompanionTheory.MajC.L_eta h hd).2
  rw [← this]
  rfl

theorem Yb_inv (h : M22) (hd : (Matrix.of h).det ≠ 0) : Yb (Matrix.of h)⁻¹ = yb h := by
  have hD : 0 < GlobalTheory.CompanionTheory.MajC.dt h := norm_pos_iff.2 hd
  obtain ⟨e0, e1⟩ := eta_entries h
  have a0 : ((Matrix.of h)⁻¹) 1 0 = (Matrix.of h).det⁻¹ * (-h 1 0) := e0
  have a1 : ((Matrix.of h)⁻¹) 1 1 = (Matrix.of h).det⁻¹ * h 0 0 := e1
  have hdet : ((Matrix.of h)⁻¹).det = (Matrix.of h).det⁻¹ := by
    rw [Matrix.det_nonsing_inv]
    simp
  unfold Yb yb rr
  rw [hdet, a0, a1]
  simp only [norm_mul, norm_inv, norm_neg]
  change (GlobalTheory.CompanionTheory.MajC.dt h)⁻¹ ^ 2 / (((GlobalTheory.CompanionTheory.MajC.dt h)⁻¹ * ‖h 1 0‖) ^ 2 + ((GlobalTheory.CompanionTheory.MajC.dt h)⁻¹ * ‖h 0 0‖) ^ 2) ^ 2 = _
  have hc := (GlobalTheory.CompanionTheory.MajC.L_eta h hd).1
  have hR : 0 < ‖h 0 0‖ ^ 2 + ‖h 1 0‖ ^ 2 := by
    rcases max_cases ‖h 0 0‖ ‖h 1 0‖ with ⟨e, -⟩ | ⟨e, -⟩ <;>
      · unfold GlobalTheory.CompanionTheory.MajC.col at hc
        rw [e] at hc
        positivity
  have e : ((GlobalTheory.CompanionTheory.MajC.dt h)⁻¹ * ‖h 1 0‖) ^ 2 + ((GlobalTheory.CompanionTheory.MajC.dt h)⁻¹ * ‖h 0 0‖) ^ 2 =
      ((GlobalTheory.CompanionTheory.MajC.dt h)⁻¹) ^ 2 * (‖h 0 0‖ ^ 2 + ‖h 1 0‖ ^ 2) := by ring
  rw [e]
  generalize ‖h 0 0‖ ^ 2 + ‖h 1 0‖ ^ 2 = R at hR
  field_simp

theorem norm_chC' (n : ℤ) (s : ℂ) (t : ℂˣ) : ‖chC n s t‖ = ‖(t : ℂ)‖ ^ (2 * s.re) := by
  have ht : 0 < ‖(t : ℂ)‖ := norm_pos_iff.2 t.ne_zero
  have h1 : ‖((t : ℂ) / ‖(t : ℂ)‖)‖ = 1 := by
    rw [norm_div, Complex.norm_real, norm_norm, div_self ht.ne']
  unfold chC
  rw [norm_mul, norm_zpow, h1, _root_.one_zpow, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  norm_num

theorem measurable_chC' (n : ℤ) (s : ℂ) : Measurable (chC n s) := by
  have hv : Measurable (Units.val : ℂˣ → ℂ) := GlobalTheory.CompanionTheory.TateC.val_measurableEmbedding.measurable
  have h1 : Measurable fun a : ℂˣ => ph n (a : ℂ) := (GlobalTheory.CompanionTheory.GodementFE.measurable_ph n).comp hv
  have h2 : Measurable fun a : ℂˣ => (((‖(a : ℂ)‖ ^ 2 : ℝ) : ℂ)) ^ s := by
    refine Measurable.pow_const ?_ s
    exact Complex.measurable_ofReal.comp ((hv.norm).pow_const 2)
  exact h1.mul h2

theorem gx_nonneg (σ : ℝ) (N : ℕ) (h : M22) : 0 ≤ gx σ N h := by
  have hD : 0 ≤ GlobalTheory.CompanionTheory.MajC.dt h := norm_nonneg _
  have hc : 0 ≤ GlobalTheory.CompanionTheory.MajC.col h := le_max_of_le_left (norm_nonneg _)
  have hy : 0 ≤ yb h := by unfold yb; positivity
  unfold gx
  positivity

theorem rr_swp (h : M22) : rr (GlobalTheory.CompanionTheory.MajC.swp h) = rr h := by
  simp [rr, GlobalTheory.CompanionTheory.MajC.swp, add_comm]

theorem gx_swp (σ : ℝ) (N : ℕ) (h : M22) : gx σ N (GlobalTheory.CompanionTheory.MajC.swp h) = gx σ N h := by
  unfold gx yb
  rw [GlobalTheory.CompanionTheory.MajC.dt_swp, GlobalTheory.CompanionTheory.MajC.col_swp, GlobalTheory.CompanionTheory.MajC.norm_swp, rr_swp]

theorem measurable_swp : Measurable GlobalTheory.CompanionTheory.MajC.swp := by
  unfold GlobalTheory.CompanionTheory.MajC.swp
  refine measurable_pi_lambda _ fun i => ?_
  fin_cases i
  · exact measurable_pi_apply 1
  · exact measurable_pi_apply 0

theorem measurable_gx (σ : ℝ) (N : ℕ) : Measurable (gx σ N) := by
  have hdt : Measurable GlobalTheory.CompanionTheory.MajC.dt := by
    unfold GlobalTheory.CompanionTheory.MajC.dt
    simp only [Matrix.det_fin_two, Matrix.of_apply]
    fun_prop
  have hcol : Measurable GlobalTheory.CompanionTheory.MajC.col := by
    unfold GlobalTheory.CompanionTheory.MajC.col
    fun_prop
  have hrr : Measurable rr := by
    unfold rr
    fun_prop
  have hyb : Measurable yb := by
    unfold yb
    fun_prop
  have hlog : Measurable fun h => Real.log (yb h) := Real.measurable_log.comp hyb
  unfold gx
  fun_prop

theorem hint : ∀ σ : ℝ, 0 < σ → σ < 1 → ∃ N₀ : ℕ, ∀ N ≥ N₀, Integrable (gx σ N) := by
  intro σ h0 h1
  obtain ⟨hm, hn, hl⟩ := GlobalTheory.T.lintegral_majorant_torus_lt_top σ h0 h1
  obtain ⟨C, N₀, hC⟩ := GlobalTheory.T.majorant_le_const_mul_torus σ h0 h1
  refine ⟨N₀, fun N hN => ?_⟩
  have i1 : Integrable (ga σ 4) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hn)]
    exact hl
  have i2 : Integrable (fun h => ga σ 4 (GlobalTheory.CompanionTheory.MajC.swp h)) := by
    refine ⟨(hm.comp measurable_swp).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun h => hn _),
      GlobalTheory.CompanionTheory.MajC.L_swp (fun h => ENNReal.ofReal (ga σ 4 h))]
    exact hl
  refine Integrable.mono' ((i1.add i2).const_mul |C|) (measurable_gx σ N).aestronglyMeasurable
    (Filter.Eventually.of_forall fun h => ?_)
  rw [Real.norm_of_nonneg (gx_nonneg σ N h)]
  have g1 := hn h
  have g2 := hn (GlobalTheory.CompanionTheory.MajC.swp h)
  have hCa := abs_nonneg C
  have key : ∀ h : M22, ‖h 1 0‖ ≤ ‖h 0 0‖ → GlobalTheory.CompanionTheory.MajC.dt h ≠ 0 → gx σ N h ≤ |C| * ga σ 4 h :=
    fun h a b => (hC N hN h a b).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (hn h))
  show gx σ N h ≤ |C| * (ga σ 4 h + ga σ 4 (GlobalTheory.CompanionTheory.MajC.swp h))
  by_cases hd : GlobalTheory.CompanionTheory.MajC.dt h = 0
  · have : gx σ N h = 0 := by
      simp [gx, hd]
    rw [this]
    positivity
  by_cases hv : ‖h 1 0‖ ≤ ‖h 0 0‖
  · have := key h hv hd
    nlinarith
  · have hv' : ‖(GlobalTheory.CompanionTheory.MajC.swp h) 1 0‖ ≤ ‖(GlobalTheory.CompanionTheory.MajC.swp h) 0 0‖ := by
      have : ‖h 0 0‖ ≤ ‖h 1 0‖ := (not_le.1 hv).le
      simpa [GlobalTheory.CompanionTheory.MajC.swp] using this
    have := key _ hv' (by rw [GlobalTheory.CompanionTheory.MajC.dt_swp]; exact hd)
    rw [gx_swp] at this
    nlinarith

theorem norm_integrand (k : ℕ) (Ψ : Sw) (n : ℤ) (s : ℂ) (t : ℂˣ) (h : M22) :
    ‖chC n s t * ((‖(t : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹ *
      (((‖(Matrix.of h).det‖⁻¹ : ℝ) : ℂ) * W2 k (innQ Ψ 1 h (t : ℂ)⁻¹) (Matrix.of h)⁻¹)‖ =
      ‖(t : ℂ)‖ ^ (2 * s.re - 2) * ((GlobalTheory.CompanionTheory.MajC.dt h)⁻¹ * ‖W2 k (innQ Ψ 1 h (t : ℂ)⁻¹) (Matrix.of h)⁻¹‖) := by
  have ht : 0 < ‖(t : ℂ)‖ := norm_pos_iff.2 t.ne_zero
  have e : ‖(t : ℂ)‖ ^ (2 * s.re - 2) = ‖(t : ℂ)‖ ^ (2 * s.re) * (‖(t : ℂ)‖ ^ 2)⁻¹ := by
    rw [Real.rpow_sub ht, div_eq_mul_inv, Real.rpow_two]
  rw [norm_mul, norm_mul, norm_mul, norm_chC', norm_inv, Complex.norm_real, Complex.norm_real, e]
  simp [GlobalTheory.CompanionTheory.MajC.dt]

theorem main : IbpQ → WhittakerSchwartzBound → UnipotentJointIntegrability := by
  intro hIbp hW k hk Ψ n s hs0 hs1 u
  obtain ⟨N₀, hG⟩ := hint s.re hs0 hs1
  set N := max N₀ 4 with hN
  have hGN := hG N (le_max_left _ _)
  obtain ⟨C₂, N₂, hC₂⟩ := hW k hk N
  set Nb := max N N₂ with hNb
  obtain ⟨C₁, N₁, hC₁⟩ := hIbp Nb
  have hN4 : 4 ≤ Nb := (le_max_right _ _).trans (le_max_left _ _)
  have hNb4 : 4 - 4 * s.re ≤ (Nb : ℝ) := by
    have : (4 : ℝ) ≤ Nb := by exact_mod_cast hN4
    linarith
  obtain ⟨K, hK⟩ := GlobalTheory.T.integral_unit_pow_decay_le s.re hs1 Nb hNb4
  set Ψ' : Sw := rtS (cyc u) Ψ with hΨ'
  have hrw : ∀ (h : M22) (β : ℂ), innQ Ψ (cyc u) h β = innQ Ψ' 1 h β := fun h β => innQ_rt _ _ _ _
  simp only [hrw]
  set A : ℝ := |C₂| * |C₁ * pS N₁ Ψ'| with hA
  have hA0 : 0 ≤ A := by positivity
  set X : M22 → ℝ := fun h => yb h ^ ((1 : ℝ) / 2) * (1 + |Real.log (yb h)|) / (1 + yb h) ^ N with hX
  have hy0 : ∀ h, 0 ≤ yb h := fun h => by unfold yb; positivity
  have hX0 : ∀ h, 0 ≤ X h := fun h => by
    have := hy0 h
    simp only [hX]
    positivity
  have hWb : ∀ (h : M22) (t : ℂˣ), (Matrix.of h).det ≠ 0 →
      ‖W2 k (innQ Ψ' 1 h (t : ℂ)⁻¹) (Matrix.of h)⁻¹‖ ≤
        A * ((GlobalTheory.CompanionTheory.MajC.dt h ^ 2)⁻¹ / ((1 + ‖h‖) ^ Nb * (1 + ‖(t : ℂ)⁻¹‖ * ‖eta h‖) ^ Nb)) * X h := by
    intro h t hd
    obtain ⟨f, hf, hfb⟩ := hC₁ Ψ' h (t : ℂ)⁻¹ hd
    have hM : ((Matrix.of h)⁻¹).det ≠ 0 := by
      rw [Matrix.det_nonsing_inv]
      simpa using hd
    have b := hC₂ f _ hM
    rw [Yb_inv h hd] at b
    rw [← hf]
    have hQ : 0 ≤ (GlobalTheory.CompanionTheory.MajC.dt h ^ 2)⁻¹ / ((1 + ‖h‖) ^ Nb * (1 + ‖(t : ℂ)⁻¹‖ * ‖eta h‖) ^ Nb) := by
      have : 0 ≤ GlobalTheory.CompanionTheory.MajC.dt h := norm_nonneg _
      positivity
    have hp : pS N₂ f ≤ |C₁ * pS N₁ Ψ'| *
        ((GlobalTheory.CompanionTheory.MajC.dt h ^ 2)⁻¹ / ((1 + ‖h‖) ^ Nb * (1 + ‖(t : ℂ)⁻¹‖ * ‖eta h‖) ^ Nb)) := by
      refine (pS_mono (le_max_right _ _) f).trans (hfb.trans ?_)
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) hQ
    calc _ ≤ C₂ * pS N₂ f * yb h ^ ((1 : ℝ) / 2) * (1 + |Real.log (yb h)|) / (1 + yb h) ^ N := b
      _ = (C₂ * pS N₂ f) * X h := by simp only [hX]; ring
      _ ≤ (|C₂| * pS N₂ f) * X h := by
          refine mul_le_mul_of_nonneg_right ?_ (hX0 h)
          exact mul_le_mul_of_nonneg_right (le_abs_self _) (pS_nonneg _ _)
      _ ≤ (|C₂| * (|C₁ * pS N₁ Ψ'| *
            ((GlobalTheory.CompanionTheory.MajC.dt h ^ 2)⁻¹ / ((1 + ‖h‖) ^ Nb * (1 + ‖(t : ℂ)⁻¹‖ * ‖eta h‖) ^ Nb)))) * X h := by
          refine mul_le_mul_of_nonneg_right ?_ (hX0 h)
          exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)
      _ = _ := by rw [hA]; ring
  set E : M22 → ℝ := fun h => A * (((GlobalTheory.CompanionTheory.MajC.dt h ^ 3)⁻¹ * X h) / (1 + ‖h‖) ^ N) with hE
  have hE0 : ∀ h, 0 ≤ E h := fun h => by
    have := hX0 h
    have h2 : 0 ≤ GlobalTheory.CompanionTheory.MajC.dt h := norm_nonneg _
    simp only [hE]
    positivity
  have hpt : ∀ (h : M22) (t : ℂˣ), (Matrix.of h).det ≠ 0 →
      ‖(t : ℂ)‖ ^ (2 * s.re - 2) * ((GlobalTheory.CompanionTheory.MajC.dt h)⁻¹ * ‖W2 k (innQ Ψ' 1 h (t : ℂ)⁻¹) (Matrix.of h)⁻¹‖) ≤
        E h * (‖(t : ℂ)‖ ^ (2 * s.re - 2) / (1 + ‖(t : ℂ)⁻¹‖ * ‖eta h‖) ^ Nb) := by
    intro h t hd
    have hD : 0 < GlobalTheory.CompanionTheory.MajC.dt h := norm_pos_iff.2 hd
    have hT : 0 ≤ ‖(t : ℂ)‖ ^ (2 * s.re - 2) := Real.rpow_nonneg (norm_nonneg _) _
    have hq : 0 < (1 + ‖(t : ℂ)⁻¹‖ * ‖eta h‖) ^ Nb := by positivity
    have hP : (1 + ‖h‖) ^ N ≤ (1 + ‖h‖) ^ Nb :=
      pow_le_pow_right₀ (by linarith [norm_nonneg h]) (le_max_left _ _)
    have hP0 : 0 < (1 + ‖h‖) ^ N := by positivity
    have h1 := hWb h t hd
    have h2 : A * ((GlobalTheory.CompanionTheory.MajC.dt h ^ 2)⁻¹ / ((1 + ‖h‖) ^ Nb * (1 + ‖(t : ℂ)⁻¹‖ * ‖eta h‖) ^ Nb)) * X h ≤
        A * ((GlobalTheory.CompanionTheory.MajC.dt h ^ 2)⁻¹ / ((1 + ‖h‖) ^ N * (1 + ‖(t : ℂ)⁻¹‖ * ‖eta h‖) ^ Nb)) * X h := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hA0) (hX0 h)
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_right hP hq.le)
    calc _ ≤ ‖(t : ℂ)‖ ^ (2 * s.re - 2) * ((GlobalTheory.CompanionTheory.MajC.dt h)⁻¹ *
          (A * ((GlobalTheory.CompanionTheory.MajC.dt h ^ 2)⁻¹ / ((1 + ‖h‖) ^ N * (1 + ‖(t : ℂ)⁻¹‖ * ‖eta h‖) ^ Nb)) * X h)) := by
          refine mul_le_mul_of_nonneg_left ?_ hT
          exact mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
      _ = _ := by
          simp only [hE]
          field_simp
  have hmeas : Measurable (fun p : ℂˣ × M22 => chC n s p.1 * ((‖(p.1 : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹ *
      (((‖(Matrix.of p.2).det‖⁻¹ : ℝ) : ℂ) * W2 k (innQ Ψ' 1 p.2 (p.1 : ℂ)⁻¹) (Matrix.of p.2)⁻¹)) := by
    have hv : Measurable (fun p : ℂˣ × M22 => ((p.1 : ℂˣ) : ℂ)) :=
      GlobalTheory.CompanionTheory.TateC.val_measurableEmbedding.measurable.comp measurable_fst
    have hdet : Measurable (fun p : ℂˣ × M22 => (Matrix.of p.2).det) := by
      simp only [Matrix.det_fin_two, Matrix.of_apply]
      fun_prop
    refine (((measurable_chC' n s).comp measurable_fst).mul ?_).mul (Measurable.mul ?_ (GlobalTheory.T.measurable_whittaker_inner_quotient_inv k Ψ'))
    · exact (Complex.measurable_ofReal.comp (hv.norm.pow_const 2)).inv
    · exact Complex.measurable_ofReal.comp hdet.norm.inv
  have hnorm := fun (t : ℂˣ) (h : M22) => norm_integrand k Ψ' n s t h
  have hz : ∀ h : M22, (Matrix.of h).det = 0 → ∀ t : ℂˣ,
      chC n s t * ((‖(t : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹ *
      (((‖(Matrix.of h).det‖⁻¹ : ℝ) : ℂ) * W2 k (innQ Ψ' 1 h (t : ℂ)⁻¹) (Matrix.of h)⁻¹) = 0 := by
    intro h hd t
    simp [hd]
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun h => ?_, ?_⟩
  · by_cases hd : (Matrix.of h).det = 0
    · simp only [hz h hd]
      exact integrable_zero _ _ _
    · have hq : 0 < ‖eta h‖ := by
        rw [norm_eta h hd]
        exact div_pos (GlobalTheory.CompanionTheory.MajC.L_eta h hd).1 (norm_pos_iff.2 hd)
      refine Integrable.mono' (((hK _ hq).1).const_mul (E h)) ?_ ?_
      · exact (hmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun t => by
          have := hpt h t hd
          rw [← hnorm t h] at this
          exact this
  · refine Integrable.mono' (hGN.const_mul (A * |K|)) ?_ ?_
    · exact (hmeas.norm.stronglyMeasurable.integral_prod_left' (μ := mulC)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun h => ?_
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      by_cases hd : (Matrix.of h).det = 0
      · simp only [hz h hd, norm_zero, integral_zero]
        exact mul_nonneg (by positivity) (gx_nonneg _ _ _)
      · have hD : 0 < GlobalTheory.CompanionTheory.MajC.dt h := norm_pos_iff.2 hd
        have hq : 0 < ‖eta h‖ := by
          rw [norm_eta h hd]
          exact div_pos (GlobalTheory.CompanionTheory.MajC.L_eta h hd).1 hD
        obtain ⟨i1, i2⟩ := hK _ hq
        have hqp : 0 ≤ ‖eta h‖ ^ (2 * s.re - 2) := Real.rpow_nonneg hq.le _
        calc ∫ t : ℂˣ, ‖_‖ ∂mulC ≤ ∫ t : ℂˣ, E h *
              (‖(t : ℂ)‖ ^ (2 * s.re - 2) / (1 + ‖(t : ℂ)⁻¹‖ * ‖eta h‖) ^ Nb) ∂mulC := by
              refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
                (i1.const_mul _) (Filter.Eventually.of_forall fun t => ?_)
              have := hpt h t hd
              rw [← hnorm t h] at this
              exact this
          _ = E h * ∫ t : ℂˣ, ‖(t : ℂ)‖ ^ (2 * s.re - 2) / (1 + ‖(t : ℂ)⁻¹‖ * ‖eta h‖) ^ Nb ∂mulC :=
              integral_const_mul _ _
          _ ≤ E h * (K * ‖eta h‖ ^ (2 * s.re - 2)) := mul_le_mul_of_nonneg_left i2 (hE0 h)
          _ ≤ E h * (|K| * ‖eta h‖ ^ (2 * s.re - 2)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self _) hqp) (hE0 h)
          _ = _ := by
              simp only [hE, hX, gx]
              rw [norm_eta h hd]
              ring

end GlobalTheory.CompanionTheory.PerUC
