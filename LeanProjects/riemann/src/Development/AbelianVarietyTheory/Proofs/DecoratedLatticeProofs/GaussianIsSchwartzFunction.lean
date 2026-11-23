import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyMulGaussianBounded
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.GaussSchwartz

open scoped Nat

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_id_le_one_add (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (id : E → E) x‖ ≤ 1 + ‖x‖ := by
  rcases j with _ | n
  · rw [norm_iteratedFDeriv_zero]; simp
  · rw [← norm_iteratedFDeriv_fderiv,
      show fderiv ℝ (id : E → E) = fun _ => ContinuousLinearMap.id ℝ E from funext fun _ => fderiv_id]
    rcases n with _ | n
    · rw [norm_iteratedFDeriv_zero]
      exact (ContinuousLinearMap.norm_id_le).trans (by linarith [norm_nonneg x])
    · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]
      simp only [Pi.zero_apply, norm_zero]
      positivity

theorem norm_iteratedFDeriv_diag_le (B : E →L[ℝ] E →L[ℝ] ℝ) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => B y y) x‖ ≤ ‖B‖ * (2 ^ n * (1 + ‖x‖) ^ 2) := by
  have h := B.norm_iteratedFDeriv_le_of_bilinear (f := id) (g := id) (N := (n : WithTop ℕ∞))
    contDiff_id contDiff_id x le_rfl
  simp only [id] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : E => y) x‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun y : E => y) x‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (1 + ‖x‖) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [mul_assoc, sq]
        gcongr
        · exact norm_iteratedFDeriv_id_le_one_add i x
        · exact norm_iteratedFDeriv_id_le_one_add (n - i) x
    _ = 2 ^ n * (1 + ‖x‖) ^ 2 := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose n

theorem norm_iteratedFDeriv_rexp (i : ℕ) (y : ℝ) : ‖iteratedFDeriv ℝ i Real.exp y‖ = Real.exp y := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have h := congrFun (iteratedDeriv_exp_const_mul i 1) y
  simp only [one_mul, one_pow] at h
  rw [show (fun s => Real.exp s) = Real.exp from rfl] at h
  rw [h, Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]

theorem exists_bound_poly_mul_exp (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ C, ∀ r : ℝ, 0 ≤ r → (1 + r) ^ N * Real.exp (-(c * r ^ 2)) ≤ C := by
  first
  | exact @_root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded
  | exact _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded
  | (apply _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded <;> assumption)
  | (intros; apply _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PolynomialGaussianBounded.poly_mul_gaussian_bounded ..)

theorem exists_coercive [FiniteDimensional ℝ E] (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ x, x ≠ 0 → B x x < 0) :
    ∃ c > 0, ∀ x, B x x ≤ -(c * ‖x‖ ^ 2) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · refine ⟨1, one_pos, fun x => ?_⟩
    rw [Subsingleton.elim x 0]; simp
  · have hcont : Continuous fun y : E => B y y := (B.continuous.clm_apply continuous_id)
    obtain ⟨x0, hx0, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn
      (NormedSpace.sphere_nonempty.2 zero_le_one) hcont.continuousOn
    have hx0n : ‖x0‖ = 1 := by simpa using hx0
    have hx0ne : x0 ≠ 0 := by intro h; rw [h, norm_zero] at hx0n; exact zero_ne_one hx0n
    refine ⟨-(B x0 x0), by linarith [hB x0 hx0ne], fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp
    · have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
      set u : E := ‖x‖⁻¹ • x with hu
      have hun : u ∈ Metric.sphere (0 : E) 1 := by
        rw [mem_sphere_zero_iff_norm, hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxn.ne']
      have hxu : x = ‖x‖ • u := by rw [hu, smul_smul, mul_inv_cancel₀ hxn.ne', one_smul]
      have h1 : B u u ≤ B x0 x0 := hmax hun
      have h2 : B x x = ‖x‖ ^ 2 * B u u := by
        conv_lhs => rw [hxu]
        simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
      rw [h2]
      nlinarith [sq_nonneg ‖x‖]

theorem exists_schwartz_exp_diag [FiniteDimensional ℝ E] (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ x, x ≠ 0 → B x x < 0) :
    ∃ f : SchwartzMap E ℂ, ∀ x, f x = ((Real.exp (B x x) : ℝ) : ℂ) := by
  obtain ⟨c, hc, hBc⟩ := exists_coercive B hB
  have hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : E => B y y) := B.contDiff.clm_apply contDiff_id
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Real.exp ∘ fun y : E => B y y) := Real.contDiff_exp.comp hq
  refine ⟨⟨Complex.ofRealLI ∘ (Real.exp ∘ fun y : E => B y y),
    Complex.ofRealLI.toContinuousLinearMap.contDiff.comp hg, ?_⟩, fun x => rfl⟩
  intro k n
  obtain ⟨C, hC⟩ := exists_bound_poly_mul_exp c hc (k + 2 * n)
  refine ⟨n ! * (2 * (‖B‖ + 1)) ^ n * C, fun x => ?_⟩
  have hn : ((n : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  rw [LinearIsometry.norm_iteratedFDeriv_comp_left _ hg.contDiffAt hn]
  have hfb := norm_iteratedFDeriv_comp_le (g := Real.exp) (f := fun y : E => B y y)
    Real.contDiff_exp hq hn x (C := Real.exp (B x x)) (D := 2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2)
    (fun i _ => (norm_iteratedFDeriv_rexp i _).le) (fun i hi _ => by
      have hB0 := norm_nonneg B
      have hx0 := norm_nonneg x
      have a1 : ‖B‖ ≤ (‖B‖ + 1) ^ i :=
        le_trans (by linarith) (le_self_pow₀ (by linarith) (by omega))
      have a2 : (1 + ‖x‖) ^ 2 ≤ ((1 + ‖x‖) ^ 2) ^ i :=
        le_self_pow₀ (by nlinarith) (by omega)
      calc ‖iteratedFDeriv ℝ i (fun y : E => B y y) x‖ ≤ ‖B‖ * (2 ^ i * (1 + ‖x‖) ^ 2) :=
            norm_iteratedFDeriv_diag_le B i x
        _ = 2 ^ i * ‖B‖ * (1 + ‖x‖) ^ 2 := by ring
        _ ≤ 2 ^ i * (‖B‖ + 1) ^ i * ((1 + ‖x‖) ^ 2) ^ i := by gcongr
        _ = (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ i := by rw [mul_pow, mul_pow])
  have hx0 := norm_nonneg x
  have hB0 := norm_nonneg B
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (Real.exp ∘ fun y : E => B y y) x‖
      ≤ (1 + ‖x‖) ^ k * (n ! * Real.exp (-(c * ‖x‖ ^ 2)) * (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ n) := by
        gcongr
        · linarith
        · exact hfb.trans (by gcongr; exact hBc x)
    _ = n ! * (2 * (‖B‖ + 1)) ^ n * ((1 + ‖x‖) ^ (k + 2 * n) * Real.exp (-(c * ‖x‖ ^ 2))) := by
        rw [show (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ n = (2 * (‖B‖ + 1)) ^ n * (1 + ‖x‖) ^ (2 * n) by
          rw [mul_pow, pow_mul], pow_add]; ring
    _ ≤ n ! * (2 * (‖B‖ + 1)) ^ n * C := by gcongr; exact hC ‖x‖ hx0

end GlobalTheory.GaussSchwartz

namespace GlobalTheory.GaussSchwartz

open scoped ComplexOrder

section TraceForm

variable {ι : Type} [Fintype ι] {m n : ℕ}

def trForm (w : ι → ℝ) (M : ι → Matrix (Fin m) (Fin m) ℂ) (x y : ι → Fin m → Fin n → ℂ) : ℝ :=
  -(2 * Real.pi) * ∑ i, w i * (Matrix.trace ((Matrix.of (x i))ᴴ * M i * Matrix.of (y i))).re

def trFormL (w : ι → ℝ) (M : ι → Matrix (Fin m) (Fin m) ℂ) :
    (ι → Fin m → Fin n → ℂ) →ₗ[ℝ] (ι → Fin m → Fin n → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (trForm w M)
    (fun x x' y => by
      simp only [trForm, Pi.add_apply, ← Matrix.of_add_of, Matrix.conjTranspose_add, Matrix.add_mul,
        Matrix.trace_add, Complex.add_re, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [trForm, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : Matrix.of (c • x i) = c • Matrix.of (x i) := rfl
      rw [this, Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul,
        Complex.smul_re, smul_eq_mul]
      ring)
    (fun x y y' => by
      simp only [trForm, Pi.add_apply, ← Matrix.of_add_of, Matrix.mul_add,
        Matrix.trace_add, Complex.add_re, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [trForm, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : Matrix.of (c • y i) = c • Matrix.of (y i) := rfl
      rw [this, Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
      ring)

def trFormC (w : ι → ℝ) (M : ι → Matrix (Fin m) (Fin m) ℂ) :
    (ι → Fin m → Fin n → ℂ) →L[ℝ] (ι → Fin m → Fin n → ℂ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((ι → Fin m → Fin n → ℂ) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ trFormL w M)

theorem trFormC_apply (w : ι → ℝ) (M : ι → Matrix (Fin m) (Fin m) ℂ) (x y : ι → Fin m → Fin n → ℂ) :
    trFormC w M x y = trForm w M x y := rfl

theorem trace_conjTranspose_mul_mul (M : Matrix (Fin m) (Fin m) ℂ) (Z : Matrix (Fin m) (Fin n) ℂ) :
    Matrix.trace (Zᴴ * M * Z) = ∑ j, star (fun a => Z a j) ⬝ᵥ (M *ᵥ fun a => Z a j) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct,
    Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem re_trace_nonneg {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.PosDef) (Z : Matrix (Fin m) (Fin n) ℂ) :
    0 ≤ (Matrix.trace (Zᴴ * M * Z)).re := by
  rw [trace_conjTranspose_mul_mul, Complex.re_sum]
  exact Finset.sum_nonneg fun j _ => by
    simpa using (Complex.le_def.1 (hM.posSemidef.dotProduct_mulVec_nonneg (fun a => Z a j))).1

theorem re_trace_pos {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.PosDef) {Z : Matrix (Fin m) (Fin n) ℂ} (hZ : Z ≠ 0) :
    0 < (Matrix.trace (Zᴴ * M * Z)).re := by
  obtain ⟨j, hj⟩ : ∃ j, (fun a => Z a j) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hZ
    ext a j
    exact congrFun (h j) a
  rw [trace_conjTranspose_mul_mul, Complex.re_sum]
  refine Finset.sum_pos' (fun j _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩
  · simpa using (Complex.le_def.1 (hM.posSemidef.dotProduct_mulVec_nonneg (fun a => Z a j))).1
  · simpa using (Complex.lt_def.1 (hM.dotProduct_mulVec_pos hj)).1

theorem trForm_self_neg (w : ι → ℝ) (hw : ∀ i, 0 < w i) (M : ι → Matrix (Fin m) (Fin m) ℂ)
    (hM : ∀ i, (M i).PosDef) (x : ι → Fin m → Fin n → ℂ) (hx : x ≠ 0) : trForm w M x x < 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  have hpos : 0 < ∑ i, w i * (Matrix.trace ((Matrix.of (x i))ᴴ * M i * Matrix.of (x i))).re := by
    refine Finset.sum_pos' (fun k _ => mul_nonneg (hw k).le (re_trace_nonneg (hM k) _))
      ⟨i, Finset.mem_univ _, mul_pos (hw i) (re_trace_pos (hM i) ?_)⟩
    intro h
    exact hi h
  unfold trForm
  have := Real.pi_pos
  nlinarith

theorem trace_conjTranspose_mul_mul_real {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.IsHermitian)
    (Z : Matrix (Fin m) (Fin n) ℂ) :
    (((Matrix.trace (Zᴴ * M * Z)).re : ℝ) : ℂ) = Matrix.trace (Zᴴ * M * Z) := by
  apply Complex.conj_eq_iff_re.mp
  change star (Matrix.trace _) = _
  rw [← Matrix.trace_conjTranspose]
  congr 1
  simp [Matrix.conjTranspose_mul, hM.eq, Matrix.mul_assoc]

end TraceForm

theorem exists_schwartz_gauss : ∀ (D : D7) (n : ℕ) (V : HSp D) (l : D.what₂.Tau → ℝ), (∀ τ, l τ ≠ 0) →
    ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) →
    ∃ f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ, ∀ z, f z = gauss V l s (fun τ => Matrix.of (z τ)) := by
  intro D n V l hl s hs
  have hM : ∀ τ, (gramAt D V τ * s τ).PosDef := fun τ => (hs τ).2.2
  obtain ⟨f, hf⟩ := exists_schwartz_exp_diag (trFormC (n := n) (fun τ => |l τ|) (fun τ => gramAt D V τ * s τ))
    (fun x hx => by
      rw [trFormC_apply]
      exact trForm_self_neg _ (fun τ => abs_pos.2 (hl τ)) _ hM x hx)
  refine ⟨f, fun z => ?_⟩
  rw [hf, trFormC_apply, Complex.ofReal_exp, gauss]
  congr 1
  simp only [trForm]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [trace_conjTranspose_mul_mul_real (hM τ).1]

end GlobalTheory.GaussSchwartz

end
