import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsCompactZetaLe

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate InnerProductSpace ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section HS

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hs_add_left (A A' C : Wq →L[ℂ] Wp) : B.hsInner (A + A') C = B.hsInner A C + B.hsInner A' C := by
  have h : B.hsVec (A + A') = B.hsVec A + B.hsVec A' := by
    unfold B.hsVec; ext i; simp
  unfold B.hsInner
  rw [h, inner_add_right]

theorem hs_add_right (A C C' : Wq →L[ℂ] Wp) : B.hsInner A (C + C') = B.hsInner A C + B.hsInner A C' := by
  have h : B.hsVec (C + C') = B.hsVec C + B.hsVec C' := by
    unfold B.hsVec; ext i; simp
  unfold B.hsInner
  rw [h, inner_add_left]

theorem hs_smul_left (a : ℂ) (A C : Wq →L[ℂ] Wp) : B.hsInner (a • A) C = a * B.hsInner A C := by
  have h : B.hsVec (a • A) = a • B.hsVec A := by
    unfold B.hsVec; ext i; simp
  unfold B.hsInner
  rw [h, inner_smul_right]

theorem hs_smul_right (a : ℂ) (A C : Wq →L[ℂ] Wp) : B.hsInner A (a • C) = conj a * B.hsInner A C := by
  have h : B.hsVec (a • C) = a • B.hsVec C := by
    unfold B.hsVec; ext i; simp
  unfold B.hsInner
  rw [h, inner_smul_left]

end HS

section Lim

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem tendsto_int_uv (I J : α → ℂ) (hI : Integrable I μ) (hJ : Integrable J μ) (u v : ℕ → α → ℂ) (M : ℝ)
    (hum : ∀ n, AEStronglyMeasurable (u n) μ) (hvm : ∀ n, AEStronglyMeasurable (v n) μ)
    (hu : ∀ n x, ‖u n x‖ ≤ 1) (hv : ∀ n x, ‖v n x‖ ≤ M) (hl : ∀ x, ∀ᶠ n in atTop, u n x = 1 ∧ v n x = 0) :
    Tendsto (fun n => ∫ x, (u n x * I x + v n x * J x) ∂μ) atTop (𝓝 (∫ x, I x ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => ‖I x‖ + M * ‖J x‖) ?_ ?_ ?_ ?_
  · intro n
    exact ((hum n).mul hI.aestronglyMeasurable).add ((hvm n).mul hJ.aestronglyMeasurable)
  · exact hI.norm.add (hJ.norm.const_mul M)
  · intro n
    refine ae_of_all _ fun x => ?_
    calc ‖u n x * I x + v n x * J x‖ ≤ ‖u n x * I x‖ + ‖v n x * J x‖ := norm_add_le _ _
      _ = ‖u n x‖ * ‖I x‖ + ‖v n x‖ * ‖J x‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 * ‖I x‖ + M * ‖J x‖ :=
        add_le_add (mul_le_mul_of_nonneg_right (hu n x) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hv n x) (norm_nonneg _))
      _ = ‖I x‖ + M * ‖J x‖ := by ring
  · refine ae_of_all _ fun x => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hl x] with n hn
    rw [hn.1, hn.2]
    ring

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem pair_lim (φ ψ aφ bφ a'ψ b'ψ : α → (Wq →L[ℂ] Wp)) (F D D' : ℕ → α → ℂ) (M : ℝ)
    (hFm : ∀ n, AEStronglyMeasurable (F n) μ) (hDm : ∀ n, AEStronglyMeasurable (D n) μ)
    (hD'm : ∀ n, AEStronglyMeasurable (D' n) μ)
    (hF : ∀ n x, ‖F n x‖ ≤ 1) (hD : ∀ n x, ‖D n x‖ ≤ M) (hD' : ∀ n x, ‖D' n x‖ ≤ M)
    (hl : ∀ x, ∀ᶠ n in atTop, F n x = 1 ∧ D n x = 0 ∧ D' n x = 0)
    (h1 : Integrable (fun x => B.hsInner (aφ x) (ψ x)) μ) (h2 : Integrable (fun x => B.hsInner (φ x) (a'ψ x)) μ)
    (h3 : Integrable (fun x => B.hsInner (bφ x) (ψ x)) μ) (h4 : Integrable (fun x => B.hsInner (φ x) (b'ψ x)) μ)
    (heq : ∀ n, ∫ x, B.hsInner (F n x • aφ x + D n x • bφ x) (F n x • ψ x) ∂μ =
      ∫ x, B.hsInner (F n x • φ x) (F n x • a'ψ x + D' n x • b'ψ x) ∂μ) :
    ∫ x, B.hsInner (aφ x) (ψ x) ∂μ = ∫ x, B.hsInner (φ x) (a'ψ x) ∂μ := by
  have hcF : ∀ n, AEStronglyMeasurable (fun x => conj (F n x)) μ := fun n =>
    Complex.continuous_conj.comp_aestronglyMeasurable (hFm n)
  have hcD' : ∀ n, AEStronglyMeasurable (fun x => conj (D' n x)) μ := fun n =>
    Complex.continuous_conj.comp_aestronglyMeasurable (hD'm n)
  have hL : Tendsto (fun n => ∫ x, B.hsInner (F n x • aφ x + D n x • bφ x) (F n x • ψ x) ∂μ) atTop
      (𝓝 (∫ x, B.hsInner (aφ x) (ψ x) ∂μ)) := by
    refine (tendsto_int_uv (fun x => B.hsInner (aφ x) (ψ x)) (fun x => B.hsInner (bφ x) (ψ x)) h1 h3
      (fun n x => F n x * conj (F n x)) (fun n x => D n x * conj (F n x)) M
      (fun n => (hFm n).mul (hcF n)) (fun n => (hDm n).mul (hcF n)) ?_ ?_ ?_).congr fun n => ?_
    · intro n x
      rw [norm_mul, Complex.norm_conj]
      nlinarith [hF n x, norm_nonneg (F n x)]
    · intro n x
      rw [norm_mul, Complex.norm_conj]
      nlinarith [hF n x, hD n x, norm_nonneg (F n x), norm_nonneg (D n x)]
    · intro x
      filter_upwards [hl x] with n hn
      rw [hn.1, hn.2.1]
      simp
    · congr 1
      funext x
      simp only [hs_smul_right, hs_add_left, hs_smul_left]
      ring
  have hR : Tendsto (fun n => ∫ x, B.hsInner (F n x • φ x) (F n x • a'ψ x + D' n x • b'ψ x) ∂μ) atTop
      (𝓝 (∫ x, B.hsInner (φ x) (a'ψ x) ∂μ)) := by
    refine (tendsto_int_uv (fun x => B.hsInner (φ x) (a'ψ x)) (fun x => B.hsInner (φ x) (b'ψ x)) h2 h4
      (fun n x => F n x * conj (F n x)) (fun n x => F n x * conj (D' n x)) M
      (fun n => (hFm n).mul (hcF n)) (fun n => (hFm n).mul (hcD' n)) ?_ ?_ ?_).congr fun n => ?_
    · intro n x
      rw [norm_mul, Complex.norm_conj]
      nlinarith [hF n x, norm_nonneg (F n x)]
    · intro n x
      rw [norm_mul, Complex.norm_conj]
      nlinarith [hF n x, hD' n x, norm_nonneg (F n x), norm_nonneg (D' n x)]
    · intro x
      filter_upwards [hl x] with n hn
      rw [hn.1, hn.2.2]
      simp
    · congr 1
      funext x
      simp only [hs_add_right, hs_smul_right, hs_smul_left]
      ring
  exact tendsto_nhds_unique (hL.congr heq) hR

end Lim

end Formalism.FourierDecayAlt.P5.HerB
