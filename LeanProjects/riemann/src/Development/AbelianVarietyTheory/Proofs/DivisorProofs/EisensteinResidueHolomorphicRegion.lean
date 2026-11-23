import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EisRes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def lineStab (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) :
    Subgroup (ratPts σ J) where
  carrier := {γ | ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J γ.1).1 * adMat F x = l.1 • adMat F x}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro γ δ ⟨l₁, h₁⟩ ⟨l₂, h₂⟩
    refine ⟨l₁ * l₂, ?_⟩
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul]
    rw [Matrix.mul_assoc, h₂, Matrix.mul_smul, h₁, smul_smul, mul_comm]
  inv_mem' := by
    rintro γ ⟨l, hl⟩
    refine ⟨l⁻¹, ?_⟩
    have e : (matHom _ σ J (γ.1)⁻¹).1 * (matHom _ σ J γ.1).1 = 1 := by
      rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    have := congrArg (fun M => (matHom _ σ J (γ.1)⁻¹).1 * M) hl
    simp only [← Matrix.mul_assoc, e, Matrix.one_mul, Matrix.mul_smul] at this
    simp only [Subgroup.coe_inv]
    have h2 : (↑l⁻¹ : AF F ⊗[F] E) • adMat F x = (↑l⁻¹ : AF F ⊗[F] E) • (↑l • ((matHom _ σ J (γ.1)⁻¹).1 * adMat F x)) :=
      congrArg _ this
    rw [h2, ← Units.smul_def, inv_smul_smul]

theorem exists_reps (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) :
    ∃ T : Set (ratPts σ J), ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ l : (AF F ⊗[F] E)ˣ,
      (matHom _ σ J (γ * t⁻¹ : ratPts σ J).1).1 * adMat F x = l.1 • adMat F x := by
  let R := QuotientGroup.rightRel (lineStab σ J x)
  refine ⟨Set.range (fun q : Quotient R => q.out), fun γ => ⟨(Quotient.mk R γ).out, ⟨⟨_, rfl⟩, ?_⟩, ?_⟩⟩
  · have := Quotient.mk_out (s := R) γ
    exact (QuotientGroup.rightRel_apply.1 this)
  · rintro t ⟨⟨q, rfl⟩, ht⟩
    have h1 : R q.out γ := QuotientGroup.rightRel_apply.2 ht
    have h2 : Quotient.mk R q.out = Quotient.mk R γ := Quotient.sound h1
    rw [Quotient.out_eq] at h2
    rw [h2]

end GlobalTheory.EisRes

namespace GlobalTheory.EisRes

theorem levelAll_inv_near_rho : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) (Eis : ℂ → GAd σ J → ℂ) (c : ℂ → ℂ),
    HidaSetting σ J X Y L a h → EisensteinHyp σ J (col0 X) (col0 Y) h Eis c →
    ∀ (k₀ : ℕ) (U₀ : Set ℂ) (H₀ : ℂ → GAd σ J → ℂ), U₀ ∈ 𝓝 (((n : ℂ) - 1) / 2) →
      (∀ s ∈ U₀, s ≠ (((n : ℂ) - 1) / 2) → ∀ g, H₀ s g = (s - (((n : ℂ) - 1) / 2)) ^ k₀ * Eis s g) →
      (∀ s ∈ U₀, IsSmoothModerate σ J (H₀ s)) →
      (∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) U₀) →
      ∃ V ∈ 𝓝 (((n : ℂ) - 1) / 2), ∀ s ∈ V, ∀ k ∈ levelAll σ J L a, ∀ g, H₀ s (g * k) = H₀ s g := by
  intro F E _ _ _ _ _ σ n J r X Y L a h Eis c hS hP k₀ U₀ H₀ hU₀ hH hsm hhol
  set ρ : ℂ := ((n : ℂ) - 1) / 2 with hρ
  have hρre : ρ.re = ((n : ℝ) - 1) / 2 := by simp [hρ]
  have hI : IsIwaHtG σ J (col0 X) L a h := hS.2.2.2.2.2.2

  have hinv : ∀ g, ∀ k ∈ levelAll σ J L a, h (g * k) = h g := by
    intro g k hk
    obtain ⟨p, l, hpl, k', hk', rfl⟩ := hI.1 g
    rw [mul_assoc, hI.2 p l hpl _ (Subgroup.mul_mem _ hk' hk), hI.2 p l hpl k' hk']
  obtain ⟨T, hT⟩ := exists_reps σ J (col0 X)

  have Heisenberg₂ : ∀ s : ℂ, ρ.re < s.re → ∀ g, ∀ k ∈ levelAll σ J L a, Eis s (g * k) = Eis s g := by
    intro s hs g k hk
    rw [hρre] at hs
    have h1 := hP.1 T hT s hs (g * k)
    have h2 := hP.1 T hT s hs g
    simp only [← mul_assoc, hinv _ k hk] at h1
    exact h1.unique h2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU₀
  refine ⟨Metric.ball ρ ε, Metric.ball_mem_nhds ρ hε, fun s hs k hk g => ?_⟩
  have hd : ∀ g', DifferentiableOn ℂ (fun s => H₀ s g') (Metric.ball ρ ε) := fun g' =>
    (hhol _ (GlobalTheory.EisLine.isModerateForm_proj σ J g')).mono hball
  have a1 := (hd (g * k)).analyticOnNhd Metric.isOpen_ball
  have a2 := (hd g).analyticOnNhd Metric.isOpen_ball
  set z₀ : ℂ := ρ + ((ε / 2 : ℝ) : ℂ) with hz₀
  have hz₀b : z₀ ∈ Metric.ball ρ ε := by
    rw [Metric.mem_ball, hz₀, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
    linarith
  have hz₀re : ρ.re < z₀.re := by simp [hz₀, hε]
  have hopen : IsOpen (Metric.ball ρ ε ∩ {s : ℂ | ρ.re < s.re}) :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hev : (fun s => H₀ s (g * k)) =ᶠ[𝓝 z₀] fun s => H₀ s g := by
    filter_upwards [hopen.mem_nhds ⟨hz₀b, hz₀re⟩] with s hs'
    have hsU : s ∈ U₀ := hball hs'.1
    have hne : s ≠ ρ := by rintro rfl; exact lt_irrefl ρ.re hs'.2
    rw [hH s hsU hne, hH s hsU hne, Heisenberg₂ s hs'.2 g k hk]
  exact a1.eqOn_of_preconnected_of_eventuallyEq a2 (convex_ball ρ ε).isPreconnected hz₀b hev hs

end GlobalTheory.EisRes

end
