import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.NormAddSmulSq

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exp_alg (s t N a U : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * s * t * N - 4 * Real.pi * Complex.I * t * (a + s * N) +
      ((-(2 * Real.pi * (U + 2 * s * a + s ^ 2 * N)) : ℝ) : ℂ)) =
      ((Real.exp (-(1 / (16 * Real.pi) * (s ^ 2 + t ^ 2) * (16 * Real.pi ^ 2 * N))) : ℝ) : ℂ) *
        (Complex.exp (-((s + t * Complex.I) ^ 2 * ((16 * Real.pi ^ 2 * N : ℝ) : ℂ) / (16 * Real.pi))) *
          ((Real.exp (-(2 * Real.pi * U)) : ℝ) : ℂ) * Complex.exp ((s + t * Complex.I) * ((-(4 * Real.pi) * a : ℝ) : ℂ))) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  linear_combination ((t : ℂ) ^ 2 * N) * Complex.I_sq

variable {d : SD σ}

theorem B_vline (hT : TAll) (hU : TUnit) (hH : THeis) (hA : AuxiliaryPrimeFunction) (hF : FockMem) (R : RD d) :
    ∃ (C : ℂ) (c s : ℝ) (ν : Measure (Mx F E d.m d.n)) (νf : Measure (Yf d)), C ≠ 0 ∧ s ≠ 0 ∧
      ν.IsAddHaarMeasure ∧ νf.IsAddHaarMeasure ∧
      ∀ g ∈ SB (Yf d), ∀ Ω ∈ d.sch, d.T Ω = vac R g → ∀ Φ ∈ d.sch, ∀ W : Mx F E d.m d.n, finOne F • W = 0 → ∀ z : ℂ,
        B ν Φ (d.dd.rho d.B.ψ (vline R W z) Ω) = C * Real.exp (-(c * ‖z‖ ^ 2 * ‖s • arc R W‖ ^ 2)) *
          (Complex.exp (-(z ^ 2 * ‖s • arc R W‖ ^ 2 / (16 * Real.pi))) *
            ∫ u, hg R νf (d.T Φ) g u * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2)) *
              Complex.exp (z * ⟪s • arc R W, u⟫_ℝ)) := by
  obtain ⟨νf, hνf, hν⟩ := exists_nuf R
  refine ⟨1, 1 / (16 * Real.pi), -(4 * Real.pi), Measure.map (jnp R) ((volume : Measure (Vw d)).prod νf), νf,
    one_ne_zero, neg_ne_zero.2 (by positivity), hν, hνf, ?_⟩
  intro g hg' Ω hΩ hTΩ Φ hΦ W hW z
  set w := arc R W with hw
  let e : Vw d → ℂ := ev w z
  let b : Vw d → ℂ := bv w z
  have hTv : ∀ X, d.T (d.dd.rho d.B.ψ (vline R W z) Ω) X = b (arc R X) * g (fin d X) :=
    T_vline hH R hΩ hTΩ hW z
  have hb : Continuous b := continuous_bv w z
  have hb1 : ∀ u, ‖b u‖ ≤ 1 := norm_bv_le w z
  have hTΦ : d.T Φ ∈ d.schM := (hT.1 F E σ d).1 Φ hΦ
  have e1 : B (Measure.map (jnp R) ((volume : Measure (Vw d)).prod νf)) Φ (d.dd.rho d.B.ψ (vline R W z) Ω) =
      ∫ u, star (b u) * hg R νf (d.T Φ) g u := by
    simp only [B, hTv]
    exact integral_jnp R hνf hTΦ hg' hb hb1
  rw [e1]
  have key : ∀ u, star (b u) * hg R νf (d.T Φ) g u =
      ((Real.exp (-(1 / (16 * Real.pi) * ‖z‖ ^ 2 * ‖(-(4 * Real.pi)) • w‖ ^ 2)) : ℝ) : ℂ) *
        Complex.exp (-(z ^ 2 * (‖(-(4 * Real.pi)) • w‖ ^ 2 : ℝ) / (16 * Real.pi))) *
          (hg R νf (d.T Φ) g u * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2)) *
            Complex.exp (z * ⟪(-(4 * Real.pi)) • w, u⟫_ℝ)) := by
    intro u
    have hz : z = z.re + z.im * Complex.I := (Complex.re_add_im z).symm
    have h1 := exp_alg z.re z.im (‖w‖ ^ 2) ⟪w, u⟫_ℝ (‖u‖ ^ 2)
    rw [← hz] at h1
    have hn : ‖(-(4 * Real.pi)) • w‖ ^ 2 = 16 * Real.pi ^ 2 * ‖w‖ ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
    have hi : ⟪(-(4 * Real.pi)) • w, u⟫_ℝ = -(4 * Real.pi) * ⟪w, u⟫_ℝ := real_inner_smul_left _ _ _
    have hzn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
    simp only [b, bv, star_star, hn, hi, hzn]
    have h2 : ev w z u = 2 * Real.pi * Complex.I * z.re * z.im * ((‖w‖ ^ 2 : ℝ) : ℂ) -
        4 * Real.pi * Complex.I * z.im * (⟪w, u⟫_ℝ + z.re * ((‖w‖ ^ 2 : ℝ) : ℂ)) +
        ((-(2 * Real.pi * (‖u‖ ^ 2 + 2 * z.re * ⟪w, u⟫_ℝ + z.re ^ 2 * ‖w‖ ^ 2)) : ℝ) : ℂ) := by
      rfl
    rw [h2, h1]
    ring
  simp_rw [key]
  rw [integral_const_mul]
  simp only [one_mul, Complex.ofReal_exp]
  push_cast
  ring

end PositivityTheory.SiegelWeilFormula.KFP

end
