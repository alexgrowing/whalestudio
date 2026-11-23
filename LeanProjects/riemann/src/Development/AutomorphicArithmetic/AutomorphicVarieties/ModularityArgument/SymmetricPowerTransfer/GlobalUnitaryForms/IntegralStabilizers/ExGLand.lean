import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LandherrAndLandherrSt

open NumberField Matrix

namespace UpperTheory.V.Z.Sym.Glob

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private theorem ex_real (φ : F →+* ℂ) : ∃ σ : F →+* ℝ, ∀ x, φ x = (σ x : ℂ) := by
  have h := InfinitePlace.isReal_of_mk_isReal (IsTotallyReal.isReal (InfinitePlace.mk φ))
  exact ⟨h.embedding, fun x => (h.coe_embedding_apply x).symm⟩

theorem exG_nonsq {Δ : F} (hΔ : ∀ σ : F →+* ℝ, σ Δ < 0) : ∀ r : F, r ^ 2 ≠ Δ + 0 * r := by
  intro r hr
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  obtain ⟨σ, -⟩ := ex_real φ
  have h := hΔ σ
  have h2 := congrArg σ hr
  simp only [map_pow, zero_mul, add_zero] at h2
  nlinarith [sq_nonneg (σ r)]

theorem exG_ne {x : F} (h : TPos x) : x ≠ 0 := by
  intro hx
  obtain ⟨σ, -⟩ := ex_real (Classical.arbitrary (InfinitePlace F)).embedding
  have := h σ
  simp [hx] at this

private theorem emb_star {Δ : F} (hΔ : ∀ σ : F →+* ℝ, σ Δ < 0) (φ : Lsq F Δ →+* ℂ) :
    (∀ x, φ (star x) = starRingEnd ℂ (φ x)) ∧ (φ QuadraticAlgebra.omega).im ≠ 0 := by
  obtain ⟨σ, hσ⟩ := ex_real (φ.comp (algebraMap F (Lsq F Δ)))
  have hσ' : ∀ t : F, φ (algebraMap F _ t) = (σ t : ℂ) := hσ
  set w := φ QuadraticAlgebra.omega with hwdef
  have hw : w * w = (σ Δ : ℂ) := by
    rw [hwdef, ← map_mul, ← hσ']
    congr 1
    ext <;> simp
  have hre := congrArg Complex.re hw
  have him := congrArg Complex.im hw
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at hre him
  have hneg := hΔ σ
  have hwi : w.im ≠ 0 := by
    intro h0
    rw [h0] at hre
    nlinarith [sq_nonneg w.re]
  have hwr : w.re = 0 := by
    have : 2 * w.re * w.im = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hwi
  have hd : ∀ x : Lsq F Δ, φ x = (σ x.re : ℂ) + (σ x.im : ℂ) * w := by
    intro x
    conv_lhs => rw [show x = algebraMap F _ x.re + algebraMap F _ x.im * QuadraticAlgebra.omega by ext <;> simp]
    rw [map_add, map_mul, hσ', hσ']
  refine ⟨fun x => ?_, hwi⟩
  rw [hd, hd]
  apply Complex.ext <;> simp [hwr]

theorem exG_land {Δ : F} (hΔ : ∀ σ : F →+* ℝ, σ Δ < 0) (g : Fin 3 → F) (hg : ∀ i, TPos (g i)) (y : Lsq F Δ)
    (hy : algebraMap F (Lsq F Δ) (∏ i, g i) = y * star y) :
    ∃ P : Matrix (Fin 3) (Fin 3) (Lsq F Δ), IsUnit P.det ∧
      diagonal (fun i => algebraMap F (Lsq F Δ) (g i)) = Pᵀ * P.map star := by
  haveI : Fact (∀ r : F, r ^ 2 ≠ Δ + 0 * r) := ⟨exG_nonsq hΔ⟩
  haveI : Module.Finite ℚ (Lsq F Δ) := Module.Finite.trans F (Lsq F Δ)
  haveI : NumberField (Lsq F Δ) := ⟨⟩
  haveI : IsTotallyComplex (Lsq F Δ) := by
    refine ⟨fun w => ?_⟩
    rw [InfinitePlace.isComplex_iff]
    intro hr
    apply (emb_star hΔ w.embedding).2
    rw [← hr.coe_embedding_apply]
    exact Complex.ofReal_im _
  haveI : Algebra.IsQuadraticExtension F (Lsq F Δ) :=
    { finrank_eq_two' := QuadraticAlgebra.finrank_eq_two Δ 0 }
  haveI : IsCMField (Lsq F Δ) := IsCMField.ofCMExtension F (Lsq F Δ)
  have hcc : ∀ x : Lsq F Δ, ReciprocityTheory.ChartRestriction.G.FD.cc x = star x := by
    intro x
    obtain φ := (Classical.arbitrary (InfinitePlace (Lsq F Δ))).embedding
    apply φ.injective
    simp only [ReciprocityTheory.ChartRestriction.G.FD.cc, IsCMField.complexEmbedding_complexConj, (emb_star hΔ φ).1]
  have hstar : ∀ t : F, star (algebraMap F (Lsq F Δ) t) = algebraMap F (Lsq F Δ) t := by
    intro t
    ext <;> simp
  set G' : Matrix (Fin 3) (Fin 3) (Lsq F Δ) := diagonal (fun i => algebraMap F (Lsq F Δ) (g i)) with hG'
  have hdet : G'.det = algebraMap F (Lsq F Δ) (∏ i, g i) := by
    rw [hG', det_diagonal, map_prod]
  have hprod : (∏ i, g i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => exG_ne (hg i))
  obtain ⟨P, hP, hPe⟩ := GlobalTheory.QNorm.landherr_and_landherrSt.1 (Lsq F Δ) 3 1 G'
    (by
      intro a b
      rw [hcc]
      by_cases h : a = b
      · subst h
        simp
      · simp [Matrix.one_apply, h, Ne.symm h])
    (by
      intro a b
      rw [hcc]
      by_cases h : a = b
      · subst h
        simp [hG', hstar]
      · simp [hG', Matrix.diagonal_apply, h, Ne.symm h])
    (by simp)
    (by
      rw [hdet]
      exact (map_ne_zero_iff _ (algebraMap F (Lsq F Δ)).injective).mpr hprod)
    (by
      intro τ
      obtain ⟨σ, hσ⟩ := ex_real (τ.comp (algebraMap F (Lsq F Δ)))
      have hσ' : ∀ t : F, τ (algebraMap F _ t) = (σ t : ℂ) := hσ
      refine ⟨diagonal (fun i => ((Real.sqrt (σ (g i)) : ℝ) : ℂ)), ?_, ?_⟩
      · rw [det_diagonal]
        refine Finset.prod_ne_zero_iff.mpr (fun i _ => ?_)
        rw [Complex.ofReal_ne_zero]
        exact (Real.sqrt_pos.mpr (hg i σ)).ne'
      · ext a b
        by_cases h : a = b
        · subst h
          simp only [hG', Matrix.map_apply, Matrix.diagonal_apply_eq, Matrix.mul_apply, Matrix.transpose_apply,
            Matrix.diagonal_apply, Matrix.one_apply]
          simp [hσ']
          rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hg a σ).le]
        · simp [hG', Matrix.diagonal_apply, h, Ne.symm h, Matrix.mul_apply, Matrix.one_apply])
    (by
      refine ⟨y⁻¹, ?_⟩
      rw [hcc, det_one, hdet, hy, star_inv₀, one_div, mul_inv])
  have hm : P.map ReciprocityTheory.ChartRestriction.G.FD.cc = P.map star := Matrix.ext fun a b => hcc (P a b)
  refine ⟨P, isUnit_iff_ne_zero.mpr hP, ?_⟩
  rw [hPe, Matrix.mul_one, hm]

end UpperTheory.V.Z.Sym.Glob
