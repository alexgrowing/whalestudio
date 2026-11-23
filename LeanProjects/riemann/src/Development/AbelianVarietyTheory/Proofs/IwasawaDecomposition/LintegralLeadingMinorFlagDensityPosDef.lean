import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorFlagDensityGlueLowerUnitriangularStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingGlueLowerUnitriangularBlocksStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HuaIntegralPositiveDefiniteQuadricStatement
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre.FlagInt

theorem isEmpty_low_one : IsEmpty (Low 1) :=
  ⟨fun s => by have h := s.2; rw [Subsingleton.elim s.1.1 s.1.2] at h; exact lt_irrefl _ h⟩

theorem isEmpty_low_zero : IsEmpty (Low 0) := ⟨fun s => s.1.1.elim0⟩

theorem volume_univ_of_isEmpty {ι : Type} [Fintype ι] [IsEmpty ι] : (volume : Measure (ι → ℂ)) Set.univ = 1 := by
  rw [volume_pi, Measure.pi_univ]; simp

theorem dens_one (A : Matrix (Fin 1) (Fin 1) ℂ) (y : Low 1 → ℂ) : dens A y = 1 := by
  simp only [dens, lminor, Fin.prod_univ_one]
  have : IsEmpty (Fin ((0 : Fin 1).castSucc : ℕ)) := ⟨fun x => x.elim0⟩
  rw [det_isEmpty]; simp

theorem re_facts {n : Type} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (h : H.PosDef) :
    0 < H.det.re ∧ H.det = (H.det.re : ℂ) := by
  have := Complex.pos_iff.1 h.det_pos
  exact ⟨this.1, Complex.ext (by simp) (by simp [← this.2])⟩

theorem lintegral_dens : ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ), A.PosDef →
    ∫⁻ y : Low m → ℂ, ENNReal.ofReal (dens A y) = ENNReal.ofReal (A.det.re ^ (1 - (m : ℤ)) / flagConst m) := by
  intro m
  induction m with
  | zero =>
    intro A _
    have := isEmpty_low_zero
    simp [dens, flagConst, volume_univ_of_isEmpty]
  | succ p ih =>
    intro A hA
    have := isEmpty_low_one
    obtain ⟨e, he⟩ := exists_isBlockOrderedSumEquiv p 1
    have hA' : (reindex e e A).PosDef := hA.submatrix e.symm.injective
    have hd : (reindex e e A).det = A.det := det_reindex_self e A
    have hm : Measurable fun y : Low (p + 1) → ℂ => ENNReal.ofReal (dens A y) := (measurable_dens A).ennreal_ofReal
    have hm2 : Measurable fun w => ENNReal.ofReal (dens A (glue e w)) := hm.comp (continuous_glue e).measurable
    obtain ⟨hDpos, hD⟩ := re_facts hA
    have hf := flagConst_pos p
    have hc : 0 ≤ A.det.re ^ (1 - (p : ℤ)) / flagConst p := by positivity
    rw [← (GlobalTheory.T.measurePreserving_glueLowerUnitriangularBlocks _ _ _ e he).lintegral_comp hm, Measure.volume_eq_prod, lintegral_prod _ hm2.aemeasurable]
    have key : ∀ v : Fin p × Fin 1 → ℂ,
        ∫⁻ w : (Low 1 → ℂ) × (Low p → ℂ), ENNReal.ofReal (dens A (glue e (v, w))) =
        ENNReal.ofReal (A.det.re ^ (1 - (p : ℤ)) / flagConst p) *
          ENNReal.ofReal ((shear (reindex e e A) (toMat v)).toBlocks₂₂.det.re ^ (-((p + 1 : ℕ) : ℤ))) := by
      intro v
      have hS := posDef_shear hA' (toMat v)
      obtain ⟨-, h2, h3⟩ := posDef_blocks hS
      have hu := h2.det_pos.ne'.isUnit
      have hm3 : Measurable fun w : (Low 1 → ℂ) × (Low p → ℂ) => ENNReal.ofReal (dens A (glue e (v, w))) :=
        hm2.comp measurable_prodMk_left
      rw [Measure.volume_eq_prod, lintegral_prod _ hm3.aemeasurable]
      have hg := fun (y1 : Low 1 → ℂ) (y2 : Low p → ℂ) => GlobalTheory.T.leadingMinorFlagDensity_glueLowerUnitriangular _ _ _ e he A (v, y1, y2) hu
      simp only [dens_one, one_mul] at hg
      simp only [hg]
      have hdet := det_eq_mul_schur hu
      rw [det_shear, hd] at hdet
      obtain ⟨hp2, he2⟩ := re_facts h2
      obtain ⟨hp3, he3⟩ := re_facts h3
      have hI := ih _ h3
      set S := shear (reindex e e A) (toMat v)
      have hn : ‖S.toBlocks₂₂.det‖ = S.toBlocks₂₂.det.re := by
        conv_lhs => rw [he2, Complex.norm_real, Real.norm_of_nonneg hp2.le]
      have hre : A.det.re = S.toBlocks₂₂.det.re * (schur S).det.re := by
        rw [hdet]; conv_lhs => rw [he2, he3, ← Complex.ofReal_mul, Complex.ofReal_re]
      rw [lintegral_const, volume_univ_of_isEmpty, mul_one, hn]
      simp only [ENNReal.ofReal_mul (zpow_nonneg hp2.le _)]
      rw [lintegral_const_mul _ (measurable_dens _).ennreal_ofReal, hI, ← ENNReal.ofReal_mul (zpow_nonneg hp2.le _),
        ← ENNReal.ofReal_mul hc, hre, mul_zpow]
      congr 1
      have : S.toBlocks₂₂.det.re ^ (-(2 * p : ℤ)) =
          S.toBlocks₂₂.det.re ^ (1 - (p : ℤ)) * S.toBlocks₂₂.det.re ^ (-((p + 1 : ℕ) : ℤ)) := by
        rw [← zpow_add₀ hp2.ne']; congr 1; push_cast; ring
      rw [this]; ring
    simp only [key]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, GlobalTheory.T.hua_integral_positive_definite_quadric p 1 _ hA', ← ENNReal.ofReal_mul hc, hd,
      flagConst_add p 1]
    congr 1
    have h1 : flagConst 1 = 1 := by simp [flagConst]
    have : A.det.re ^ (1 - ((p + 1 : ℕ) : ℤ)) = A.det.re ^ (1 - (p : ℤ)) * A.det.re ^ (-((1 : ℕ) : ℤ)) := by
      rw [← zpow_add₀ hDpos.ne']; congr 1; push_cast; ring
    rw [this, h1]; ring

end GlobalTheory.FlagFibre.FlagInt
