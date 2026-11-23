import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockEmbeddingFiniteAdelicGLCompatContinuous
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeightBlockEmbeddingLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ContinuousConstantTerm
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermLeviRationalLeftInvariant
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HasModerateGrowthConstantTerm
import Development.AutomorphicArithmetic.WhittakerHecke.BlockDiagonalEqLeviEmbedding

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open PositivityTheory.Rg.Tf.Core (qht)

namespace UpperTheory.ConvolutionTheory.BW.Pair

variable {E : Type} [Field E] [NumberField E] {r s : ℕ}

theorem out_eq {h : AdelicGLn.AdelicGL E r → ℂ}
    (hh : AutomorphicForm.IsLeftInvariant h) (y : RightCosetSpace (rationalGLOne E r)) :
    h ((Quotient.out y : normOneGL E r) : AdelicGLn.AdelicGL E r) = CuspidalSpectrum.cuspQuot hh y := by
  conv_rhs => rw [← Quotient.out_eq y]
  rfl

theorem int_of {h : AdelicGLn.AdelicGL E r → ℂ}
    (hh : AutomorphicForm.IsLeftInvariant h) (hc : Continuous h) {C : ℝ} (hC : ∀ y : normOneGL E r, ‖h y‖ ≤ C) :
    Integrable (fun y : RightCosetSpace (rationalGLOne E r) =>
      h ((Quotient.out y : normOneGL E r) : AdelicGLn.AdelicGL E r)) (quotientMeasure (rationalGLOne E r) (mu1 E r)) := by
  have hfin := Reduction.isFiniteMeasure_quotientMeasure (K := E) (n := r) (mu1 E r)
  refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun y => hC _)
  rw [funext (out_eq hh)]
  exact (CuspidalSpectrum.continuous_cuspQuot hh hc).aestronglyMeasurable

theorem one_le_qht (x : normOneGL E r) : 1 ≤ qht x := le_ciInf fun _ => AutomorphicForm.one_le_height _

theorem le_qht {F : AdelicGLn.AdelicGL E r → ℂ} (hF : AutomorphicForm.IsLeftInvariant F) {B : ℝ} {N : ℕ} (hB : 0 ≤ B)
    (h : ∀ x : normOneGL E r, ‖F x‖ ≤ B * AutomorphicForm.height (x : AdelicGLn.AdelicGL E r) ^ N) (x : normOneGL E r) :
    ‖F x‖ ≤ B * 2 ^ N * qht x ^ N := by
  have h1 := one_le_qht x
  obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt (show qht x < 2 * qht x by linarith)
  obtain ⟨γ', hγ'⟩ := Subgroup.mem_subgroupOf.1 γ.2
  have e : F ((γ : normOneGL E r) * x : normOneGL E r) = F x := by
    change F (((γ : normOneGL E r) : AdelicGLn.AdelicGL E r) * x) = F x
    rw [← hγ']
    exact hF γ' x
  rw [← e, mul_assoc, ← mul_pow]
  exact (h _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (AutomorphicForm.height_pos _).le hγ.le N) hB)

theorem pair_le {F ψ : AdelicGLn.AdelicGL E r → ℂ} (hF : AutomorphicForm.IsLeftInvariant F) {B C : ℝ} {N : ℕ} (hB : 0 ≤ B)
    (h : ∀ x : normOneGL E r, ‖F x‖ ≤ B * AutomorphicForm.height (x : AdelicGLn.AdelicGL E r) ^ N)
    (hψ : ∀ x : normOneGL E r, ‖ψ x‖ * qht x ^ N ≤ C) (x : normOneGL E r) :
    ‖F x * starRingEnd ℂ (ψ x)‖ ≤ B * 2 ^ N * C := by
  rw [norm_mul, RCLike.norm_conj]
  refine (mul_le_mul_of_nonneg_right (le_qht hF hB h x) (norm_nonneg _)).trans ?_
  rw [mul_assoc, mul_comm (qht x ^ N)]
  exact mul_le_mul_of_nonneg_left (hψ x) (by positivity)

theorem pair_int {F ψ : AdelicGLn.AdelicGL E r → ℂ} (hF : AutomorphicForm.IsLeftInvariant F)
    (hψl : AutomorphicForm.IsLeftInvariant ψ) (hFc : Continuous F) (hψc : Continuous ψ) {B C : ℝ} {N : ℕ}
    (h : ∀ x : normOneGL E r, ‖F x‖ ≤ B * AutomorphicForm.height (x : AdelicGLn.AdelicGL E r) ^ N)
    (hψ : ∀ x : normOneGL E r, ‖ψ x‖ * qht x ^ N ≤ C) :
    Integrable (fun y : RightCosetSpace (rationalGLOne E r) =>
      F ((Quotient.out y : normOneGL E r) : AdelicGLn.AdelicGL E r) *
        starRingEnd ℂ (ψ ((Quotient.out y : normOneGL E r) : AdelicGLn.AdelicGL E r)))
      (quotientMeasure (rationalGLOne E r) (mu1 E r)) := by
  have hB : 0 ≤ |B| := abs_nonneg B
  refine int_of (h := fun x => F x * starRingEnd ℂ (ψ x)) (fun γ x => ?_) (hFc.mul (Complex.continuous_conj.comp hψc))
    (pair_le hF hB (fun x => (h x).trans ?_) hψ)
  · beta_reduce
    rw [hF γ, hψl γ]
  · exact mul_le_mul_of_nonneg_right (le_abs_self B) (pow_nonneg (AutomorphicForm.height_pos _).le N)

theorem height_lev (x : AdelicGLn.AdelicGL E r) (m : AdelicGLn.AdelicGL E s) :
    AutomorphicForm.height (K := E) (lev (Ad E) r s (x, m)) ≤
      AutomorphicForm.heightConst E (r + s) * AutomorphicForm.height x * AutomorphicForm.height m := by
  rw [← UpperTheory.blockDiagonal_eq_leviEmbedding]
  have h0 : 0 ≤ AutomorphicForm.heightConst E (r + s) := zero_le_one.trans AutomorphicForm.one_le_heightConst
  refine (AutomorphicForm.height_mul_le _ _).trans ?_
  exact mul_le_mul (mul_le_mul_of_nonneg_left (UpperTheory.height_blockEmbedding_le E _ _ _ x) h0) (UpperTheory.height_blockEmbedding_le E _ _ _ m)
    (AutomorphicForm.height_pos _).le (mul_nonneg h0 (AutomorphicForm.height_pos _).le)

theorem continuous_lev : Continuous fun p : AdelicGLn.AdelicGL E r × AdelicGLn.AdelicGL E s =>
    (lev (Ad E) r s p : AdelicGLn.AdelicGL E (r + s)) := by
  have e : (fun p : AdelicGLn.AdelicGL E r × AdelicGLn.AdelicGL E s => (lev (Ad E) r s p : AdelicGLn.AdelicGL E (r + s))) =
      fun p => UpperTheory.V.Af.Fin.blk p.1 p.2 := funext fun p => (UpperTheory.blockDiagonal_eq_leviEmbedding _ r s p.1 p.2).symm
  rw [e]
  have h : ∀ {a : ℕ} (e : Fin a ↪ Fin (r + s)),
      Continuous (UpperTheory.V.Af.Fin.emb e : AdelicGLn.AdelicGL E a → AdelicGLn.AdelicGL E (r + s)) := fun {a} e => by
    refine Continuous.units_map (UpperTheory.V.Af.Fin.embM (R := Ad E) e) ?_
    change Continuous fun X : Matrix (Fin a) (Fin a) (Ad E) =>
      1 + UpperTheory.V.Af.Fin.inc e (Ad E) * (X - 1) * (UpperTheory.V.Af.Fin.inc e (Ad E)).transpose
    exact continuous_const.add
      ((continuous_const.matrix_mul (continuous_id.sub continuous_const)).matrix_mul continuous_const)
  exact ((h _).comp continuous_fst).mul ((h _).comp continuous_snd)

theorem ct_lev_rat {φ : AdelicGLn.AdelicGL E (r + s) → ℂ} (hφ : AutomorphicForm.IsLeftInvariant φ)
    (γ₁ : GL (Fin r) E) (γ₂ : GL (Fin s) E) (x : AdelicGLn.AdelicGL E r) (m : AdelicGLn.AdelicGL E s) :
    AutomorphicForm.constantTerm r φ (lev (Ad E) r s (AdelicGLn.diagonal E r γ₁ * x, AdelicGLn.diagonal E s γ₂ * m)) =
      AutomorphicForm.constantTerm r φ (lev (Ad E) r s (x, m)) := by
  rw [← UpperTheory.constantTerm_levi_rational_left_invariant E r s φ hφ γ₁ γ₂ (lev (Ad E) r s (x, m)), ← Prod.mk_mul_mk, map_mul, ← UpperTheory.blockDiagonal_eq_leviEmbedding]
  congr 2
  rw [UpperTheory.V.Af.Fin.blk, UpperTheory.V.Af.Fin.blk, map_mul, (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous E _ _ _).2.1, (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous E _ _ _).2.1]

end UpperTheory.ConvolutionTheory.BW.Pair
