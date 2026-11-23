import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSizeRWordNeTopOfLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RWordRTrAdelic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsModGrowthExpLeNormInfPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspFunctionClosedUnderOperations

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.Grow GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.Size
open scoped ENNReal NNReal

namespace GlobalTheory.Size.Translate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem wordSum_succ {ι X : Type} [Fintype ι] (A : ι → X → X) (p : X → ℝ≥0∞) (d : ℕ) (x : X) :
    wordSum A p (d + 1) x = p x + ∑ i, wordSum A p d (A i x) := by
  classical
  unfold wordSum
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  · simp [wordAct_nil]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Fintype.sum_prod_type']
    symm
    refine Fintype.sum_equiv (Fin.snocEquiv fun _ => ι) _ _ fun q => ?_
    change _ = p (wordAct A (List.ofFn (fun i => (Fin.snoc (α := fun _ => ι) q.2 q.1 i : ι))) x)
    rw [List.ofFn_succ']
    simp [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append, wordAct_append, wordAct_cons, wordAct_nil]

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem growthSob_sum_le {α : Type} (s : Finset α) (f : α → GA D V → ℂ) (hf : ∀ a, f a ∈ SmFun θ V) (d N : ℕ) :
    growthSob θ V d N (∑ a ∈ s, f a) ≤ ∑ a ∈ s, growthSob θ V d N (f a) := by
  classical
  induction s using Finset.induction_on
  · simpa using growthSob_smul (θ := θ) (φ := (0 : GA D V → ℂ)) (0 : ℂ) d N
  · rename_i a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (growthSob_add_le (hf a) (Submodule.sum_mem _ fun b _ => hf b) d N).trans (add_le_add le_rfl ih)

theorem growthSob_RderC_le (hθ : IsInfFam θ) {φ : GA D V → ℂ} (hs : φ ∈ SmFun θ V) (τ : D.what₂.Tau)
    {Z : Matrix (Fin V.rank) (Fin V.rank) ℂ} {B : ℝ≥0∞} (hB : ∀ a b, ‖Z a b‖ₑ ≤ B) (d N : ℕ) :
    growthSob θ V d N (RderC θ V τ Z φ) ≤
      (Fintype.card (Fin V.rank × Fin V.rank) : ℝ≥0∞) * (B * growthSob θ V (d + 1) N φ) := by
  rw [RderC_eq_sum_glDer hθ hs τ Z]
  have hmem : ∀ a : Fin V.rank × Fin V.rank, Z a.1 a.2 • glDer θ V (τ, a) φ ∈ SmFun θ V := fun a =>
    (SmFun θ V).smul_mem _ ((linOnSm_RderC (θ := θ) τ (Matrix.single a.1 a.2 1)).mem φ hs)
  refine (growthSob_sum_le Finset.univ _ hmem d N).trans ?_
  calc ∑ a : Fin V.rank × Fin V.rank, growthSob θ V d N (Z a.1 a.2 • glDer θ V (τ, a) φ)
      ≤ ∑ _a : Fin V.rank × Fin V.rank, B * growthSob θ V (d + 1) N φ := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [growthSob_smul]
        exact mul_le_mul' (hB a.1 a.2)
          (wordSum_letter_le (A := glDer θ V) (p := growthSize V N) d (τ, a) φ)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem growthSize_rTr_le (h : GA D V) (N : ℕ) (φ : GA D V → ℂ) :
    growthSize V N (rTr V h φ) ≤ ENNReal.ofReal (height V h) ^ N * growthSize V N φ := by
  obtain ⟨h1, -, -, hmul, -⟩ := height_laws V
  unfold growthSize
  refine iSup_le fun g => ?_
  have hgpos : 0 < height V g := lt_of_lt_of_le one_pos (h1 g)
  have hhpos : 0 < height V h := lt_of_lt_of_le one_pos (h1 h)
  have hghpos : 0 < height V (g * h) := lt_of_lt_of_le one_pos (h1 (g * h))
  have hq : 0 ≤ ‖φ (g * h)‖ / height V (g * h) ^ N := div_nonneg (norm_nonneg _) (pow_pos hghpos N).le
  have key : ‖rTr V h φ g‖ / height V g ^ N ≤ height V h ^ N * (‖φ (g * h)‖ / height V (g * h) ^ N) := by
    change ‖φ (g * h)‖ / height V g ^ N ≤ _
    rw [div_le_iff₀ (pow_pos hgpos N)]
    have hp : height V (g * h) ^ N ≤ (height V g * height V h) ^ N := pow_le_pow_left₀ hghpos.le (hmul g h) N
    calc ‖φ (g * h)‖ = ‖φ (g * h)‖ / height V (g * h) ^ N * height V (g * h) ^ N :=
          (div_mul_cancel₀ _ (pow_pos hghpos N).ne').symm
      _ ≤ ‖φ (g * h)‖ / height V (g * h) ^ N * (height V g * height V h) ^ N := mul_le_mul_of_nonneg_left hp hq
      _ = height V h ^ N * (‖φ (g * h)‖ / height V (g * h) ^ N) * height V g ^ N := by ring
  calc ENNReal.ofReal (‖rTr V h φ g‖ / height V g ^ N)
      ≤ ENNReal.ofReal (height V h ^ N * (‖φ (g * h)‖ / height V (g * h) ^ N)) := ENNReal.ofReal_le_ofReal key
    _ = ENNReal.ofReal (height V h) ^ N * ENNReal.ofReal (‖φ (g * h)‖ / height V (g * h) ^ N) := by
        rw [ENNReal.ofReal_mul (pow_pos hhpos N).le, ENNReal.ofReal_pow hhpos.le]
    _ ≤ ENNReal.ofReal (height V h) ^ N * ⨆ g', ENNReal.ofReal (‖φ g'‖ / height V g' ^ N) :=
        by gcongr; exact le_iSup (fun g' => ENNReal.ofReal (‖φ g'‖ / height V g' ^ N)) (g * h)

theorem exists_adAt_le (hθ : IsInfFam θ) (V : HSp D) : ∃ C : ℝ≥0, ∀ (h : GA D V) τ a b c d,
    ‖adAt θ h τ (Matrix.single a b 1) c d‖ₑ ≤ C * ENNReal.ofReal (height V h) ^ 2 := by
  obtain ⟨C, hC⟩ := normInf_le_height V hθ
  refine ⟨Real.toNNReal (C ^ 2), fun h τ a b c d => ?_⟩
  have hent : ∀ i j, ‖infMat D.sp.cm.sig V.gram (θ τ) h i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i j‖ ≤
      C * height V h := by
    intro i j
    refine le_trans ?_ (hC h)
    calc ‖infMat D.sp.cm.sig V.gram (θ τ) h i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i j‖
        ≤ ∑ j', (‖infMat D.sp.cm.sig V.gram (θ τ) h i j'‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i j'‖) :=
          Finset.single_le_sum (f := fun j' => ‖infMat D.sp.cm.sig V.gram (θ τ) h i j'‖ +
            ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i j'‖) (fun _ _ => by positivity) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', (‖infMat D.sp.cm.sig V.gram (θ τ) h i' j'‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i' j'‖) :=
          Finset.single_le_sum (f := fun i' => ∑ j', (‖infMat D.sp.cm.sig V.gram (θ τ) h i' j'‖ +
            ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i' j'‖)) (fun _ _ => by positivity) (Finset.mem_univ i)
      _ ≤ ∑ τ', ∑ i', ∑ j', (‖infMat D.sp.cm.sig V.gram (θ τ') h i' j'‖ +
            ‖infMat D.sp.cm.sig V.gram (θ τ') h⁻¹ i' j'‖) :=
          Finset.single_le_sum (f := fun τ' => ∑ i', ∑ j', (‖infMat D.sp.cm.sig V.gram (θ τ') h i' j'‖ +
            ‖infMat D.sp.cm.sig V.gram (θ τ') h⁻¹ i' j'‖)) (fun _ _ => by positivity) (Finset.mem_univ τ)
      _ = _ := rfl
  have hcomp : adAt θ h τ (Matrix.single a b 1) c d =
      infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ c a * infMat D.sp.cm.sig V.gram (θ τ) h b d := by
    simp [adAt, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']
  have hx := hent c a
  have hy := hent b d
  have hx' : ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ c a‖ ≤ C * height V h := by
    linarith [norm_nonneg (infMat D.sp.cm.sig V.gram (θ τ) h c a)]
  have hy' : ‖infMat D.sp.cm.sig V.gram (θ τ) h b d‖ ≤ C * height V h := by
    linarith [norm_nonneg (infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ b d)]
  have hht : 0 ≤ height V h := le_trans zero_le_one ((height_laws V).1 h)
  have hreal : ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ c a‖ * ‖infMat D.sp.cm.sig V.gram (θ τ) h b d‖ ≤
      C ^ 2 * height V h ^ 2 := by
    calc _ ≤ (C * height V h) * (C * height V h) :=
          mul_le_mul hx' hy' (norm_nonneg _) ((norm_nonneg _).trans hx')
      _ = C ^ 2 * height V h ^ 2 := by ring
  rw [hcomp, ← ofReal_norm_eq_enorm, norm_mul]
  calc ENNReal.ofReal (‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ c a‖ * ‖infMat D.sp.cm.sig V.gram (θ τ) h b d‖)
      ≤ ENNReal.ofReal (C ^ 2 * height V h ^ 2) := ENNReal.ofReal_le_ofReal hreal
    _ = _ := by rw [ENNReal.ofReal_mul (sq_nonneg C), ENNReal.ofReal_pow hht]; rfl

private theorem rderC_rTr' (hθ : IsInfFam θ) (h : GA D V) {φ : GA D V → ℂ} (hs : φ ∈ SmFun θ V)
    (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    RderC θ V τ Z (rTr V h φ) = rTr V h (RderC θ V τ (adAt θ h τ Z) φ) := by
  obtain ⟨hX, hY⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  have hZ := (GlobalTheory.SmoothAutCheck.parts_sum V τ Z).symm
  set X := (1 / 2 : ℂ) • (Z + conjAt V τ Z) with hXdef
  set Y := (1 / (2 * Complex.I)) • (Z - conjAt V τ Z) with hYdef
  have hsum : adAt θ h τ Z = adAt θ h τ X + Complex.I • adAt θ h τ Y := by
    conv_lhs => rw [hZ]
    simp only [adAt, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hsum, RderC_add hθ hs, RderC_smul hθ hs,
    GlobalTheory.SmoothAutCheck.RderC_eq θ V τ (adAt_mem_lieAt hθ h hX),
    GlobalTheory.SmoothAutCheck.RderC_eq θ V τ (adAt_mem_lieAt hθ h hY)]
  change Rder θ V τ X (rTr V h φ) + Complex.I • Rder θ V τ Y (rTr V h φ) = _
  rw [Rder_rTr_adelic hθ h hX, Rder_rTr_adelic hθ h hY]
  rfl

theorem exists_growthSob_rTr_le (hθ : IsInfFam θ) (V : HSp D) (N d : ℕ) : ∃ C : ℝ≥0, ∀ h ∈ GinfC V, ∀ φ ∈ SmFun θ V,
    growthSob θ V d N (rTr V h φ) ≤ C * ENNReal.ofReal (height V h) ^ (N + 2 * d) * growthSob θ V d N φ := by
  obtain ⟨C₁, hC₁⟩ := exists_adAt_le hθ V
  induction d with
  | zero =>
    refine ⟨1, fun h _ φ _ => ?_⟩
    simpa [growthSob, wordSum_zero] using growthSize_rTr_le h N φ
  | succ d ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨1 + (Fintype.card (D.what₂.Tau × Fin V.rank × Fin V.rank) : ℝ≥0) * C *
      (Fintype.card (Fin V.rank × Fin V.rank) : ℝ≥0) * C₁, fun h hh φ hs => ?_⟩
    have hT : 1 ≤ ENNReal.ofReal (height V h) := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal ((height_laws V).1 h)
    have hS0 : growthSize V N φ ≤ growthSob θ V (d + 1) N φ :=
      le_wordSum (A := glDer θ V) (p := growthSize V N) (l := []) (Nat.zero_le _) φ
    have hterm : ∀ a : D.what₂.Tau × Fin V.rank × Fin V.rank,
        growthSob θ V d N (glDer θ V a (rTr V h φ)) ≤
          C * ENNReal.ofReal (height V h) ^ (N + 2 * d) *
            ((Fintype.card (Fin V.rank × Fin V.rank) : ℝ≥0∞) *
              ((C₁ * ENNReal.ofReal (height V h) ^ 2) * growthSob θ V (d + 1) N φ)) := by
      intro a
      have e : glDer θ V a (rTr V h φ) =
          rTr V h (RderC θ V a.1 (adAt θ h a.1 (Matrix.single a.2.1 a.2.2 1)) φ) :=
        rderC_rTr' hθ h hs a.1 _
      rw [e]
      refine (hC h hh _ ((linOnSm_RderC (θ := θ) a.1 _).mem φ hs)).trans ?_
      gcongr
      exact growthSob_RderC_le hθ hs a.1 (fun b c => hC₁ h a.1 a.2.1 a.2.2 b c) d N
    have hpow : ENNReal.ofReal (height V h) ^ N ≤ ENNReal.ofReal (height V h) ^ (N + 2 * (d + 1)) :=
      pow_le_pow_right₀ hT (by omega)
    have e0 : growthSob θ V (d + 1) N (rTr V h φ) =
        growthSize V N (rTr V h φ) + ∑ a, growthSob θ V d N (glDer θ V a (rTr V h φ)) :=
      wordSum_succ _ _ _ _
    rw [e0]
    calc growthSize V N (rTr V h φ) + ∑ a, growthSob θ V d N (glDer θ V a (rTr V h φ))
        ≤ ENNReal.ofReal (height V h) ^ (N + 2 * (d + 1)) * growthSob θ V (d + 1) N φ +
          ∑ _a : D.what₂.Tau × Fin V.rank × Fin V.rank, C * ENNReal.ofReal (height V h) ^ (N + 2 * d) *
            ((Fintype.card (Fin V.rank × Fin V.rank) : ℝ≥0∞) *
              ((C₁ * ENNReal.ofReal (height V h) ^ 2) * growthSob θ V (d + 1) N φ)) :=
          add_le_add ((growthSize_rTr_le h N φ).trans (mul_le_mul' hpow hS0))
            (Finset.sum_le_sum fun a _ => hterm a)
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          push_cast
          ring

theorem growthSob_rTr_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (d N : ℕ), ∃ (C : NNReal) (m : ℕ),
    ∀ h ∈ GinfC V, ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, GlobalTheory.Size.growthSob θ V d N (rTr V h φ) ≤
      (C : ENNReal) * ENNReal.ofReal (GlobalTheory.Grow.height V h ^ m) * GlobalTheory.Size.growthSob θ V d N φ := by
  intro D θ hθ V d N
  obtain ⟨C, hC⟩ := exists_growthSob_rTr_le hθ V N d
  refine ⟨C, N + 2 * d, fun h hh φ hφ => ?_⟩
  rw [ENNReal.ofReal_pow (le_trans zero_le_one ((height_laws V).1 h))]
  exact hC h hh φ hφ

end GlobalTheory.Size.Translate

end
