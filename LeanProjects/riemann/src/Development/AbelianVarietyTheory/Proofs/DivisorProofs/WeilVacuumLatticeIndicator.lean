import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWittModelUnitaryActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetCoverMatrixValuationOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeltaHalfMulUnrTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConduct
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
open Formalism.UG (IsUnifV qV)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.KSplit

theorem one_mem_UAt_fin {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (X : Spc F E n) (v : Pl F) : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := by
  intro u _
  simp [mat]

theorem prod_zpow_eq_zpow_sum' {G ι : Type*} [CommGroup G] (a : G) (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, a ^ f i = a ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add]

end GlobalTheory.KSplit

theorem GlobalTheory.KSplit.vac_act_torus : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r₁ s₁ : ℕ),
    IsPair B M χX χW om r s r₁ s₁ →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) ι, M.IsLinW B.ψ t b c ι →
    ι (M.vac v) = Set.indicator {Y | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} 1 → UnrAt χW (splitPrime t) →
    ∀ (ϖ : (Fv F v)ˣ), IsUnifV F v ϖ.1 → ∀ (e : Fin n → ℤ) (T : GL (Fin n) (Fv F v)), T.1 = Matrix.diagonal (fun i => ϖ.1 ^ e i) → ∀ k₁ ∈ KGL v n, ∀ k₂ ∈ KGL v n,
    ∀ g ∈ UAt σ X (evFin F v), GlobalTheory.KSplit.locMat t b g = k₁ * T * k₂ →
      ∃ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (g, 1)) (M.vac v) φ₁ ∧
        ι φ₁ = ((chrW χW t ϖ : ℂ) ^ (∑ j, e j) * (((qV F v : ℝ) ^ ((d : ℝ) / 2 * ((∑ j, e j : ℤ) : ℝ)) : ℝ) : ℂ)) •
          Set.indicator {Y : Matrix (Fin n) (Fin d) (Fv F v) | ∀ i j, (((k₁ * T * k₂)⁻¹).1 * Y) i j ∈ v.adicCompletionIntegers F} 1 := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r₁ s₁ hP v t b c ι hι hvac hunr ϖ hϖ e T hT k₁ hk₁ k₂ hk₂ g hg hgk
  have h1 := GlobalTheory.KSplit.one_mem_UAt_fin σ W v
  obtain ⟨φ₁, ⟨hφ₁SB, hφ₁⟩, -⟩ :=
    (GlobalTheory.T.theta_action_exists hPr F E σ B n d X W M χX χW om r s r₁ s₁ hP v).1 g hg 1 h1 (M.vac v) (hP.good.vac v).1
  refine ⟨φ₁, hφ₁SB, hφ₁, ?_⟩
  rw [GlobalTheory.T.linear_witt_model_unitary_action hPr F E σ B n d X W M χX χW om r s r₁ s₁ hP v t b c ι hι g hg 1 h1 _ (hP.good.vac v).1 φ₁ hφ₁SB
    hφ₁, hvac, map_one, hgk]
  set u : (Fv F v)ˣ := GlobalTheory.SplitFlip.gdet k₁ * GlobalTheory.SplitFlip.gdet k₂ with hu
  have hdetT : GlobalTheory.SplitFlip.gdet T = ϖ ^ (∑ j, e j) := by
    rw [← GlobalTheory.KSplit.prod_zpow_eq_zpow_sum']
    apply Units.ext
    show T.1.det = _
    rw [hT, Matrix.det_diagonal, Units.coe_prod]
    simp only [Units.val_zpow_eq_zpow_val]
  have hdet : GlobalTheory.SplitFlip.gdet (k₁ * T * k₂) = u * ϖ ^ (∑ j, e j) := by
    rw [GlobalTheory.SplitFlip.gdet_mul, GlobalTheory.SplitFlip.gdet_mul, hdetT, hu, mul_right_comm]
  have hvu : Valued.v ((u : Fv F v)) = 1 := by
    simp only [hu, Units.val_mul, map_mul]
    rw [show ((GlobalTheory.SplitFlip.gdet k₁ : (Fv F v)ˣ) : Fv F v) = k₁.1.det from rfl,
      show ((GlobalTheory.SplitFlip.gdet k₂ : (Fv F v)ˣ) : Fv F v) = k₂.1.det from rfl,
      GlobalTheory.GLintCover.det_v hk₁, GlobalTheory.GLintCover.det_v hk₂, one_mul]
  have hchr : chrW χW t u = 1 :=
    (GlobalTheory.ChrWLocal.isUnram_chrW_iff χW t).2 hunr u ((GlobalTheory.ChrWLocal.valuation_eq_one_iff _).2 hvu)
  have hvD : Valued.v ((GlobalTheory.SplitFlip.gdet (k₁ * T * k₂) : (Fv F v)ˣ) : Fv F v) =
      WithZero.exp (-(∑ j, e j)) := by
    rw [hdet, Units.val_mul, map_mul, hvu, one_mul, Units.val_zpow_eq_zpow_val, map_zpow₀]
    rw [show Valued.v (ϖ : Fv F v) = WithZero.exp (-1 : ℤ) from hϖ, ← WithZero.exp_zsmul]
    simp
  have hnabs : GlobalTheory.SplitWeil.nabs (Fv F v) (GlobalTheory.SplitFlip.gdet (k₁ * T * k₂)) =
      (qV F v : ℝ) ^ (-(∑ j, e j)) := by
    rw [GlobalTheory.LGrp.BorelCompletion.nabs_completion, hvD, WithZero.log_exp]
  have hq : (0 : ℝ) ≤ (qV F v : ℝ) := Nat.cast_nonneg _
  funext Y
  simp only [GlobalTheory.SplitFlip.omA, MonoidHom.inv_apply, inv_inv, map_one, Units.val_one, one_mul, Matrix.mul_one,
    Fintype.card_fin, Pi.smul_apply, smul_eq_mul]
  rw [hdet, map_mul, hchr, one_mul, map_zpow, Units.val_zpow_eq_zpow_val]
  rw [← hdet]
  have ha1 : GlobalTheory.SplitFlip.apow (1 : (Fv F v)ˣ) (-(n : ℂ) / 2) = 1 := by
    simp [GlobalTheory.SplitFlip.apow, GlobalTheory.SplitWeil.nabs]
  have haD : GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (k₁ * T * k₂)) (-(d : ℂ) / 2) =
      (((qV F v : ℝ) ^ ((d : ℝ) / 2 * ((∑ j, e j : ℤ) : ℝ)) : ℝ) : ℂ) := by
    rw [GlobalTheory.SplitFlip.apow, hnabs, show (-(d : ℂ) / 2) = ((-(d : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (zpow_nonneg hq _), ← Real.rpow_intCast, ← Real.rpow_mul hq]
    congr 2
    push_cast; ring
  rw [ha1, haD, mul_one]
  simp only [Pi.smul_apply, smul_eq_mul, mul_one]
  rfl
