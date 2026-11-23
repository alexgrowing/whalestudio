import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimeAdditiveCharacterUnramified
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.TrSumOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceEqSumMultMulRe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.PsiNontriv

variable {F : Type} [Field F] [NumberField F]

theorem trace_re (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ w : InfinitePlace F, (w.mult : ℝ) * (w.embedding x).re := by
  first
  | exact @_root_.GlobalTheory.TraceRealEmbeddingSum.trace_eq_sum_mult_mul_re
  | exact _root_.GlobalTheory.TraceRealEmbeddingSum.trace_eq_sum_mult_mul_re
  | (apply _root_.GlobalTheory.TraceRealEmbeddingSum.trace_eq_sum_mult_mul_re <;> assumption)
  | (intros; apply _root_.GlobalTheory.TraceRealEmbeddingSum.trace_eq_sum_mult_mul_re <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TraceRealEmbeddingSum.trace_eq_sum_mult_mul_re <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TraceRealEmbeddingSum.trace_eq_sum_mult_mul_re ..)

theorem trace_mixedEmbedding (x : F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (mixedEmbedding F x) = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  rw [trace_re, Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi,
    InfinitePlace.sum_eq_sum_add_sum]
  simp only [Algebra.trace_complex_apply, mixedEmbedding.mixedEmbedding_apply_isReal,
    mixedEmbedding.mixedEmbedding_apply_isComplex, Algebra.trace_self_apply]
  congr 1
  · refine Fintype.sum_congr _ _ fun w => ?_
    rw [InfinitePlace.mult_isReal, Nat.cast_one, one_mul, ← InfinitePlace.embedding_of_isReal_apply w.2,
      Complex.ofReal_re]
  · refine Fintype.sum_congr _ _ fun w => ?_
    rw [InfinitePlace.mult_isComplex]
    push_cast
    rfl

end GlobalTheory.PsiNontriv

namespace GlobalTheory.PsiNontriv

open GlobalTheory.Idele WithZero
open GlobalTheory.StdDual (codiff codiff_ne_zero)

variable {F : Type} [Field F] [NumberField F]

theorem at_pairA_zero (a : Ainf F) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (pairA F a 0) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  refine Prod.ext ?_ ?_
  · change u.1 * a = 0
    rw [h1, zero_mul]
  · change u.2 * 0 = 0
    exact mul_zero _

theorem isStd_fin_rat {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : F) :
    ψ (pairA F 0 (algebraMap F (Af F) x)) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ)) := by
  have e : pairA F 0 (algebraMap F (Af F) x) =
      algebraMap F (AF F) x + pairA F (algebraMap F (Ainf F) (-x)) 0 := by
    refine Prod.ext ?_ (add_zero _).symm
    show (0 : Ainf F) = algebraMap F (Ainf F) x + algebraMap F (Ainf F) (-x)
    rw [map_neg, add_neg_cancel]
  have hev : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (pairA F (algebraMap F (Ainf F) (-x)) 0) = mixedEmbedding F (-x) :=
    (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (K := F)).symm
  rw [e, AddChar.map_add_eq_mul, hψ.2.1, one_mul, hψ.2.2 _ (at_pairA_zero _), hev, map_neg, map_neg,
    trace_mixedEmbedding]
  congr 1
  push_cast
  ring

theorem psiAt_ne_one : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, GlobalTheory.LatVac.psiAt ψ v ≠ 1 := by
  intro F _ _ ψ hψ v h1
  set c := FractionalIdeal.count F v (codiff F) with hc
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  set x : Fv F v := algebraMap F (Fv F v) (π ^ (c - 1)) with hx
  have hmem : GlobalTheory.AdelicU.singleFin v x ∈ adelicIdeal (codiff F) := by
    rw [GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (isStd_fin_rat hψ)]
    intro α hα
    have e : α * GlobalTheory.AdelicU.singleFin v x = GlobalTheory.AdelicU.singleFin v (α v * x) := by
      apply GlobalTheory.AdelicU.af_ext
      intro u
      by_cases hu : u = v
      · subst hu
        rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]
        rfl
      · rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]
    rw [e]
    have := DFunLike.congr_fun h1 (α v * x)
    rw [AddChar.one_apply] at this
    exact this
  have h2 := (mem_adelicIdeal_iff codiff_ne_zero).1 hmem v
  rw [show (GlobalTheory.AdelicU.singleFin v x) v = x from GlobalTheory.AdelicU.evalV_singleFin_self v x, hx, valued_algebraMap,
    map_zpow₀, hπ, ← WithZero.exp_zsmul, WithZero.exp_le_exp, smul_eq_mul] at h2
  omega

end GlobalTheory.PsiNontriv
