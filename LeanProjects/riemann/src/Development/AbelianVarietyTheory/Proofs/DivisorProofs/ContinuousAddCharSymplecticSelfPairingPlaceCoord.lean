import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

namespace GlobalTheory.ContSymp

theorem continuous_psi_symp_atPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (o : E) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {M : Type} [Fintype M] (g : M → Matrix (Fin n) (Fin d) E),
    Continuous (fun a : M → v.adicCompletionIntegers F => ψ (⅟(2 : AF F) *
      GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) o) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB)
        (∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))
        (∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m)))) := by
  intro F E _ _ _ _ _ σ ψ hψ n d JA JB o v M _ g
  set B := GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) o) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB) with hB
  have hadd1 : ∀ x x' y, B (x + x') y = B x y + B x' y := by
    intro x x' y
    simp only [hB, GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens, ← map_add, ← mul_add, ← Finset.sum_add_distrib, Matrix.add_apply, add_mul]
  have hadd2 : ∀ x y y', B x (y + y') = B x y + B x y' := by
    intro x y y'
    simp only [hB, GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens, Matrix.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  have hsm1 : ∀ (r : AF F) x y, B (r • x) y = r * B x y := by
    intro r x y
    simp only [hB, GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens, Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, mul_smul_comm,
      LinearMap.map_smul, smul_eq_mul]
  have hsm2 : ∀ (r : AF F) x y, B x (r • y) = r * B x y := by
    intro r x y
    simp only [hB, GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens, Matrix.smul_apply, map_smul, mul_smul_comm, ← Finset.smul_sum,
      LinearMap.map_smul, smul_eq_mul]
  let Bl : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) →ₗ[AF F] Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) →ₗ[AF F] AF F :=
    LinearMap.mk₂ (AF F) B hadd1 (fun r x y => by rw [hsm1, smul_eq_mul]) hadd2 (fun r x y => by rw [hsm2, smul_eq_mul])
  have hexp : ∀ a : M → v.adicCompletionIntegers F,
      B (∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))
        (∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m)) =
      ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) * ∑ m', GlobalTheory.EmbChart.atPlace v (a m' : Fv F v) *
        B (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m)) := by
    intro a
    change Bl _ _ = _
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rfl
  simp_rw [hexp]
  have hc : ∀ m, Continuous fun a : M → v.adicCompletionIntegers F => GlobalTheory.EmbChart.atPlace v (a m : Fv F v) :=
    fun m => (GlobalTheory.VacAny.continuous_atPlace v).comp (continuous_subtype_val.comp (continuous_apply m))
  refine hψ.comp (continuous_const.mul (continuous_finset_sum _ fun m _ => (hc m).mul (continuous_finset_sum _ fun m' _ =>
    (hc m').mul continuous_const)))

end GlobalTheory.ContSymp
