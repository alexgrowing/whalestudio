import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FcCont
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def adr [IsTotallyReal F] (w : InfinitePlace F) (r : ℝ) : AF F :=
  ((fun u => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal u)).symm (if u = w then r else 1),
    (1 : FiniteAdeleRing (𝓞 F) F)) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)

theorem adr_fst [IsTotallyReal F] (w u : InfinitePlace F) (r : ℝ) :
    (adr w r).1 u = (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal u)).symm (if u = w then r else 1) := rfl

theorem adr_snd [IsTotallyReal F] (w : InfinitePlace F) (r : ℝ) : (adr (F := F) w r).2 = 1 := rfl

theorem adr_mul [IsTotallyReal F] (w : InfinitePlace F) (r s : ℝ) : adr w r * adr w s = adr (F := F) w (r * s) := by
  refine Prod.ext (funext fun u => ?_) (mul_one _)
  show (adr w r).1 u * (adr w s).1 u = (adr w (r * s)).1 u
  rw [adr_fst, adr_fst, adr_fst, ← map_mul]
  congr 1
  split_ifs <;> simp

theorem adr_one [IsTotallyReal F] (w : InfinitePlace F) : adr (F := F) w 1 = 1 := by
  refine Prod.ext (funext fun u => ?_) rfl
  show (adr w 1).1 u = 1
  rw [adr_fst, ite_self, map_one]

theorem ext_adr [IsTotallyReal F] (w u : InfinitePlace F) (r : ℝ) :
    InfinitePlace.Completion.extensionEmbedding u ((adr w r).1 u) = ((if u = w then r else 1 : ℝ) : ℂ) := by
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal u), adr_fst]
  congr 1
  exact (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal u)).apply_symm_apply _

theorem finOne_adr [IsTotallyReal F] (w : InfinitePlace F) (r : ℝ) : finOne F * adr w r = finOne F := by
  refine Prod.ext ?_ (mul_one _)
  show (finOne F).1 * (adr w r).1 = (finOne F).1
  have h0 : (finOne F).1 = 0 := rfl
  rw [h0, zero_mul]

end PositivityTheory.SiegelWeilFormula.AStep

end
