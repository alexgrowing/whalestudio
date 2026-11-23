import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.RightSub
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep

open scoped TensorProduct Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.RealLift UpperTheory.TP.RP

theorem UpperTheory.TP.RP.embBij :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E),
      Function.Bijective (fun w : InfinitePlace (maximalRealSubfield E) => InfinitePlace.mk (B.emb w).1) := by
  intro E _ _ _ B
  have key : ∀ w, IsCMField.equivInfinitePlace E (InfinitePlace.mk (B.emb w).1) = w := by
    intro w
    rw [IsCMField.equivInfinitePlace_apply, InfinitePlace.comap_mk, (B.emb w).2,
      InfinitePlace.mk_embedding]
  have hf : (fun w => InfinitePlace.mk (B.emb w).1) = (IsCMField.equivInfinitePlace E).symm := by
    funext w
    rw [Equiv.eq_symm_apply]
    exact key w
  rw [hf]
  exact Equiv.bijective _
