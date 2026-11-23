import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.mwAt :
    MWAt := by
  intro E _ _ _ n l v
  have hne : ComplexEmbedding.conjugate v.embedding ≠ v.embedding := fun h =>
    (InfinitePlace.isComplex_iff.1 (NumberField.IsTotallyComplex.isComplex v))
      (ComplexEmbedding.isReal_iff.2 h)
  have hmk : InfinitePlace.mk (ComplexEmbedding.conjugate v.embedding) = v := by
    rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  constructor
  · unfold mW PositivityTheory.Rg.BcB.CG.mOf infOfWeight PositivityTheory.RgBcC.infOf
    simp only [InfinitePlace.mk_embedding, decide_true, if_true, one_mul]
    congr 1
    funext k
    rw [add_sub_assoc]
  · unfold mW PositivityTheory.Rg.BcB.CG.mOf infOfWeight PositivityTheory.RgBcC.infOf
    simp only [hmk, hne, decide_false, Multiset.map_map]
    congr 1
    funext k
    simp only [Function.comp, Bool.false_eq_true, if_false]
    ring
