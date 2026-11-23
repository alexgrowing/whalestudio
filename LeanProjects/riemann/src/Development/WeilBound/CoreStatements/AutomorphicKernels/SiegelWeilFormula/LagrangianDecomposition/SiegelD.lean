import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SiegelC

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

def AdaptedChar : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (m n : ℕ) (bs : Module.Basis (Fin 2) F E) (A : Spc F E m) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E)
  (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (Fin m × Fin n × Fin 2)),
  IsAdapted bs A Y b dd → IsFrame2 σ Y b →
  (∀ z : Matrix (Fin m) (Fin n) (AE F E),
      (dd.e (z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ)).1 = 0) ∧
  ∀ y : Fin m × Fin n × Fin 2 → AF F, ∃ z : Matrix (Fin m) (Fin n) (AE F E),
      dd.e (z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ) = (0, y)

end PositivityTheory.SiegelWeilFormula.Ald

end
