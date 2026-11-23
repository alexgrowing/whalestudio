import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocDerBig

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Kdil

instance firstCountable_GR (n : ℕ) : FirstCountableTopology (GR n) := by
  haveI : FirstCountableTopology (M2 n) :=
    inferInstanceAs (FirstCountableTopology (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℂ))
  haveI : FirstCountableTopology (M2 n)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.firstCountableTopology
  haveI : FirstCountableTopology (GL (Fin n ⊕ Fin n) ℂ) := Units.isEmbedding_embedProduct.firstCountableTopology
  exact Topology.IsEmbedding.subtypeVal.firstCountableTopology

end PositivityTheory.SiegelWeilFormula.Kdil

end
