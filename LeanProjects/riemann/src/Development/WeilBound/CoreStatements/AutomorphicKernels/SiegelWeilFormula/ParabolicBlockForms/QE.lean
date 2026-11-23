import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.NilpotentFramePartApplyZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.MemStabiliserIffFrameLowerBlock
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.ExistsGlCol
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.FrameInvPf

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C4

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace Bq

def QE (n : ℕ) (ε : ℤˣ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E :=
  Matrix.fromBlocks 0 1 ((((ε : ℤ) : E)) • 1) 0

theorem sum_emb {α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M] (e : α → β) (he : Function.Injective e)
    (f : β → M) (h : ∀ b, b ∉ Set.range e → f b = 0) : ∑ b, f b = ∑ a, f (e a) := by
  rw [← Finset.sum_image (fun a _ b _ hab => he hab)]
  refine (Finset.sum_subset (Finset.subset_univ _) fun b _ hb => h b ?_).symm
  rintro ⟨a, rfl⟩
  exact hb (Finset.mem_image_of_mem e (Finset.mem_univ a))

theorem NQ.map {ι R S : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S] (f : R →+* S) {x y : ι}
    {M : Matrix ι ι R} (hM : NQ x y M) : NQ x y (M.map f) := by
  have e : ∀ k l, (M.map f - 1) k l = f ((M - 1) k l) := fun k l => by
    simp only [Matrix.sub_apply, Matrix.map_apply, map_sub, Matrix.one_apply]
    split_ifs <;> simp
  exact ⟨fun k => by rw [e, hM.1 k, map_zero], fun k l h1 h2 h3 => by rw [e, hM.2 k l h1 h2 h3, map_zero]⟩

end Bq

end PositivityTheory.SiegelWeilFormula.Act.C4

end
