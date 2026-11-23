import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.MemRatVIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp PositivityTheory.SiegelWeilFormula.kfour
namespace PositivityTheory.SiegelWeilFormula.Afc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem mem_ratV_iff_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u : Fin L.n → AE F E) :
    u ∈ L.ratV ↔ ∃ v : Fin L.n → E, u = GlobalTheory.ThK.incV F v := by
  constructor
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem x hx => obtain ⟨v, rfl⟩ := hx; exact ⟨v, rfl⟩
    | zero => exact ⟨0, by funext i; simp [GlobalTheory.ThK.incV]⟩
    | add x y _ _ hx hy =>
      obtain ⟨v, rfl⟩ := hx
      obtain ⟨v', rfl⟩ := hy
      exact ⟨v + v', by funext i; simp [GlobalTheory.ThK.incV]⟩
    | neg x _ hx =>
      obtain ⟨v, rfl⟩ := hx
      exact ⟨-v, by funext i; simp [GlobalTheory.ThK.incV]⟩
  · rintro ⟨v, rfl⟩
    exact AddSubgroup.subset_closure ⟨v, rfl⟩
end PositivityTheory.SiegelWeilFormula.Afc
end
end
