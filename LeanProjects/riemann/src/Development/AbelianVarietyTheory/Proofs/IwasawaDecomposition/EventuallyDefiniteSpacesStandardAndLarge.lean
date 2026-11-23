import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoreAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RecAtOfTwoPasses
import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotVstdOfGramOne

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.StdSize

theorem vstd_size_ev : Top.Ev fun K => ∀ X : Stages, K.Over X.B.toPre →
    (∀ i, Formalism.IndefR.FWT.VStd X.toD7 i) ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV := by
  refine GlobalTheory.Mem.Top.V4.TwoPass.ev_mono ?_ GlobalTheory.Mem.HostFrames.hostHyp_frames_ev
  intro K hK X hX
  obtain ⟨-, -, -, -, -, -, hVf, -⟩ := hK X hX
  obtain ⟨hR, -⟩ := GlobalTheory.Mem.HostFrames.val_of_over hX
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hVf i
    rw [GlobalTheory.StdFrameCounterexample.vstd_iff]
    refine ⟨Matrix.ext fun a b => ?_, fun x => ?_⟩
    · rw [HSpace.gram, h1, Matrix.one_apply]
    · rw [h2, Module.Basis.mem_span_iff_repr_mem, Module.Basis.repr_sum_self]
      refine forall_congr' fun a => ?_
      constructor
      · rintro ⟨y, hy⟩
        rw [← hy]; exact y.2
      · intro h
        exact ⟨⟨x a, h⟩, rfl⟩
  · have h4 := hR.2.2.2
    show 8 * X.B.R.f * X.B.R.r + 4 ≤ X.B.R.r + X.B.R.t
    omega

end GlobalTheory.Mem.StdSize
