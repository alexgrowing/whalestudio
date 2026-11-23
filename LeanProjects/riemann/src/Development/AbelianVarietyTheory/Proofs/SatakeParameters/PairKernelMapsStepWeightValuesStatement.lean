import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairKernelMapsStepWeightValues
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsAre
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_kernel_maps_step_weight_values : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (O : GL3Theta.LiftObj D C) (i : ℕ), i < D.R.m → UnfIs O i (nuT D u i) → ∀ (c : C.cls i) (c' : C.cls (i + 1)) f, IsVal (O.frm i) (lamTG M i) (RingHom.id ℂ) f → IsVal (O.frm (i + 1)) (lamTG M (i + 1)) (RingHom.id ℂ) (C.Kmap i c c' f) := by
  first | exact @GlobalTheory.KerJ.Kmap_isVal | exact GlobalTheory.KerJ.Kmap_isVal | (intros; apply GlobalTheory.KerJ.Kmap_isVal <;> assumption)
