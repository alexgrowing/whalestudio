import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanKilledUnionAverages
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisOAdd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_annihilated_union_class_averages : ∀ {G M : Type} [Group G] [Fintype G] [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (π : G → Module.End ℂ M), (∀ g, ∀ v ∈ S, π g v ∈ S) → (∀ v ∈ S, π 1 v = v) → (∀ g h, ∀ v ∈ S, π (g * h) v = π h (π g v)) → ∀ (C : Set (G → ℂ)), (∀ c ∈ C, ∀ x : G, (fun g => c (x * g * x⁻¹)) ∈ C) → ∀ v ∈ S, v ∈ Submodule.span ℂ ({w | w ∈ S ∧ ∀ c ∈ C, ∑ g, c g • π g w = 0} ∪ {u | ∃ c ∈ C, ∃ w ∈ S, u = ∑ g, c g • π g w}) := by
  first | exact @GlobalTheory.mem_span_killed_union_averages | exact GlobalTheory.mem_span_killed_union_averages | (intros; apply GlobalTheory.mem_span_killed_union_averages <;> assumption)
