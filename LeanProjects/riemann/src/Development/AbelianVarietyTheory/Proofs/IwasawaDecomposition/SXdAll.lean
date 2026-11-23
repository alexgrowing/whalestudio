import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLevelTypeFormsOfUniversalCoeffReading

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up

set_option maxHeartbeats 2000000 in

theorem sXd_all : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, SXd hL := by
  intro hL
  refine StepW.of_all fun K B f T w _ _ _ P x l => ?_
  have hU : x.m.z.R.toRealDat.LUnif := x.m.intersectionNumber_baseChange.prim.unif
  have hW : x.m.z.R.toRealDat.models_HW := x.m.z.pins.char.base.models.HW
  have H := (GlobalTheory.ExportType.type_of_exportTie l.b.ser.ex hU hW).2.2.2
  exact ⟨⟨fun _ j _ => {_d | j ∈ Finset.Icc 1 (Dof x).R.m}, fun i j b a ha u =>
    sub_eq_zero.1 (LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 (H i j ha b a) u))⟩,
    fun i j b h1 h2 => Set.eq_univ_of_forall fun _ => Finset.mem_Icc.2 ⟨h1, h2⟩⟩

end GlobalTheory.HeightCounting.Up
