import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRowHeckeOfOcc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadWMemGoodW
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EigSpanDesc

section Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem iotaR_injective_of (R : RealDat3 D A3 Ks) (hM : R.toRealDat.IsModels) (hU : R.toRealDat.LUnif) (i : Fin D.R.m) :
    Function.Injective (iotaR R i) := by
  have hj : Function.Injective ((R.FW i).j (sg0 D A3.A)) := by
    refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
    by_contra hne
    exact ((hU i _).1 1 (fun _ => v) (linearIndependent_unique_iff.2 hne)).ne_zero 0 hv
  exact (hM.HW i _).1.comp hj

end Gen

theorem iotaR_injective_states : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), LA hL x → ∀ i : Fin (Dof x).R.m, Function.Injective (GlobalTheory.EigSpanDesc.iotaR x.m.z.R i) := by
  intro hL
  refine GlobalTheory.Mem.Top.Bl.StepW.of_all fun K B f T w _ _ _ => ?_
  intro P x _ i
  exact iotaR_injective_of x.m.z.R x.m.z.pins.char.base.models x.m.intersectionNumber_baseChange.prim.unif i

end GlobalTheory.EigSpanDesc
