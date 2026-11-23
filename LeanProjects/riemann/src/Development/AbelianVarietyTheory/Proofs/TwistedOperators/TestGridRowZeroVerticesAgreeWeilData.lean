import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

theorem lattice_heq_of_eq_hermitianSpaceWithLattice_mk {D : D7} {x : LSp D} {s : HSp D} {l : Submodule (𝓞 D.host.E) (Fin s.rank → D.host.E)}
    (e : x = ⟨s, l⟩) : HEq l x.lat := by subst e; rfl

theorem nodeAgree_grid0_of_weil_over : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ j, j ≤ D.R.m → NodeAgree (GlobalTheory.Grid.row0 R j) W (.grid 0 j) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc G' W hW j hj
  rcases Nat.lt_or_ge j D.R.m with h | h
  · rw [← nodeY_eq_chainVertexAtRowZero_of_lt R h]
    have e : G'.node (.grid 0 j) = ⟨Yc D j, R.ΛY j⟩ := colY_lt R.toLevCh h
    exact ⟨(congrArg LSp.sp e).symm, lattice_heq_of_eq_hermitianSpaceWithLattice_mk e, (hW.cartY j h).symm, (hW.onbY j h).symm⟩
  · obtain rfl : j = D.R.m := le_antisymm hj h
    rw [← nodeX_eq_chainVertexAtRowZero_top R]
    have e : G'.node (.grid 0 D.R.m) = ⟨D.sp.X', R.ΛX⟩ := colY_m R.toLevCh
    exact ⟨(congrArg LSp.sp e).symm, lattice_heq_of_eq_hermitianSpaceWithLattice_mk e, hW.cartX.symm, hW.onbX.symm⟩

end GlobalTheory.GridJoin
