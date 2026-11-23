import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowSideDefinitionBothLevelsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndefiniteSideRowLatticeAdoptedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IpMSmulMeasureSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MajAtSmulRightOf
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3

theorem rowLat_ties : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HLatTie (RowSide.sharp D).RR (A3.indefDown (s1Of R F)).RR (A3.indefDown (s1Of R F)).XE Z.eRR ∧ HLatTie X0.s.RR (A3.indefDown (s0Of R F)).RR (A3.indefDown (s0Of R F)).XE Z.eRR0 := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH
  have hD := GlobalTheory.T.rowSide_definition_both_levels hC D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  have hok : A3.A.fam.Ok 1 := hH.ok.ok2
  have hmu1 : ∀ w, D.what₂.muAt w = Y.tup ((A3.indefDown (s1Of R F)).μ (D.plEq w)) := fun w => Y.muAt w
  have hmu0 : ∀ w, D.what₂.muAt w = Y.tup ((A3.indefDown (s0Of R F)).μ (D.plEq w)) := fun w => Y.muAt w
  have h1 := GlobalTheory.T.indefinite_side_row_lattice_adopted D G Pl0 T D.R.m A3.A 1 D.what₂.EE (RowSide.sharp D) F.P1 F.ψ1 (A3.fam3.toSub2 (zsOf R F))
    (A3.indefDown (s1Of R F)) Y.tup Z.eRR Y.jA hok hD.1 Z.rr hmu1 Y.stable
  have h0 := GlobalTheory.T.indefinite_side_row_lattice_adopted D G Pl0 T D.R.m A3.A 1 D.what₂.EE0 X0.s F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F))
    (A3.indefDown (s0Of R F)) Y.tup Z.eRR0 Y.jA0 hok hD.2 Z.rr0 hmu0 Y.stable0
  have m1 := GlobalTheory.Mem.R3.MetSharp.majAt_rows_fixed D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  have m0 := GlobalTheory.Mem.R3.MetBase.metric_base_fixed D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  refine ⟨⟨h1, fun v x y => ?_⟩, ⟨h0, fun v x y => ?_⟩⟩
  · by_cases hv : v = A3.A.v0
    · subst hv; exact m1 x y
    · exact Z.met v hv x y
  · by_cases hv : v = A3.A.v0
    · subst hv; exact m0 x y
    · exact Z.met0 v hv x y

end GlobalTheory.Mem.R3
