import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointLiftRangeLeGoodBlockEigenspacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftCarryingOfBaseTupleRowsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalMultiplicityCarriersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGoodProjectorBaseLevelTwistedModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLiftFormsEqGoodFormsStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.LevW

open MeasureTheory IsDedekindDomain NumberField Matrix Polynomial in
open scoped TensorProduct InnerProductSpace in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in

theorem _root_.GlobalTheory.LevW.levW_of_parts : _root_.GlobalTheory.Published.CuspRapidDecay → _root_.GlobalTheory.Hk3.HoweUnram → ∀ {D : _root_.Formalism.BasicNotions.D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : _root_.Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : _root_.Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : _root_.Formalism.IndefR.Links.Face3 D A3) {s : ℕ}, _root_.GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, _root_.Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, _root_.Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → _root_.Formalism.L2.DIV.GoodStable A3.A.X → _root_.GlobalTheory.CuspMult.CuspDecomp D → _root_.GlobalTheory.CuspMult.MultEq R.toRealDat → R.PGEquiv F → (∀ b, (_root_.Formalism.IndefR.Cx.lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmA → _root_.Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → R.toRealDat.LUnif → R.PLevW F := by
  intro hDecay hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hConv hOk hChar hEx hInert hStable hIrr hMult hEquiv hPos hScal hThmA hLift hUnif
  have hCarry := _root_.GlobalTheory.Hk3.carries_of_rows_top hDecay hHowe R F hConv hOk hChar hEx hInert hEquiv hPos
  have hSum := _root_.GlobalTheory.SpanW.iSup_wp3_eq_range_eH R F hOk hChar hEx
    (_root_.GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hDecay _) hStable hIrr hMult hCarry
  have hBlock := _root_.GlobalTheory.Hk3.inBlock_of_cuspRapidDecay hDecay R F hConv hOk hChar hEx hEquiv
  intro j
  rw [_root_.GlobalTheory.WType.range_w0C_type R F hOk hChar hEx hUnif j,
    _root_.GlobalTheory.WgLift.principal_lift_forms_eq_good_forms R F hOk hChar hEx hSum hScal hThmA hLift hBlock j]
  rfl

end GlobalTheory.LevW

end
