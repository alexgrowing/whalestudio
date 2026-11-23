import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelRowsEqTypeVectorsOfLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointLiftRangeLeGoodBlockEigenspacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftCarryingOfBaseTupleRowsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelRowsEqTopStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupRowsEigenpartsPrincipalLevelEqTopStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.LevelRowsPrincipal

theorem pLevE_of : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PGEquiv F → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → R.PLevE F := by
  intro hCusp hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hLI hOk hC hEx hJunk hGE hPos hScal hB hRT
  have hBlock : (R.toCx3 F).zs.InBlock := GlobalTheory.T.adjointLift_range_le_goodBlock_eigenspaces hCusp R F hLI hOk hC hEx hGE
  have hCarry : ∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c := GlobalTheory.T.thetaLift_carrying_of_base_tuple_rows hCusp hHowe R F hLI hOk hC hEx hJunk hGE hPos
  have hSpan : (⨆ p, R.EEp3 p) = ⊤ :=
    GlobalTheory.T.iSup_eEp3_eq_whole_space_of_weakCharacterisation R F hC hEx (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCusp R.toRealDat) hCarry
  have hTop := GlobalTheory.T.EEg3_eq_univ_of_weakCharacterisation R F hOk hC hSpan hScal hB hRT hBlock
  obtain ⟨h0, h1⟩ := GlobalTheory.LevelRows3.eel_eq_typeSp3 R F hC
  refine ⟨?_, ?_⟩
  · show (R.toCx3 F).EEl false = _ ⊓ _
    rw [hTop, top_inf_eq, h0]
  · show (R.toCx3 F).EEl true = _ ⊓ _
    rw [hTop, top_inf_eq, h1]

end GlobalTheory.LevelRowsPrincipal
