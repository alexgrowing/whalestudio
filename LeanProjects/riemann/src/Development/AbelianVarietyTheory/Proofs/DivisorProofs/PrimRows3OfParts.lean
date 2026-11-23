import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointLiftRangeLeGoodBlockEigenspacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelGoodFormsDimsAgreePartwiseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelRowsEqPrincipalRowsOfTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelWFormsEqPrincipalFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelRowsOrthogonalSumOfPartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelWOrthogonalSumOfPartsStatement
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory

theorem primRows3_of_parts : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PHecke F → R.PGUnit F → R.PGEquiv F → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false → (∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → R.PPos → R.PrincipalLevelBijective F → R.PThmB → R.toRealDat.LUnif → (R.toCx3 F).MLat false → R.PThmA → (R.toCx3 F).GalD F.cr false → PrimRows3 R F := by
  intro hCusp hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hLift hOk hC hEx hInert hGS hCD hME hR hL hHk hGU hGE hRT hLT hLTB hOnto hPos hPP hH2 hB hU hM hA hGal
  have hPP' : 0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0 := ⟨hPP.1, fun i t p => hPP.2 i t p _⟩
  exact
    { heckeR := hR
      heckeL := hL
      hecke := hHk
      gUnit := hGU
      gEquiv := hGE
      block := GlobalTheory.T.adjointLift_range_le_goodBlock_eigenspaces hCusp R F hLift hOk hC hEx hGE
      rowTest := hRT
      liftTest := hLT
      liftTestB := hLTB
      liftOnto := hOnto
      pos := hPos
      posScal := hPP
      levE := GlobalTheory.T.levelRows_eq_principalRows_of_type hCusp hHowe R F hLift hOk hC hEx hInert hGE hPos hPP' hB hRT
      h2P := hH2
      thmB := hB
      sumE := GlobalTheory.T.levelRows_orthogonalSum_of_parts hCusp hHowe R F hLift hOk hC hEx hInert hR hGE hPos hPP' hB
      unif := hU
      mLat := hM
      levW := GlobalTheory.T.baseLevelW_forms_eq_principalForms hCusp hHowe R F hLift hOk hC hEx hInert hGS hCD hME hGE hPos hPP' hA hLT hU
      thmA := hA
      sumW := GlobalTheory.T.baseLevelW_orthogonalSum_of_parts hCusp hHowe R F hLift hOk hC hEx hInert hGS hCD hME hR hGE hPos hPP' hB hU
      scalConj := hGal
      dimParts := GlobalTheory.T.baseLevel_goodForms_dims_agree_partwise hCusp R F hOk hC hEx hGS hCD hME hU }

end GlobalTheory
