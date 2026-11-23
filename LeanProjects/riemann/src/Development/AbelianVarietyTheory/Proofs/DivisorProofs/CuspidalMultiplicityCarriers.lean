import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsFormsOnRankSpaceNormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigensystemGoodFormsThetaTargetOccursOnRowsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
namespace GlobalTheory.SpanW

theorem iSup_wp3_eq_range_eH : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c) → ∀ i, (⨆ p, R.Wp3 i p) = LinearMap.range (eH R.toRealDat i) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hW hEx hS hGS hCD hME hcar i
  obtain ⟨hCore, hSF, hE, hWc⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW hEx
  have hOk2 : A3.A.fam.Ok s := hOk.ok2
  have hirr : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk2.irr
  obtain ⟨h, -, -, -, hsum, -⟩ := GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 hCore hS hirr R.SF hSF i
  rw [← hsum]
  apply le_antisymm
  · refine iSup_le fun p => iSup₂_le fun c _ => ?_
    rw [hWc]
    exact le_iSup (fun c => Wcc R.toRealDat R.SF i c) c
  · refine iSup_le fun c => ?_
    by_cases h0 : Wcc R.toRealDat R.SF i c = ⊥
    · rw [h0]; exact bot_le
    · have hE0 : EEc R.toRealDat R.SF c ≠ ⊥ :=
        GlobalTheory.T.eigensystem_goodForms_thetaTarget_occurs_on_rows R.toRealDat F.lv2 hOk2 hCore hS hGS hCD hME R.SF hSF i c h0
      obtain ⟨p, hp⟩ := hcar c (by rw [hE]; exact hE0)
      rw [← hWc]
      exact le_trans (le_iSup₂ (f := fun c (_ : R.Carries p c) => R.Wc' i c) c hp) (le_iSup (fun p => R.Wp3 i p) p)

end GlobalTheory.SpanW
