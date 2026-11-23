import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelTypeEigenfunctionOfLiftableElement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.LevelRows3

theorem eel_eq_typeSp3 : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → (R.toCx3 F).EEl false = typeSp3 A3 (R.toCx3 F) (R.gEx F) F.P0 F.ψ0 ∧ (R.toCx3 F).EEl true = typeSp3 A3 (R.toCx3 F) (R.gEx F) F.P1 F.ψ1 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F h
  have key : GlobalTheory.IndefiniteRowSideFullHecke.TypeCharacterLevelRows.RowsOfLevel R.toRealDat F.lv2 :=
    GlobalTheory.LevelRows.rowsOfLevel_of_models R.toRealDat F.lv2 h.base.models.HE h.base.models.gE
  have aux : ∀ (b : Bool) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ),
      (∀ x : R.HE.H, R.HE.e x ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 b) ↔
        ∀ g : P, R.gE (g : G) x = D.what₂.embLL ((ψ g : D.what₂.LLˣ) : D.what₂.LL) • x) →
      (R.toCx3 F).EEl b = typeSp3 A3 (R.toCx3 F) (R.gEx F) P ψ := by
    intro b P ψ hx
    ext x
    simp only [typeSp3, Submodule.mem_iInf, LinearMap.mem_ker]
    refine Iff.trans (hx x) (forall_congr' fun g => ?_)
    rw [LinearMap.sub_apply, sub_eq_zero]
    rw [LinearMap.smul_apply, LinearMap.id_apply]
    have e : cj (twAt D.what₂.embLL A3.A.v0) (A3.A.v0.embedding ((ψ g : D.what₂.LLˣ) : D.what₂.LL)) =
        D.what₂.embLL ((ψ g : D.what₂.LLˣ) : D.what₂.LL) := by
      simp only [R.emb0, cj_cj]
    have e' : A3.A.fam.v0.embedding ((ψ g : D.what₂.LLˣ) : D.what₂.LL) • x =
        Tw.mk (twAt D.what₂.embLL A3.A.v0) (D.what₂.embLL ((ψ g : D.what₂.LLˣ) : D.what₂.LL) • Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) x) := by
      rw [← e]
      rfl
    rw [e']
    exact Iff.rfl
  exact ⟨aux false _ _ (key false), aux true _ _ (key true)⟩

end GlobalTheory.LevelRows3

end
