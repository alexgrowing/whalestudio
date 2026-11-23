import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom
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

noncomputable section

namespace GlobalTheory.LevelRange

theorem range_w0C_eq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.LUnif → ∀ b i, LinearMap.range ((R.toCx3 F).w0C b i) = Tw.sub (twAt D.what₂.embLL A3.A.v0) ((R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 b (sg0 D A3.A))).comap (R.HW i (sg0 D A3.A)).e) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hU b i
  have hL := GlobalTheory.LevelForms.levelW_of_irr R.toRealDat F.lv2 hOk.ok2.irr hU hC.base.models.HW
  rw [← hL b i (sg0 D A3.A)]
  have h3 : Submodule.span ℂ (Set.range fun k => (⟨R.toRealDat.bC F.lv2 b i (sg0 D A3.A) k, Submodule.subset_span ⟨k, rfl⟩⟩ :
      R.toRealDat.WS F.lv2 b i (sg0 D A3.A))) = ⊤ := Submodule.span_range_subtype_eq_top_iff _ _ |>.2 rfl
  have h4 : LinearMap.range ((R.toCx3 F).wC b i A3.A.v0) = ⊤ :=
    (Fintype.range_linearCombination _ _).trans (Tw.span_top (E := R.toRealDat.WS F.lv2 b i (sg0 D A3.A)) _ h3)
  have hc : ((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (RealDat.nP_pos (F := F.lv2) b)).ne'
  refine (LinearMap.range_comp_of_range_eq_top _ h4).trans (le_antisymm ?_ fun x hx => ?_)
  · rintro _ ⟨y, rfl⟩
    exact (R.toRealDat.WS F.lv2 b i (sg0 D A3.A)).smul_mem _ (Tw.out y : R.toRealDat.WS F.lv2 b i (sg0 D A3.A)).2
  · let y : (R.HW i (sg0 D A3.A)).H := x
    exact ⟨(⟨((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ)⁻¹ • y, (R.toRealDat.WS F.lv2 b i (sg0 D A3.A)).smul_mem _ hx⟩ :
      R.toRealDat.WS F.lv2 b i (sg0 D A3.A)), smul_inv_smul₀ hc y⟩

end GlobalTheory.LevelRange
