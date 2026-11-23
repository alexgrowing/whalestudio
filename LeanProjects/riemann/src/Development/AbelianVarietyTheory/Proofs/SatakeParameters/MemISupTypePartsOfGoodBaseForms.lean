import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwParts

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
  [Algebra Ks D.what₂.LL]

theorem mk_bC_mem_range (R : RealDat3 D A3 Ks) (F : Face3 D A3) (j : Fin D.R.m)
    (k : Fin ((R.toCx3 F).dW false j)) :
    Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.toRealDat.bC F.lv2 false j (sg0 D A3.A) k) ∈
      LinearMap.range ((R.toCx3 F).w0C false j) := by
  have hpos : (0 : ℝ) < Real.sqrt (RealDat.nP F.lv2 false) := Real.sqrt_pos.mpr (RealDat.nP_pos (F := F.lv2) false)
  refine ⟨Pi.single k ((((Real.sqrt (RealDat.nP F.lv2 false))⁻¹ : ℝ) : ℂ)), ?_⟩
  simp only [CxData.w0C, CxData.wC, lin, LinearMap.comp_apply, Fintype.linearCombination_apply_single]
  rw [LinearMap.map_smul]
  show Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW j (sg0 D A3.A)).H) (_ • _) = Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW j (sg0 D A3.A)).H) (Tw.mk _ _)
  erw [Tw.out_smul, cj_ofReal]
  show ((((Real.sqrt (RealDat.nP F.lv2 false))⁻¹ : ℝ) : ℂ)) • ((((Real.sqrt (RealDat.nP F.lv2 false)) : ℝ) : ℂ) • R.toRealDat.bC F.lv2 false j (sg0 D A3.A) k) = R.toRealDat.bC F.lv2 false j (sg0 D A3.A) k
  rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one, one_smul]

end GlobalTheory.TwParts

open GlobalTheory.TwParts in
theorem GlobalTheory.TwParts.mem_iSup_Wp3_of_mem_WS : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), (R.toCx3 F).PartsW false → ∀ j (w : (R.HW j (sg0 D A3.A)).H), w ∈ R.toRealDat.WS F.lv2 false j (sg0 D A3.A) → w ∈ ⨆ p, R.Wp3 j p := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hP j w hw
  obtain ⟨-, hsup⟩ := hP j
  refine Submodule.span_le.mpr ?_ hw
  rintro _ ⟨k, rfl⟩
  have hk := mk_bC_mem_range R F j k
  rw [← hsup] at hk
  have hk' : Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.toRealDat.bC F.lv2 false j (sg0 D A3.A) k) ∈
      ⨆ p, (R.toCx3 F).Wp j p := by
    have hle : (⨆ p, (R.toCx3 F).Wp j p ⊓ LinearMap.range ((R.toCx3 F).w0C false j)) ≤ ⨆ p, (R.toCx3 F).Wp j p :=
      iSup_mono fun p => inf_le_left
    exact hle hk
  refine Submodule.iSup_induction (fun p => (R.toCx3 F).Wp j p) (motive := fun x => Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW j (sg0 D A3.A)).H) x ∈ ⨆ p, R.Wp3 j p) hk' ?_ ?_ ?_
  · intro p x hx
    exact Submodule.mem_iSup_of_mem p hx
  · exact Submodule.zero_mem _
  · intro x y hx hy
    exact Submodule.add_mem _ hx hy
