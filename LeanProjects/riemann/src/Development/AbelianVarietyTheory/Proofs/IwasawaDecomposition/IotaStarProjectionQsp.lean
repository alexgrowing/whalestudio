import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.HilbertRowConditions.KaTiedIffKapDef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowSideDefinitionBothLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGoodProjectorEqRangeGoodCoordinates
import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3

theorem iota_starProjection_Qsp (D : D7) (μ : D.what₂.Tup) (F : D.what₂.Amb μ) (hF : F ∈ D.what₂.V0 μ) :
    D.what₂.iota μ ((D.what₂.Qsp μ).starProjection F) = D.what₂.iota μ F := by
  set a := (D.what₂.Usp μ).starProjection F with ha
  have haU : a ∈ D.what₂.Usp μ := Submodule.starProjection_apply_mem _ _
  have hb : F - a ∈ D.what₂.Qsp μ := ⟨Submodule.sub_mem _ hF haU.1, Submodule.sub_starProjection_mem_orthogonal F⟩
  have haQ : (D.what₂.Qsp μ).starProjection a = 0 := by
    rw [Submodule.starProjection_apply_eq_zero_iff]
    exact (Submodule.mem_orthogonal _ _).2 fun q hq => Submodule.inner_left_of_mem_orthogonal haU hq.2
  have e : (D.what₂.Qsp μ).starProjection F = F - a := by
    have h := map_add (D.what₂.Qsp μ).starProjection a (F - a)
    rw [add_sub_cancel, haQ, zero_add, Submodule.starProjection_eq_self_iff.2 hb] at h
    exact h
  rw [e, map_sub, LinearMap.mem_ker.1 haU.2, sub_zero]

theorem zeTied_of_read : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (C : ReadC R F X0 Y), Pins R F cG → Holds R F → D.BuRational → ZetaCompatible D := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z C hP hH hB u μ c hfac hnz
  refine Y.ze u μ c hfac hnz ?_
  by_cases hU : Used0 D μ
  swap
  · exfalso
    obtain ⟨φ, x, hx, hne⟩ := hnz
    apply hne
    rw [hfac φ x hx, Y.junk μ hU, LinearMap.zero_apply, (D.Bu_linR u φ).map_zero, mul_zero]
  obtain ⟨t, rfl⟩ : ∃ t, Y.tup t = μ := ⟨Y.tupT μ, Y.tupTie μ hU⟩
  have hRS := (GlobalTheory.T.rowSide_definition_both_levels hC D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH).1
  have hFo := Y.formsA t
  have hR : LinearMap.range (rE D A3.A F.P1 F.ψ1 t).mulVecLin = LinearMap.range (rV0 D A3.A F.P1 F.ψ1 t).mulVecLin :=
    GlobalTheory.range_lvlOp_idemOf_eq_range_lvlPr_mul_V0E _ _ _ _ _
  have hmem : ∀ f, Y.jA t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f) ∈ D.what₂.V0 (Y.tup t) := by
    intro f
    have h1 : (rV0 D A3.A F.P1 F.ψ1 t).mulVec f ∈ LinearMap.range (rE D A3.A F.P1 F.ψ1 t).mulVecLin := by
      rw [hR]; exact ⟨f, rfl⟩
    obtain ⟨g, hg⟩ := h1
    refine ⟨Y.jA t g, ?_⟩
    exact (hFo.op_eq g).trans (congrArg (Y.jA t) hg)
  have hQ : ∃ x f, D.what₂.Bu u (D.jN u (C.eNu u x))
      (D.what₂.iota (Y.tup t) (Y.jA t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f))) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨φ0, F0, hF0, hne⟩ := hnz
    apply hne
    rw [hfac φ0 F0 hF0, iota_starProjection_Qsp D _ F0 hF0]
    have h1 : ∀ x, ∀ F ∈ D.what₂.V0 (Y.tup t), D.what₂.Bu u (D.jN u (C.eNu u x)) (D.what₂.iota (Y.tup t) F) = 0 := by
      intro x F hF
      obtain ⟨y, rfl⟩ := hF
      let L : D.what₂.Amb (Y.tup t) →ₗ[ℂ] ℂ :=
        ((D.Bu_linR u (D.jN u (C.eNu u x))).mk' _) ∘ₗ D.what₂.iota (Y.tup t) ∘ₗ D.what₂.eOp (Y.tup t)
      have hL : L = 0 := by
        refine LinearMap.ext_on_range hFo.span fun i => ?_
        have h2 : (rE D A3.A F.P1 F.ψ1 t).mulVec (Pi.single i 1) ∈ LinearMap.range (rV0 D A3.A F.P1 F.ψ1 t).mulVecLin := by
          rw [← hR]; exact ⟨_, rfl⟩
        obtain ⟨f, hf⟩ := h2
        have e1 : D.what₂.eOp (Y.tup t) (Y.jA t (Pi.single i 1)) = Y.jA t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f) :=
          (hFo.op_eq _).trans (congrArg (Y.jA t) hf.symm)
        show D.what₂.Bu u (D.jN u (C.eNu u x)) (D.what₂.iota (Y.tup t) (D.what₂.eOp (Y.tup t) (Y.jA t (Pi.single i 1)))) = 0
        rw [e1]
        exact hcon x f
      exact LinearMap.congr_fun hL y
    let M : D.what₂.Mu u →ₗ[ℂ] ℂ := (D.Bu_linL u (D.what₂.iota (Y.tup t) F0)).mk' _
    have hM : M = 0 := by
      refine LinearMap.ext_on_range (D.jN_basis u).2 fun i => ?_
      have h3 := h1 ((C.eNu u).symm ((D.div.Nu u).b i)) F0 hF0
      rw [LinearEquiv.apply_symm_apply] at h3
      exact h3
    rw [show D.what₂.Bu u φ0 (D.what₂.iota (Y.tup t) F0) = 0 from LinearMap.congr_fun hM φ0, mul_zero]
  obtain ⟨x, f, hx⟩ := hQ
  have hpt := C.pt u t x f
  have hf := hfac (D.jN u (C.eNu u x)) _ (hmem f)
  rw [iota_starProjection_Qsp D _ _ (hmem f)] at hf
  obtain ⟨w, hw⟩ : ∃ w : D.div.RR.V,
      D.what₂.iota (Y.tup t) (Y.jA t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f)) = D.jEE w :=
    ⟨_, by rw [← Formalism.MainNotions.AbsolutelyIrreducibleSpan.sharp_iota]; exact hRS.iota t f⟩
  rw [hw, hB] at hx hf
  refine ⟨(F.Dc (R.toCx3 F).zs).Pt (C.wU u) t x f / D.div.Bk u (C.eNu u x) w, ?_⟩
  rw [map_div₀, hpt, hf]
  exact mul_div_cancel_right₀ c hx

end GlobalTheory.Mem.R3
