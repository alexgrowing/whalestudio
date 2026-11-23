import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsPartsDistinctTypesOrthogonalStatement
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

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Div.inner_EEp3_eq_zero_of_ne : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → ∀ p q, p ≠ q → ∀ e ∈ R.EEp3 p, ∀ e' ∈ R.EEp3 q, ⟪e, e'⟫_ℂ = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hH hPos hB p q hpq e he e' he'

  have hmap : ∀ r, (R.EEp3 r).map (LinearMap.adjoint (R.Th A3.A.μ0)) ≤
      Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum r.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)) := by
    intro r
    rw [Submodule.map_le_iff_le_comap]
    exact iSup₂_le fun c hc => Submodule.map_le_iff_le_comap.1 hc.2
  have hx : LinearMap.adjoint (R.Th A3.A.μ0) e ∈ Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)) :=
    hmap p (Submodule.mem_map_of_mem he)
  have hy : LinearMap.adjoint (R.Th A3.A.μ0) e' ∈ Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum q.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)) :=
    hmap q (Submodule.mem_map_of_mem he')
  have h0 := GlobalTheory.T.complex_points_parts_distinct_types_orthogonal R F hOk hC hH p q hpq _ hx _ hy
  have hk := hB A3.A.μ0 p e he
  rw [LinearMap.comp_apply] at hk
  have hin : ⟪R.Th A3.A.μ0 (LinearMap.adjoint (R.Th A3.A.μ0) e), e'⟫_ℂ = 0 := by
    rw [← LinearMap.adjoint_inner_right]; exact h0
  rw [hk, inner_smul_left] at hin
  have ha : (0 : ℝ) < R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.μ0 j p := by
    rw [RealDat3.prod_lamN]
    exact mul_pos hPos.1 (Finset.prod_pos fun j _ => hPos.2 j _ _)
  rcases mul_eq_zero.1 hin with h | h
  · exfalso
    rw [Complex.conj_ofReal] at h
    exact ha.ne' (by exact_mod_cast h)
  · exact h
