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

namespace GlobalTheory

theorem thetaUp_injective_on_carried : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.PThmB → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → ∀ p c, R.Carries p c → ∀ w ∈ R.EEc c, w ≠ 0 → LinearMap.adjoint (R.Th A3.A.μ0) w ≠ 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hB hP p c hc w hw hw0 hadj
  have hwp : w ∈ R.EEp3 p := by
    unfold RealDat3.EEp3
    exact (le_iSup₂ (f := fun (c : Pl D.host.E → List ℤ → ℂ) (_ : R.Carries p c) => R.EEc c) c hc) hw
  have h := hB A3.A.μ0 p w hwp
  rw [LinearMap.comp_apply, hadj, map_zero] at h
  have hpos : 0 < R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.μ0 j p := by
    refine mul_pos hP.1 (Finset.prod_pos fun j _ => ?_)
    unfold RealDat3.lamN
    split_ifs
    · exact hP.2 _ _ _
    · exact one_pos
  have hne : (((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.μ0 j p : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  exact hw0 ((smul_eq_zero.1 h.symm).resolve_left hne)

end GlobalTheory
