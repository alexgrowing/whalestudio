import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsFormsOnRankSpaceNormal
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory.Core.Rk.UpInjWProof

theorem upInjW_of_aForm : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ SF, GlobalTheory.Hk3.IsSF R SF → GlobalTheory.LiftRows.AForm R SF → GlobalTheory.LiftRows.UpInjW R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS hIrr SF hSF hA
  obtain ⟨a, ha, hAF⟩ := hA
  intro i t x hx h0
  obtain ⟨h, -, -, -, hspan, -⟩ := GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt R F hC hS hIrr SF hSF i

  have hpart : ∀ c, GlobalTheory.Hk3.Wcc R SF i c ≤ LinearMap.range (R.thG i t) := by
    intro c y hy
    by_cases hc : GlobalTheory.Hk3.Wcc R SF i c = ⊥
    · rw [hc] at hy
      rw [(Submodule.mem_bot ℂ).1 hy]
      exact Submodule.zero_mem _
    · obtain ⟨z, hz, hS'⟩ := hAF i t c hc
      obtain ⟨B, -, -, hzpos, -⟩ := hz
      have hne : ((a i * z : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (mul_pos (ha i) hzpos).ne'
      refine ⟨((a i * z : ℝ) : ℂ)⁻¹ • LinearMap.adjoint (R.thG i t) y, ?_⟩
      rw [map_smul, hS' y hy, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hxr : x ∈ LinearMap.range (R.thG i t) := by
    have : x ∈ LinearMap.range (GlobalTheory.Hk3.eH R i) := ⟨x, hx⟩
    rw [← hspan] at this
    exact (iSup_le hpart) this
  obtain ⟨v, rfl⟩ := hxr
  have h1 : ⟪R.thG i t v, R.thG i t v⟫_ℂ = 0 := by
    rw [← LinearMap.adjoint_inner_right, h0, inner_zero_right]
  exact inner_self_eq_zero.1 h1

end GlobalTheory.Core.Rk.UpInjWProof
