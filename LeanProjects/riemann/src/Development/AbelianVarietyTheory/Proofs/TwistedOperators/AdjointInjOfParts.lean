import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsFormsOnRankSpaceNormal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdjointInjectiveOfParts

theorem adjoint_inj_of_parts {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H'] (T : H' →ₗ[ℂ] H) {ι : Type*}
    (P : ι → Submodule ℂ H) (s : ι → ℂ) (hs : ∀ c, s c ≠ 0)
    (hP : ∀ c, ∀ x ∈ P c, T (LinearMap.adjoint T x) = s c • x) {x : H} (hx : x ∈ ⨆ c, P c)
    (h0 : LinearMap.adjoint T x = 0) : x = 0 := by
  have hle : (⨆ c, P c) ≤ LinearMap.range T := by
    refine iSup_le fun c y hy => ⟨LinearMap.adjoint T ((s c)⁻¹ • y), ?_⟩
    rw [hP c _ ((P c).smul_mem _ hy), smul_smul, mul_inv_cancel₀ (hs c), one_smul]
  obtain ⟨w, rfl⟩ := hle hx
  have h1 : ⟪T w, T w⟫_ℂ = 0 := by
    rw [← LinearMap.adjoint_inner_right, h0, inner_zero_right]
  exact inner_self_eq_zero.1 h1

end GlobalTheory.AdjointInjectiveOfParts

open GlobalTheory.Hk3 in

theorem GlobalTheory.LiftRows.upInj_of_scal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ SF, GlobalTheory.Hk3.IsSF R SF → Scal R SF → UpInj R ∧ UpInjW R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS hI SF hSF hScal
  obtain ⟨lam, κ, hκ, hl, hW, hE⟩ := hScal
  constructor
  · intro t
    refine (injective_iff_map_eq_zero _).2 fun x h0 => ?_
    obtain ⟨h, -, -, hsp, -⟩ := GlobalTheory.Hk3.OpsRows.exists_opsE R F hC hS SF hSF
    refine GlobalTheory.AdjointInjectiveOfParts.adjoint_inj_of_parts (R.Th t) (fun c => EEc R SF c)
      (fun c => ((κ * ∏ i, lam i t c : ℝ) : ℂ))
      (fun c => Complex.ofReal_ne_zero.2 (mul_pos hκ (Finset.prod_pos fun i _ => hl i t c)).ne')
      (fun c x hx => hE t c x hx) ?_ h0
    rw [hsp]; trivial
  · intro i t x hx h0
    obtain ⟨h, -, -, -, hsp, -⟩ := GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt R F hC hS hI SF hSF i
    refine GlobalTheory.AdjointInjectiveOfParts.adjoint_inj_of_parts (R.thG i t) (fun c => Wcc R SF i c)
      (fun c => ((lam i t c : ℝ) : ℂ)) (fun c => Complex.ofReal_ne_zero.2 (hl i t c).ne')
      (fun c x hx => hW i t c x hx) ?_ h0
    rw [hsp]; exact ⟨x, hx⟩
