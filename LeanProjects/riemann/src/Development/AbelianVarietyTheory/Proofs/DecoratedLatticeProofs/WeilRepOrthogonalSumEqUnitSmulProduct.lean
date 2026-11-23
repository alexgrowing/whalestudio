import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionProductsSlicesOrthogonalDecompositiStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOneVariableKeepsThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOneVariablePreservesSqNormOrthogonalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.WeilSumScalar
variable {D : D7} {S A B T : HSp D} (o : OrthDec S A B)

def opA (M : Module.End ℂ (WO A T → ℂ)) : Module.End ℂ (WO S T → ℂ) where
  toFun f x := M (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1
  map_add' f g := by funext x; show M (_ + _) _ = _; rw [map_add]; rfl
  map_smul' c f := by funext x; show M (c • _) _ = _; rw [map_smul]; rfl

def opB (M : Module.End ℂ (WO B T → ℂ)) : Module.End ℂ (WO S T → ℂ) where
  toFun f x := M (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2
  map_add' f g := by funext x; show M (_ + _) _ = _; rw [map_add]; rfl
  map_smul' c f := by funext x; show M (c • _) _ = _; rw [map_smul]; rfl

theorem opA_apply (M : Module.End ℂ (WO A T → ℂ)) (f : WO S T → ℂ) (x : WO S T) :
    opA o M f x = M (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1 := rfl

theorem opB_apply (M : Module.End ℂ (WO B T → ℂ)) (f : WO S T → ℂ) (x : WO S T) :
    opB o M f x = M (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2 := rfl

theorem heisO_sum (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (f : WO S T → ℂ) (u : WO A T) (v : WO B T) :
    heisO ψ S T w f ((o.resS T).symm (u, v)) =
      ψ (symplOH A T u (o.resS T w).1) * ψ (symplOH B T v (o.resS T w).2) *
        f ((o.resS T).symm (u + (o.resS T w).1, v + (o.resS T w).2)) := by
  simp only [heisO]
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddChar.map_add_eq_mul]
  congr 2
  rw [← Prod.mk_add_mk, map_add, AddEquiv.symm_apply_apply]

theorem opB_heisO {ψ : AddChar (AF D.host.F) ℂ} {χ χ' : (AE D)ˣ →* Circle} {om : Om B T}
    (hom : IsWeilDatumO ψ B T χ χ' om) (b : GA D B) (h : GA D T) (w : WO S T) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    opB o (om (b, h)) (heisO ψ S T w f) =
      heisO ψ S T ((o.resS T).symm ((o.resS T w).1, actO B T b h (o.resS T w).2)) (opB o (om (b, h)) f) := by
  funext x
  obtain ⟨⟨u, v⟩, rfl⟩ := (o.resS T).symm.surjective x
  have hg := ((GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition D ψ hom.std S A B T o).2.2.2 f hf).2 (u + (o.resS T w).1)
  have e : (fun v' => heisO ψ S T w f ((o.resS T).symm (u, v'))) =
      ψ (symplOH A T u (o.resS T w).1) •
        heisO ψ B T (o.resS T w).2 (fun v' => f ((o.resS T).symm (u + (o.resS T w).1, v'))) := by
    funext v'
    rw [heisO_sum, Pi.smul_apply, smul_eq_mul, heisO]
    ring
  rw [heisO_sum, opB_apply, opB_apply, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]
  simp only [AddEquiv.apply_symm_apply]
  rw [e, map_smul, hom.om_heis b h _ _ hg, Pi.smul_apply, smul_eq_mul, heisO]
  ring

theorem opA_heisO {ψ : AddChar (AF D.host.F) ℂ} {χ χ' : (AE D)ˣ →* Circle} {om : Om A T}
    (hom : IsWeilDatumO ψ A T χ χ' om) (a : GA D A) (h : GA D T) (w : WO S T) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    opA o (om (a, h)) (heisO ψ S T w f) =
      heisO ψ S T ((o.resS T).symm (actO A T a h (o.resS T w).1, (o.resS T w).2)) (opA o (om (a, h)) f) := by
  funext x
  obtain ⟨⟨u, v⟩, rfl⟩ := (o.resS T).symm.surjective x
  have hg := ((GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition D ψ hom.std S A B T o).2.2.2 f hf).1 (v + (o.resS T w).2)
  have e : (fun u' => heisO ψ S T w f ((o.resS T).symm (u', v))) =
      ψ (symplOH B T v (o.resS T w).2) •
        heisO ψ A T (o.resS T w).1 (fun u' => f ((o.resS T).symm (u', v + (o.resS T w).2))) := by
    funext u'
    rw [heisO_sum, Pi.smul_apply, smul_eq_mul, heisO]
    ring
  rw [heisO_sum, opA_apply, opA_apply, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]
  simp only [AddEquiv.apply_symm_apply]
  rw [e, map_smul, hom.om_heis a h _ _ hg, Pi.smul_apply, smul_eq_mul, heisO]
  ring

def opAB (omA : Om A T) (omB : Om B T) (a : GA D A) (b : GA D B) (h : GA D T) : Module.End ℂ (WO S T → ℂ) :=
  opA o (omA (a, h)) * opB o (omB (b, h))

end GlobalTheory.WeilSumScalar

open GlobalTheory.WeilSumScalar in

theorem GlobalTheory.WeilSumScalar.omS_eq_smul_prod : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (χA χB χT : (AE D)ˣ →* Circle) (omS : Om S T) (omA : Om A T) (omB : Om B T), IsWeilDatumO ψ S T (χA * χB) χT omS → IsWeilDatumO ψ A T χA χT omA → IsWeilDatumO ψ B T χB χT omB → ∀ a b h, ∃ c : Circle, ∀ f, IsThetaFunO ψ S T f → ∀ u v, omS (o.emb (a, b), h) f ((o.resS T).symm (u, v)) = (c : ℂ) * omA (a, h) (fun u' => omB (b, h) (fun v' => f ((o.resS T).symm (u', v'))) v) u := by
  intro D ψ S A B T o χA χB χT omS omA omB hS hA hB a b h
  set N := opAB o omA omB a b h with hN
  set p : GA D S × GA D T := (o.emb (a, b), h) with hp
  have hNapp : ∀ f, N f = opA o (omA (a, h)) (opB o (omB (b, h)) f) := fun f => rfl

  have hNpres : ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (N f) := by
    intro f hf
    have h1 : IsThetaFunO ψ S T (opB o (omB (b, h)) f) := (GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ S A B T o f hf).2 _ _ _ hB (b, h)
    rw [hNapp]
    exact (GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ S A B T o _ h1).1 _ _ _ hA (a, h)

  have hNheis : ∀ w f, IsThetaFunO ψ S T f → N (heisO ψ S T w f) = heisO ψ S T (actO S T (o.emb (a, b)) h w) (N f) := by
    intro w f hf
    have h1 : IsThetaFunO ψ S T (opB o (omB (b, h)) f) := (GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ S A B T o f hf).2 _ _ _ hB (b, h)
    rw [hNapp, hNapp, opB_heisO o hB b h w hf, opA_heisO o hA a h _ h1]
    congr 1
    rw [AddEquiv.apply_symm_apply, ← o.resS_actO T a b h w, AddEquiv.symm_apply_apply]

  have hNunit : ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ →
      ∀ f, IsThetaFunO ψ S T f → ∫⁻ w in 𝓕, ‖N f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ := by
    intro μ 𝓕 hμ h𝓕 f hf
    have h1 : IsThetaFunO ψ S T (opB o (omB (b, h)) f) := (GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ S A B T o f hf).2 _ _ _ hB (b, h)
    rw [hNapp]
    exact ((GlobalTheory.T.weil_operator_one_variable_preserves_sq_norm_orthogonal_sum D ψ S A B T o μ 𝓕 hμ h𝓕 _ h1).1 _ _ _ hA (a, h)).trans
      ((GlobalTheory.T.weil_operator_one_variable_preserves_sq_norm_orthogonal_sum D ψ S A B T o μ 𝓕 hμ h𝓕 f hf).2 _ _ _ hB (b, h))

  have hinv : ∀ g, omS p (omS p⁻¹ g) = g := by
    intro g
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨c, hc, hM⟩ := GlobalTheory.ThetaSchur.schur D ψ hS.std S T (omS p⁻¹ * N)
    (fun f hf => hS.om_pres _ _ (hNpres f hf))
    (fun w f hf => by
      have hpi : p⁻¹ = ((o.emb (a, b))⁻¹, h⁻¹) := rfl
      have hw := GlobalTheory.AdelicLatMove.actO_actO_inv S T (o.emb (a, b))⁻¹ h⁻¹ w
      rw [inv_inv, inv_inv] at hw
      rw [Module.End.mul_apply, Module.End.mul_apply, hNheis w f hf, hpi,
        hS.om_heis _ _ _ _ (hNpres f hf), hw])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, hS.om_unit μ 𝓕 hμ h𝓕 _ _ (hNpres f hf), hNunit μ 𝓕 hμ h𝓕 f hf])
  have hc0 : c ≠ 0 := by intro h0; rw [h0, norm_zero] at hc; exact zero_ne_one hc
  refine ⟨⟨c⁻¹, by simp [Submonoid.unitSphere, hc]⟩, fun f hf u v => ?_⟩
  have e : N f = c • omS p f := by
    have := congrArg (omS p) (hM f hf)
    rwa [Module.End.mul_apply, hinv, map_smul] at this
  have e2 : omS p f = c⁻¹ • N f := by rw [e, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [e2, Pi.smul_apply, smul_eq_mul, hNapp, opA_apply]
  simp only [AddEquiv.apply_symm_apply, opB_apply]

end
