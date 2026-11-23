import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMulConjSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryComponentAtPlaceLawsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorStableUnitaryGroupsAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorPureTensorPlaceByPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorInnerProductEqFinprodLocalInnerProductStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor.OmPure

theorem ipO_om_left {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : OmT S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕)
    (g : GA D S) (h : GA D T) {f f' : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') :
    ipO μ 𝓕 (om (g, h) f) f' = ipO μ 𝓕 f (om (g⁻¹, h⁻¹) f') := by
  have e : om (g, h) (om (g⁻¹, h⁻¹) f') = f' := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]
  have k : ipO μ 𝓕 (om (g, h) f) (om (g, h) (om (g⁻¹, h⁻¹) f')) = ipO μ 𝓕 f (om (g⁻¹, h⁻¹) f') :=
    GlobalTheory.WeilInner.om_inner D ψ S T χS χT om hW μ 𝓕 hμ (g, h) f _ hf (hW.om_pres _ _ hf')
  rwa [e] at k

theorem isPure_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (g : GA D S) (h : GA D T), {p : Place D | om (gAt S p g, gAt T p h) f₀ ≠ f₀}.Finite → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => om (gAt S p g⁻¹, gAt T p h⁻¹) f₀) (om (g⁻¹, h⁻¹) f₀) → ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => om (gAt S p g, gAt T p h) (x p)) (om (g, h) f) := by
  intro D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ g h hfin hinv x f hx
  have hpres := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hW.std S T).1
  have h0 := base_theta hB
  refine ⟨⟨fun p => GlobalTheory.T.localFactor_stable_unitaryGroupsAtPlace D ψ θ S T χS χT om sS sT ΛS ΛT hW (base_inf hB) p _ (hx.1.1 p) g h, ?_⟩,
    hW.om_pres _ _ hx.2.1, fun w => ?_⟩
  · refine (hfin.union hx.1.2).subset fun p hp => ?_
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
    exact hp (by simp only [hc.2, hc.1])
  · have hy := GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ _ _ hinv (actO S T g⁻¹ h⁻¹ w)
    have hp := GlobalTheory.T.pureTensor_innerProduct_eq_finprod_localInnerProducts D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ _ _ _ _ hx hy
    have e : (fun p => ipO μ 𝓕 (om (gAt S p g, gAt T p h) (x p)) (heisO ψ S T (wAt p w) f₀)) =
        fun p => ipO μ 𝓕 (x p) (heisO ψ S T (wAt p (actO S T g⁻¹ h⁻¹ w)) (om (gAt S p g⁻¹, gAt T p h⁻¹) f₀)) := by
      funext p
      rw [ipO_om_left hW hμ _ _ (hx.1.1 p).1 (hpres _ _ h0), ← gAt_inv, ← gAt_inv, hW.om_heis _ _ _ _ h0,
        ((GlobalTheory.T.adelicUnitaryComponentAtPlace_laws D).2 S T p g⁻¹ h⁻¹ w).2]
    refine ⟨by rw [e]; exact hp.1, ?_⟩
    rw [e, ipO_om_left hW hμ _ _ hx.2.1 (hpres _ _ h0), hW.om_heis _ _ _ _ h0]
    exact hp.2

end GlobalTheory.PlaceTensor.OmPure
