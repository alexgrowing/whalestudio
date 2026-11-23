import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ActsLinOfSplitLin
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IsThetaFunOPull
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsTheta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PullModelLaw

theorem om_apply_eq_smul_pull : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ → (∀ u ∈ latAll S T ΛS ΛT, (IsHalf e u ∨ IsHalf (cA D e) u) → heisO ψ S T u f₀ = f₀) → ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latAll S T ΛS ΛT) 1 f₀ Tm → ∀ (p : GA D S × GA D T) (κ : ℂ), (∀ Φ, IsSBHalf e (latAll S T ΛS ΛT) Φ → IsSBHalf e (latAll S T ΛS ΛT) (actPull p Φ)) → om p f₀ = κ • Tm (actPull p (halfInd e (latAll S T ΛS ΛT))) → ∀ Φ, IsSBHalf e (latAll S T ΛS ΛT) Φ → om p (Tm Φ) = κ • Tm (actPull p Φ) := by
  intro D ψ S T χS χT om hW ΛS ΛT hsS hsT Q e he f₀ hf₀ _ Tm hTm p κ hsb hκ Φ hΦ
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hthm : ∀ Ψ, IsSBHalf e (latAll S T ΛS ΛT) Ψ → IsThetaFunO ψ S T (Tm Ψ) :=
    GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S T ΛS ΛT hsS hsT e hee hinf f₀ hf₀ Tm hTm
  have hqp : ((p.1⁻¹, p.2⁻¹) : GA D S × GA D T) * p = 1 := Prod.ext (by simp) (by simp)
  have hpq : p * ((p.1⁻¹, p.2⁻¹) : GA D S × GA D T) = 1 := Prod.ext (by simp) (by simp)
  have hback : ∀ x : WO S T, actO S T p.1⁻¹ p.2⁻¹ (actO S T p.1 p.2 x) = x := fun x => by
    rw [actO_actO, inv_mul_cancel, inv_mul_cancel, actO_one]
  have hsmul : ∀ (w : WO S T) (c : ℂ) (F : WO S T → ℂ), c • heisO ψ S T w F = heisO ψ S T w (c • F) :=
    fun w c F => by
      funext t
      simp only [heisO, Pi.smul_apply, smul_eq_mul]
      ring
  let L : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) :=
    { toFun := actPull p, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let Tm' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) := κ • ((om (p.1⁻¹, p.2⁻¹)).comp (Tm.comp L))
  have hTm'ap : ∀ Ψ, Tm' Ψ = κ • om (p.1⁻¹, p.2⁻¹) (Tm (actPull p Ψ)) := fun Ψ => rfl
  have hTm' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latAll S T ΛS ΛT) 1 f₀ Tm' := by
    refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
    · have hx' : IsHalf e (actO S T p.1 p.2 x) := (isHalf_actO p.1 p.2 x).2 hx
      have e1 : actPull p (fun t => Ψ (t + x)) = fun t => actPull p Ψ (t + actO S T p.1 p.2 x) := by
        funext t
        show Ψ (actO S T p.1⁻¹ p.2⁻¹ t + x) = Ψ (actO S T p.1⁻¹ p.2⁻¹ (t + actO S T p.1 p.2 x))
        rw [actO_add, hback]
      rw [hTm'ap, hTm'ap, e1, hTm.trans _ (hsb Ψ hΨ) _ hx',
        hW.om_heis p.1⁻¹ p.2⁻¹ _ _ (hthm _ (hsb Ψ hΨ)), hback, hsmul]
    · have hy' : IsHalf (cA D e) (actO S T p.1 p.2 y) := (isHalf_actO p.1 p.2 y).2 hy
      have e1 : actPull p (fun t => ψ (symplO S T t y) * Ψ t) =
          fun t => ψ (symplO S T t (actO S T p.1 p.2 y)) * actPull p Ψ t := by
        funext t
        show ψ (symplO S T (actO S T p.1⁻¹ p.2⁻¹ t) y) * Ψ (actO S T p.1⁻¹ p.2⁻¹ t) =
          ψ (symplO S T t (actO S T p.1 p.2 y)) * Ψ (actO S T p.1⁻¹ p.2⁻¹ t)
        conv_lhs => rw [← hback y]
        rw [Formalism.IndefR.Eqv.symplO_actO]
      rw [hTm'ap, hTm'ap, e1, hTm.modul _ (hsb Ψ hΨ) _ hy',
        hW.om_heis p.1⁻¹ p.2⁻¹ _ _ (hthm _ (hsb Ψ hΨ)), hback, hsmul]
    · rw [one_smul, hTm'ap, ← map_smul, ← hκ, ← Module.End.mul_apply, ← map_mul, hqp, map_one,
        Module.End.one_apply]
  have e3 : Tm Φ = Tm' Φ := GlobalTheory.PlaceVec.placeModel_unique hW.std hsS hsT hee hinf hTm hTm' hΦ
  rw [e3, hTm'ap, map_smul, ← Module.End.mul_apply, ← map_mul, hpq, map_one, Module.End.one_apply]

end GlobalTheory.PullModelLaw

end
