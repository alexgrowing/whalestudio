import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntSubIsLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker

noncomputable section
namespace GlobalTheory.LevLaw

theorem heisO_smul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (x : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T x (c • f) = c • heisO ψ S T x f := by
  funext t
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem omega_eq_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ e (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ vac Φ w, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (intVec D _) (intVec D _) vac → IsSBHalf e (stdHom S T) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 vac Φ w → ∀ k ∈ GfC S, ∀ k' ∈ GfC T, (∀ x, x ∈ stdHom S T ↔ actO S T k k' x ∈ stdHom S T) → ∀ p q : ℂ, om (k, k') vac = p • vac → (∀ z, IsHalf e z → p * Φ (actO S T k⁻¹ k'⁻¹ z) = q * Φ z) → om (k, k') w = q • w := by
  intro D ψ θ S T a b hS hT δ sc hstd μ om hW e SS hSS vac Φ w hvac hΦ hw k hk k' hk' hkeep p q hp hq
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hSS
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum hSS
  have sdS0 := GlobalTheory.SplitMove.selfDual_int S hstd.gS
  have sdT0 := GlobalTheory.SplitMove.selfDual_int T hstd.gT
  have hth : IsThetaFunO ψ S T vac := hvac.2.theta
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hw
  have th0 := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hstd.std S T _ _ sdS0 sdT0 e hee hinf vac hth T₀ hT₀
  have pm := GlobalTheory.SplitMove.isPlaceModel_move₂ hW hkeep hT₀ th0
  rw [hp] at pm
  have omm : ∀ r s (X : WO S T → ℂ), om r (om s X) = om (r * s) X := fun r s X => by
    rw [map_mul]; rfl

  have hv0 : vac ≠ 0 := by
    intro h0
    obtain ⟨⟨m, hm⟩, hn⟩ := hvac.2.norm
    have h1 := hn m hm
    rw [h0] at h1
    simp [nrm2] at h1
  have hp0 : p ≠ 0 := by
    intro h0
    apply hv0
    have e1 : om (k⁻¹, k'⁻¹) (om (k, k') vac) = vac := by
      rw [omm, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one]; rfl
    rw [hp, h0, zero_smul, map_zero] at e1
    exact e1.symm
  set L := om (k, k') ∘ₗ T₀ ∘ₗ LinearMap.funLeft ℂ ℂ (actO S T k k') with hL
  have pm2 : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 vac (p⁻¹ • L) := by
    refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, pm.trans Ψ hΨ x hx, heisO_smul]
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, pm.modul Ψ hΨ y hy, heisO_smul]
    · rw [LinearMap.smul_apply, pm.vac, smul_smul, inv_mul_cancel₀ hp0, one_smul]
  have w1 : w = T₀ Φ := hall T₀ hT₀
  have w2 : w = (p⁻¹ • L) Φ := hall _ pm2

  have hfun : q • (fun t => Φ (actO S T k k' t)) = p • Φ := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hz : IsHalf e (actO S T k k' z)
    · have h1 := hq _ hz
      rw [GlobalTheory.SplitHecke.actO_inv_actO] at h1
      exact h1.symm
    · have h2 : Φ (actO S T k k' z) = 0 := by
        by_contra hne; exact hz (hΦ.1 _ hne)
      have h3 : Φ z = 0 := by
        by_contra hne; exact hz (GlobalTheory.SplitHecke.isHalf_actO k k' (hΦ.1 _ hne))
      rw [h2, h3, mul_zero, mul_zero]
  have eL : L Φ = om (k, k') (T₀ fun t => Φ (actO S T k k' t)) := rfl
  calc om (k, k') w = om (k, k') (T₀ Φ) := by rw [← w1]
    _ = p⁻¹ • om (k, k') (T₀ (p • Φ)) := by
        rw [map_smul, map_smul, smul_smul, inv_mul_cancel₀ hp0, one_smul]
    _ = p⁻¹ • om (k, k') (T₀ (q • fun t => Φ (actO S T k k' t))) := by rw [hfun]
    _ = q • (p⁻¹ • L) Φ := by
        rw [map_smul, map_smul, LinearMap.smul_apply, eL, smul_comm]
    _ = q • w := by rw [← w2]

end GlobalTheory.LevLaw
