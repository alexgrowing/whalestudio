import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurLemmaThetaFunctionsFromMatrixCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology

namespace GlobalTheory.Mem.LiftCmp

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.RealWeil GlobalTheory.FockCompare GlobalTheory.OrientedHeis

theorem actO_inv_cancel {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
  have a : Formalism.L2.Theta.mt T h⁻¹ * Formalism.L2.Theta.mt T h = 1 := by
    unfold Formalism.L2.Theta.mt
    simp
  have b : Formalism.L2.Theta.mt S g⁻¹ * Formalism.L2.Theta.mt S g = 1 := by
    unfold Formalism.L2.Theta.mt
    simp
  unfold actO
  rw [inv_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, a, Matrix.one_mul, Matrix.mul_assoc, b, Matrix.mul_one]

theorem eq_smul_of_inv_mul {G H M : Type} [Group G] [Group H] [AddCommGroup M] [Module ℂ M]
    (om : G × H →* Module.End ℂ M) (A : Module.End ℂ M) (g : G) (k : H) {c : ℂ} (hc : c ≠ 0) (f : M)
    (e : (om (g⁻¹, k⁻¹) * A) f = c • f) : om (g, k) f = c⁻¹ • A f := by
  have e := congrArg (om (g, k)) e
  rw [← Module.End.mul_apply, ← mul_assoc, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel,
    Prod.mk_one_one, map_one, one_mul, map_smul] at e
  rw [e, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem weil_eq_smul_osc : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → ∀ Ω : GA D S × GA D T → GlobalTheory.RealWeil.BB ψ S T → GlobalTheory.RealWeil.BB ψ S T, GlobalTheory.RealWeil.IsOsc (GlobalTheory.RealWeil.rhoV hψ σ S T) (fun p v => GlobalTheory.RealWeil.mM θ S T p *ᵥ v) Ω → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ F : GlobalTheory.RealWeil.BB ψ S T, IsThetaFunO ψ S T F.1 → om (g, h) F.1 = c • ((Ω (g, h) F).1 : WO S T → ℂ) := by
  intro D θ σ h ψ hψ S T om hw Ω hΩ g hg k hk
  unfold IsOsc at hΩ
  obtain ⟨hadd, hsmul, hsm, hone, hmul, hheis, hcomm, hunit⟩ := hΩ
  have hθ := h.inf
  have sm := sm_of_theta (S := S) (T := T) h hψ
  have hfin : ∀ p {u : WO S T}, u.map (infPart D) = 0 → ∀ F, GlobalTheory.RealWeil.Sm (rhoV hψ σ S T) F →
      Ω p (rhoB hψ u F) = rhoB hψ u (Ω p F) := fun p u hu F hF => hcomm p _ (rhoB_comm h hψ hu) F hF
  have hth : ∀ p F, IsThetaFunO ψ S T F.1 → IsThetaFunO ψ S T (Ω p F).1 := by
    intro p F hF
    obtain ⟨U, hU, hl⟩ := hF.level
    refine theta_of_sm h hψ _ (hsm p F (sm F hF)) ⟨U, hU, fun u hu h0 => ?_⟩
    have e : rhoB hψ u F = F := QB_ext fun x => by rw [coe_rhoB, hl u hu h0]
    rw [← coe_rhoB hψ, ← hfin p h0 F (sm F hF), e]
  obtain ⟨om', hom⟩ := exists_hom hψ Ω hth (fun p F F' h1 h2 => hadd p F F' (sm F h1) (sm F' h2))
    (fun p a F h1 => hsmul p a F (sm F h1)) (fun F h1 => hone F (sm F h1)) fun p p' F h1 => hmul p p' F (sm F h1)
  have lift : ∀ f, IsThetaFunO ψ S T f → ∃ F : BB ψ S T, (F.1 : WO S T → ℂ) = f :=
    fun f hf => ⟨toB hψ f hf, coe_toB hψ f hf⟩
  have pres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (om' p f) := by
    intro p f hf
    obtain ⟨F, rfl⟩ := lift f hf
    rw [hom p F hf]
    exact hth p F hf
  have Heisenberg₂ : ∀ w f, IsThetaFunO ψ S T f →
      om' (g, k) (heisO ψ S T w f) = heisO ψ S T (actO S T g k w) (om' (g, k) f) := by
    intro w f hf
    obtain ⟨F, rfl⟩ := lift f hf
    obtain ⟨u, v, hu, rfl⟩ := exists_parts h w
    have h1 : IsThetaFunO ψ S T (rhoV hψ σ S T v F).1 := by
      rw [coe_rhoV]
      exact theta_heisO_real hθ hψ (real_iotaV h v) hf
    have h2 : IsThetaFunO ψ S T (rhoB hψ u (rhoV hψ σ S T v F)).1 := by
      rw [coe_rhoB]
      exact GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 h1 hu
    have e1 : actO S T g k (u + iotaV σ S T v) = u + iotaV σ S T (mM θ S T (g, k) *ᵥ v) := by
      rw [GlobalTheory.WeilVacMove.actO_add, actO_fin h hg hk hu, actO_iotaV h]
    rw [hom _ F hf, e1, ← coe_rhoB hψ _ F, ← coe_rhoB hψ _ (Ω (g, k) F), rhoB_add h hψ hu v F,
      rhoB_add h hψ hu _ (Ω (g, k) F), hom _ _ h2, hfin _ hu _ (sm _ h1), hheis _ _ _ (sm F hf)]
  obtain ⟨c, hc, hM⟩ := GlobalTheory.T.schur_lemma_thetaFunctions_from_matrixCoefficients D ψ hψ S T (om (g⁻¹, k⁻¹) * om' (g, k))
    (fun f hf => hw.om_pres _ _ (pres _ f hf))
    (fun w f hf => by
      rw [Module.End.mul_apply, Module.End.mul_apply, Heisenberg₂ w f hf, hw.om_heis _ _ _ _ (pres _ f hf),
        actO_inv_cancel])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, hw.om_unit μ 𝓕 hμ h𝓕 _ _ (pres _ f hf)]
      obtain ⟨F, rfl⟩ := lift f hf
      rw [hom _ F hf]
      exact lintegral_eq_of_norms hψ μ 𝓕 hμ h𝓕 fun H _ _ _ Φ hΦ =>
        hunit H Φ (fun v => hΦ _) _ F (sm F hf))
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  refine ⟨c⁻¹, by rw [norm_inv, hc, inv_one], fun F hF => ?_⟩
  rw [← hom _ F hF]
  exact eq_smul_of_inv_mul om _ g k hc0 _ (hM F.1 hF)

end GlobalTheory.Mem.LiftCmp

end
