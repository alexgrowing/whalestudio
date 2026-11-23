import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCCRXOpDOp

noncomputable section

namespace GlobalTheory.Mem.Lift.ThOps

theorem exists_restrict {Θ M : Type} [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup M] [Module ℂ M] (j : Θ →ₗ[ℂ] M)
    (hj : Function.Injective j) (A : Module.End ℂ M) (hA : ∀ f, ∃ g, j g = A (j f)) :
    ∃ a : Module.End ℂ Θ, ∀ f, j (a f) = A (j f) := by
  choose a ha using hA
  exact ⟨{ toFun := a
           map_add' := fun f g => hj (by simp only [map_add, ha])
           map_smul' := fun c f => hj (by simp only [map_smul, ha, RingHom.id_apply]) }, ha⟩

theorem isCCR_restrict {Θ M κ : Type} [DecidableEq κ] [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup M] [Module ℂ M]
    (j : Θ →ₗ[ℂ] M) (hj : Function.Injective j) {x d : κ → Module.End ℂ Θ} {x₀ d₀ : κ → Module.End ℂ M}
    (hx : ∀ k f, j (x k f) = x₀ k (j f)) (hd : ∀ k f, j (d k f) = d₀ k (j f)) (h : GlobalTheory.Mem.Lift.IsCCR x₀ d₀) :
    GlobalTheory.Mem.Lift.IsCCR x d := by
  refine ⟨fun k l => LinearMap.ext fun f => hj ?_, fun k l => LinearMap.ext fun f => hj ?_,
    fun k l => LinearMap.ext fun f => hj ?_⟩
  · simpa only [Module.End.mul_apply, hx] using LinearMap.congr_fun (h.1 k l) (j f)
  · simpa only [Module.End.mul_apply, hd] using LinearMap.congr_fun (h.2.1 k l) (j f)
  · have := LinearMap.congr_fun (h.2.2 k l) (j f)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, hx, hd] at this ⊢
    rw [this]
    split_ifs <;> simp

open Matrix GlobalTheory.RealWeil in

theorem exists_ops {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (hH : Hᴴ = H) (hd : H.det ≠ 0)
    {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (ρ : (ι → ℂ) → B →L[ℂ] B)
    (hρ : IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ) {Θ : Type} [AddCommGroup Θ] [Module ℂ Θ] (J : Θ →ₗ[ℂ] B)
    (hJ : Function.Injective J) (hs : ∀ f, Sm ρ (J f)) (hk : ∀ v f, ∃ g, J g = dH ρ v (J f)) :
    ∃ x d : ι → Module.End ℂ Θ, IsCCR x d ∧
      ∀ (X : Matrix ι ι ℂ) (f : Θ), J ((∑ k, ∑ l, X k l • (x k * d l)) f) = nOp ρ H X (J f) := by
  obtain ⟨x₀, d₀, hx₀, hd₀, hc⟩ := exists_isCCR_xOp_dOp ι H hH hd B ρ hρ
  let j : Θ →ₗ[ℂ] smS ρ := J.codRestrict _ hs
  have hj : Function.Injective j := fun f g e => hJ (congrArg Subtype.val e)
  have h1 : ∀ k, ∃ a : Module.End ℂ Θ, ∀ f, j (a f) = x₀ k (j f) := fun k => exists_restrict j hj _ fun f => by
    obtain ⟨g₁, e₁⟩ := hk (Pi.single k 1) f
    obtain ⟨g₂, e₂⟩ := hk (Complex.I • Pi.single k 1) f
    refine ⟨g₁ - Complex.I • g₂, Subtype.ext ?_⟩
    rw [hx₀]
    change J _ = xOp ρ k (J f)
    rw [xOp, map_sub, map_smul, e₁, e₂]
  have h2 : ∀ k, ∃ a : Module.End ℂ Θ, ∀ f, j (a f) = d₀ k (j f) := fun k => exists_restrict j hj _ fun f => by
    obtain ⟨g₁, e₁⟩ := hk (H⁻¹ *ᵥ Pi.single k 1) f
    obtain ⟨g₂, e₂⟩ := hk (Complex.I • H⁻¹ *ᵥ Pi.single k 1) f
    refine ⟨(-(1 / (4 * Real.pi)) : ℂ) • (g₁ + Complex.I • g₂), Subtype.ext ?_⟩
    rw [hd₀]
    change J _ = dOp ρ H k (J f)
    rw [dOp, map_smul, map_add, map_smul, e₁, e₂]
  choose x hx using h1
  choose d hd' using h2
  refine ⟨x, d, isCCR_restrict j hj hx hd' hc, fun X f => ?_⟩
  have ex : ∀ k f, J (x k f) = xOp ρ k (J f) := fun k f => (congrArg Subtype.val (hx k f)).trans (hx₀ k _)
  have ed : ∀ k f, J (d k f) = dOp ρ H k (J f) := fun k f => (congrArg Subtype.val (hd' k f)).trans (hd₀ k _)
  simp only [nOp, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, map_sum, map_smul, ex, ed]

end GlobalTheory.Mem.Lift.ThOps

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

open GlobalTheory.RealWeil in

theorem GlobalTheory.Mem.Lift.exists_isCCR_theta : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D), ∃ x d : GlobalTheory.RealWeil.Ix S T → Module.End ℂ (GlobalTheory.RealWeil.thetaSub ψ S T), IsCCR x d ∧ ∀ (X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ) (f : GlobalTheory.RealWeil.thetaSub ψ S T) (F : GlobalTheory.RealWeil.BB ψ S T), (F.1 : WO S T → ℂ) = f.1 → ((∑ k, ∑ l, X k l • (x k * d l)) f).1 = (nOp (GlobalTheory.RealWeil.rhoV hψ σ S T) (GlobalTheory.RealWeil.HM S T) X F).1 := by
  intro D θ σ h ψ hψ S T
  let J : thetaSub ψ S T →ₗ[ℂ] BB ψ S T :=
    { toFun := fun f => toB hψ f.1 f.2
      map_add' := fun f g => QB_ext fun x => rfl
      map_smul' := fun a f => QB_ext fun x => rfl }
  have hc : ∀ f, ((J f).1 : WO S T → ℂ) = f.1 := fun f => coe_toB hψ f.1 f.2
  have hJ : Function.Injective J := fun f g e => Subtype.ext (by rw [← hc, ← hc, e])
  have ht : ∀ f, IsThetaFunO ψ S T (J f).1 := fun f => (hc f).symm ▸ f.2
  have hs : ∀ f, GlobalTheory.RealWeil.Sm (rhoV hψ σ S T) (J f) := fun f => sm_of_theta h hψ _ (ht f)
  have hk : ∀ v f, ∃ g, J g = dH (rhoV hψ σ S T) v (J f) := by
    intro v f
    obtain ⟨F', hF', hd⟩ := exists_deriv h hψ (J f) (ht f) v
    refine ⟨⟨F'.1, hF'⟩, QB_ext fun w => ?_⟩
    rw [hc]
    exact (hd w).unique (((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dH v (hs f)))
  obtain ⟨x, d, hxd, hn⟩ := ThOps.exists_ops (HM S T) HM_herm HM_det (rhoV hψ σ S T) (isHeis_rhoB h hψ) J hJ hs hk
  refine ⟨x, d, hxd, fun X f F hF => ?_⟩
  have e : F = J f := QB_ext fun w => by rw [hF, hc]
  rw [e, ← hn, hc]

end
