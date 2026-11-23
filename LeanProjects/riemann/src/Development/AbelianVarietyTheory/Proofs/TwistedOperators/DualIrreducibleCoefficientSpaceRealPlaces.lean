import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVanishesSingleCoefficientOfKernelKills
import Formalism.LocalToGlobal.IndefiniteReal.TopMult
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Matrix

namespace GlobalTheory.DualIrr

theorem dual_irr : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (c : CoefA V), IsInfFam θ → c.Is → ∀ N : Submodule ℂ (Module.Dual ℂ c.W), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ f ∈ N, (c.ρ (atTau θ V τ g)⁻¹).dualMap f ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro D V θ c hθ hc N hN

  have hinv : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∃ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      (atTau θ V τ g')⁻¹ = atTau θ V τ g := by
    intro τ g hg
    have hu : IsUnit (gramAt D V τ).det := by
      have : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det (tauE D τ) V.gram).symm
      rw [this]
      exact ((_root_.map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V)).isUnit
    have h1 : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
    set gi := (gramAt D V τ)⁻¹ * gᴴ * gramAt D V τ with hgi
    have h2 : gi * g = 1 := by
      rw [hgi, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h1, Matrix.nonsing_inv_mul _ hu]
    have h3 : g * gi = 1 := mul_eq_one_comm.1 h2
    have hgi' : gi ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
      show giᴴ * gramAt D V τ * gi = gramAt D V τ
      calc giᴴ * gramAt D V τ * gi = giᴴ * (gᴴ * gramAt D V τ * g) * gi := by rw [h1]
        _ = (g * gi)ᴴ * gramAt D V τ * (g * gi) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = gramAt D V τ := by rw [h3]; simp
    refine ⟨gi, hgi', ?_⟩
    have e : atTau θ V τ g * atTau θ V τ gi = 1 := by
      rw [← GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ hg hgi', h3, GlobalTheory.PointAtPlaceHom.atTau_one hθ V τ]
    rw [eq_inv_of_mul_eq_one_right e, inv_inv]
  set U := N.dualCoannihilator with hUdef
  have hstab : ∀ a ∈ GinfC V, ∀ v ∈ U, c.ρ a v ∈ U := by
    intro a ha
    refine Submonoid.closure_induction (motive := fun a _ => ∀ v ∈ U, c.ρ a v ∈ U) ?_ ?_ ?_
      (Formalism.IndefR.TopMult.ginf_mem_closure hθ ha)
    · rintro x ⟨τ, g, hg, rfl⟩ v hv
      obtain ⟨g', hg', e⟩ := hinv τ g hg
      rw [Submodule.mem_dualCoannihilator] at hv ⊢
      intro f hf
      have := hv _ (hN τ g' hg' f hf)
      rw [e] at this
      simpa [LinearMap.dualMap_apply] using this
    · intro v hv; simpa using hv
    · intro x y _ _ hx hy v hv
      rw [map_mul, Module.End.mul_apply]
      exact hx _ (hy v hv)
  have hU : ∀ u ∈ GinfC V, U.map (c.ρ u) ≤ U := by
    rintro u hu _ ⟨v, hv, rfl⟩
    exact hstab u hu v hv
  have hN' : U.dualAnnihilator = N := Subspace.dualCoannihilator_dualAnnihilator_eq
  rcases GlobalTheory.GenRealSchur.irr_real c hc U hU with h | h
  · right; rw [← hN', h, Submodule.dualAnnihilator_bot]
  · left; rw [← hN', h, Submodule.dualAnnihilator_top]

end GlobalTheory.DualIrr
