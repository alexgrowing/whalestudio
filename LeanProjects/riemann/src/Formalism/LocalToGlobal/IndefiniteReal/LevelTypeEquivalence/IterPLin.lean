import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.RedContinuous

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def thetaSubO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f}
  zero_mem' := Formalism.IndefR.Fin.theta_zero S T
  add_mem' := fun hf hg => Formalism.IndefR.Fin.theta_add S T hf hg
  smul_mem' := fun c _ hf => Formalism.IndefR.Fin.theta_smul S T c hf

theorem exists_lin_of_theta {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (Λ : (WO S T → ℂ) → ℂ)
    (hadd : ∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → Λ (f + g) = Λ f + Λ g)
    (hsmul : ∀ (c : ℂ) f, IsThetaFunO ψ S T f → Λ (c • f) = c * Λ f) :
    ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, ∀ f, IsThetaFunO ψ S T f → ℓ f = Λ f := by
  let l0 : thetaSubO ψ S T →ₗ[ℂ] ℂ :=
    { toFun := fun f => Λ f.1
      map_add' := fun f g => hadd f.1 g.1 f.2 g.2
      map_smul' := fun c f => hsmul c f.1 f.2 }
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend l0
  exact ⟨ℓ, fun f hf => LinearMap.congr_fun hℓ ⟨f, hf⟩⟩

theorem norm_setIntegral_comp_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α} (hs : μ s < ⊤)
    {S T : HSp D} (φ : α → WO S T) (F : WO S T → ℂ) (B : ℝ) (hB : ∀ w, ‖F w‖ ≤ B) :
    ‖∫ x in s, F (φ x) ∂μ‖ ≤ (μ s).toReal * B := by
  have h := norm_setIntegral_le_of_norm_le_const (f := fun x => F (φ x)) hs (fun x _ => hB (φ x))
  rw [mul_comm]
  exact h

theorem integrableOn_comp_theta {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {F : WO S T → ℂ} (hF : IsThetaFunO ψ S T F) {m n : ℕ} (φ : Mx D m n → WO S T) (hφ : Continuous φ)
    {μ : Measure (Mx D m n)} {s : Set (Mx D m n)} (hs : μ s ≠ ⊤) :
    IntegrableOn (fun x => F (φ x)) s μ := by
  obtain ⟨B, hB⟩ := theta_bounded ψ hψ S T hF
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hs
  exact Integrable.of_bound (hF.cont.comp hφ).aestronglyMeasurable B (ae_of_all _ fun x => hB (φ x))

theorem exists_int_lin {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {m n : ℕ}
    (φ : Mx D m n → WO S T) (hφ : Continuous φ) {μ : Measure (Mx D m n)} {s : Set (Mx D m n)} (hs : μ s < ⊤) :
    ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ f, IsThetaFunO ψ S T f → ℓ f = ∫ x in s, f (φ x) ∂μ) ∧
      ∀ F, IsThetaFunO ψ S T F → ∀ B : ℝ, (∀ w, ‖F w‖ ≤ B) → ‖ℓ F‖ ≤ (μ s).toReal * B := by
  obtain ⟨ℓ, hℓ⟩ := exists_lin_of_theta (ψ := ψ) (fun f => ∫ x in s, f (φ x) ∂μ)
    (fun f g hf hg => by
      simp only [Pi.add_apply]
      exact integral_add (integrableOn_comp_theta hψ hf φ hφ hs.ne) (integrableOn_comp_theta hψ hg φ hφ hs.ne))
    (fun c f _ => by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact integral_const_mul c _)
  refine ⟨ℓ, hℓ, fun F hF B hB => ?_⟩
  rw [hℓ F hF]
  exact norm_setIntegral_comp_le hs φ F B hB

theorem exists_ellI_lin {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) {r : ℕ}
    (C : Matrix (Fin T.rank) (Fin r) D.host.E) (μ : Measure (Mx D r S.rank)) [μ.IsAddHaarMeasure]
    (𝓕 : Set (Mx D r S.rank)) (h𝓕 : IsAddFundamentalDomain (ratMx D r S.rank) 𝓕 μ) :
    ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ f, IsThetaFunO ψ S T f → ℓ f = ellI S T C μ 𝓕 f) ∧
      ∀ F, IsThetaFunO ψ S T F → ∀ B : ℝ, (∀ w, ‖F w‖ ≤ B) → ‖ℓ F‖ ≤ (μ 𝓕).toReal * B :=
  exists_int_lin hψ (embI S T C) (by unfold embI; exact continuous_const.matrix_mul continuous_id)
    (covolM r S.rank μ 𝓕 h𝓕).1

end Formalism.IndefR.Eqv

end
