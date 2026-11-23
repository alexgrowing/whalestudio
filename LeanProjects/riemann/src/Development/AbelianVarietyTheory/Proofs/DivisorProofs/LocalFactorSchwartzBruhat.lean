import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSpanLocalTensors
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.SliceSB

theorem mem_SB_of_rest : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl F) (φ : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ),
    Rest (evFin F v) φ r → r ≠ 0 → φ ∈ SB (κ → Fv F v) := by
  intro F _ _ κ _ v φ r hR hr
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, r x₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hr (funext h)

  let s : (κ → Fv F v) → (κ → AF F) := fun y => x₀ + fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x₀ i))
  have hs_at : ∀ y : κ → Fv F v, At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x₀ i))) := by
    intro y u hu
    funext i
    exact GlobalTheory.LatVac.at_liftV v _ u hu
  have hs_ev : ∀ y : κ → Fv F v, (fun i => evFin F v (s y i)) = y := by
    intro y
    funext i
    simp only [s, Pi.add_apply, map_add, GlobalTheory.LatVac.evFin_liftV]
    abel
  let P : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ) := LinearMap.funLeft ℂ ℂ s
  have hP : schA F κ ≤ (SB (κ → Fv F v)).comap P := by
    refine le_trans (GlobalTheory.PureAtPlace.schA_le_span_tens F v κ) (Submodule.span_le.2 ?_)
    rintro _ ⟨φ', r', hφ', hr', rfl⟩
    have hinv := (hr' 0 (zero_mem _)).1
    have e : P (tens (evFin F v) φ' r') = r' x₀ • φ' := by
      funext y
      simp only [P, LinearMap.funLeft_apply, Function.comp_apply, tens, Pi.smul_apply, smul_eq_mul]
      rw [hs_ev y, show s y = x₀ + _ from rfl, hinv x₀ _ (hs_at y)]
      ring
    show P (tens (evFin F v) φ' r') ∈ SB (κ → Fv F v)
    rw [e]
    exact Submodule.smul_mem _ _ hφ'
  have h1 : P (tens (evFin F v) φ r) ∈ SB (κ → Fv F v) := hP hR.2
  have e : P (tens (evFin F v) φ r) = r x₀ • φ := by
    funext y
    simp only [P, LinearMap.funLeft_apply, Function.comp_apply, tens, Pi.smul_apply, smul_eq_mul]
    rw [hs_ev y, show s y = x₀ + _ from rfl, hR.1 x₀ _ (hs_at y)]
    ring
  rw [e] at h1
  have := Submodule.smul_mem _ (r x₀)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hx₀, one_smul] at this

end GlobalTheory.SliceSB

end
