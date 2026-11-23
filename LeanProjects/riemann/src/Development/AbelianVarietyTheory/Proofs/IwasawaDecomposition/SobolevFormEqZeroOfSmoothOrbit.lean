import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevContinuousFormGardingVectorStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

theorem cyc_mul_mem_UJset {n : ℕ} {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UJset ε)
    (hb : b ∈ UJset ε) : a * b ∈ UJset ε := by
  have h1 : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
  have h2 : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := hb
  show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
  calc (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [h1, h2]

theorem clm_eq_zero_of_orbit {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (hi : IsIrredOn (UJset ε) σ)
    (L : H →L[ℂ] ℂ) {v : H} (hv : v ≠ 0) (h : ∀ g ∈ UJset ε, L (σ g v) = 0) (w : H) : L w = 0 := by
  let S : Submodule ℂ H :=
    { carrier := {x | ∀ g ∈ UJset ε, L (σ g x) = 0}
      add_mem' := fun ha hb g hg => by rw [map_add, map_add, ha g hg, hb g hg, add_zero]
      zero_mem' := fun g _ => by rw [map_zero, map_zero]
      smul_mem' := fun c x ha g hg => by rw [map_smul, map_smul, ha g hg, smul_zero] }
  have hc : IsClosed (S : Set H) := by
    have : (S : Set H) = ⋂ g ∈ UJset ε, {x | L (σ g x) = 0} := by
      ext x; simp only [Set.mem_iInter]; rfl
    rw [this]
    exact isClosed_biInter fun g _ => isClosed_eq (L.continuous.comp (σ g).continuous) continuous_const
  have hst : ∀ g ∈ UJset ε, ∀ x ∈ S, σ g x ∈ S := fun g hg x hx a ha => by
    have := hx (a * g) (cyc_mul_mem_UJset ha hg)
    rwa [hσ.1.2 a ha g hg] at this
  rcases hi S hc hst with h0 | h0
  · have : v ∈ S := h
    rw [h0] at this
    exact absurd this hv
  · have : w ∈ S := by rw [h0]; trivial
    have h1 := this 1 (by show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * 1 = Formalism.REAL.Jm ε; simp)
    rwa [hσ.1.1] at h1

theorem sobCont_eq_zero_of_orbit : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ (lieG G) (trRep σ P) ℓ → ∀ v ∈ smSub G (trRep σ P), v ≠ 0 → (∀ g ∈ UJset ε, ℓ (σ g v) = 0) → ∀ w ∈ smSub G (trRep σ P), ℓ w = 0 := by
  intro n ε H _ _ _ σ P G hP hG hσ hi ℓ hℓ v hv hv0 h0 w hw
  obtain ⟨hb, hs⟩ := GlobalTheory.T.sobolevContinuous_form_gardingVector n ε H σ P G hP hG hσ ℓ hℓ
  have key : ∀ φ, IsTest φ → ℓ (gard ε σ φ w) = 0 := fun φ hφ => by
    obtain ⟨C, hC⟩ := hb φ hφ
    let L : H →L[ℂ] ℂ :=
      (ℓ ∘ₗ GlobalTheory.LowTypeRestriction.garding hσ hφ.continuous hφ.2).mkContinuousOfExistsBound ⟨C, hC⟩
    refine clm_eq_zero_of_orbit hσ hi L hv0 (fun g hg => ?_) w
    show ℓ (gard ε σ φ (σ g v)) = 0
    rw [(hs _ (sigma_mem hP hG hσ hv hg)).2 φ hφ]
    have : ∀ a : Formalism.REAL.UJ ε, ℓ (σ (umat a) (σ g v)) = 0 := fun a => by
      have := h0 (umat a * g) (cyc_mul_mem_UJset a.2 hg)
      rwa [hσ.1.2 _ a.2 g hg] at this
    simp [this]
  have := eq_zero_of_forall_test (hs w hw).1 fun φ hφ => by rw [← (hs w hw).2 φ hφ, key φ hφ]
  have e : σ (umat (1 : Formalism.REAL.UJ ε)) w = w := by
    show σ 1 w = w
    rw [hσ.1.1]; rfl
  simpa only [e] using this

end GlobalTheory.SmVec
