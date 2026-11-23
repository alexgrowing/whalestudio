import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaProjectionIntertwiningStatement
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem smul_one_mulVec_divisor {R : Type} [CommRing R] {n : ℕ} (c : R) (v : Fin n → R) :
    (c • (1 : Matrix (Fin n) (Fin n) R)) *ᵥ v = c • v := by
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply]

theorem proj_kills_other_eig : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (C : Type) [Field C] [Algebra O C] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (σ : Λ →+* O) (f : RL p O Λ →+* O) (ρ : Λ → Matrix (Fin h) (Fin h) (Ainf p O)) (e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) (π : (Fin h → C) →ₗ[C] (Fin N → C)), Function.Injective (algebraMap O C) → IsTheta σ f → IsFrame ρ e → IsProj C e f π → ∀ z ∈ ⨆ s : {s : Λ →+* O // s ≠ σ}, eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) s.1, π z = 0 := by
  intro p _ O _ _ _ C _ _ Λ _ _ N h σ f ρ e π hinj hθ hfr hπ z hz
  suffices hle : (⨆ s : {s : Λ →+* O // s ≠ σ}, eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) s.1) ≤ LinearMap.ker π from
    LinearMap.mem_ker.mp (hle hz)
  refine iSup_le fun s => ?_
  intro z hz
  rw [LinearMap.mem_ker]
  obtain ⟨l, hl⟩ : ∃ l, s.1 l ≠ σ l := by
    by_contra hc
    push_neg at hc
    exact s.2 (RingHom.ext hc)

  have hmat : IsMat e e (ρ l) (((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l : RL p O Λ) • (1 : Matrix (Fin N) (Fin N) (RL p O Λ))) := by
    intro w
    rw [smul_one_mulVec_divisor, hfr l w]
  have h1 := GlobalTheory.T.theta_projection_intertwining p O C Λ N h f e e π π (ρ l) _ hπ hπ hmat z
  have hf : f ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) = σ l := by
    rw [hθ]; simp
  have hY : ((((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l : RL p O Λ) • (1 : Matrix (Fin N) (Fin N) (RL p O Λ))).map ((algebraMap O C).comp f)) = (algebraMap O C (σ l)) • (1 : Matrix (Fin N) (Fin N) C) := by
    ext i j
    by_cases hij : i = j <;> simp [hij, hf]
  rw [hY, smul_one_mulVec_divisor] at h1

  have hz' : redC C (ρ l) z = algebraMap O C (s.1 l) • z := by
    have := (Submodule.mem_iInf _).mp hz l
    rw [Module.End.mem_eigenspace_iff] at this
    rw [← this]
    simp [redC, Matrix.map_map]
  rw [hz', map_smul] at h1
  have hne : algebraMap O C (s.1 l) - algebraMap O C (σ l) ≠ 0 := by
    rw [sub_ne_zero]; exact fun h => hl (hinj h)
  have h2 : (algebraMap O C (s.1 l) - algebraMap O C (σ l)) • π z = 0 := by
    rw [sub_smul, h1, sub_self]
  exact (smul_eq_zero.mp h2).resolve_left hne

end GlobalTheory.DetInv
