import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import GroundTheory.AutomorphicForms.GeometricLemma
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.LeviCont

theorem levi_iso_homeo (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ) (φ : Levi k m ≃* levi k N β) (hφ : ∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) : Continuous φ ∧ Continuous φ.symm := by
  have hcont : ∀ (Ψ : Levi k m → GL (Fin N) k) (ρ : ∀ a, GL (m a) k → Matrix (m a) (m a) k),
      (∀ a, Continuous (ρ a)) →
      (∀ g a (i j : m a), (Ψ g : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) = ρ a (g a) i j) →
      (∀ g a b (i : m a) (j : m b), a ≠ b →
        (Ψ g : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0) →
      Continuous fun g => (Ψ g : Matrix (Fin N) (Fin N) k) := by
    intro Ψ ρ hρ hs hn
    refine continuous_pi fun r => continuous_pi fun s => ?_
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective r
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective s
    by_cases hab : a = b
    · subst hab
      simp_rw [hs]
      exact (continuous_apply j).comp ((continuous_apply i).comp ((hρ a).comp (continuous_apply a)))
    · simp_rw [hn _ _ _ _ _ hab]
      exact continuous_const
  have hinv : ∀ g, ((φ g : levi k N β) : GL (Fin N) k)⁻¹ = leviEmb k e g⁻¹ := by
    intro g
    rw [← hφ, map_inv, Subgroup.coe_inv]
  have hs1 : ∀ g a (i j : m a), ((φ g : levi k N β) : GL (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) =
      (g a : Matrix (m a) (m a) k) i j := by
    intro g a i j
    rw [hφ]
    exact leviEmb_apply_same k e g a i j
  have hs2 : ∀ g a (i j : m a),
      (((φ g : levi k N β) : GL (Fin N) k)⁻¹ : GL (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) =
      (((g a)⁻¹ : GL (m a) k) : Matrix (m a) (m a) k) i j := by
    intro g a i j
    rw [hinv]
    exact leviEmb_apply_same k e g⁻¹ a i j
  have hn1 : ∀ g a b (i : m a) (j : m b), a ≠ b →
      ((φ g : levi k N β) : GL (Fin N) k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 := by
    intro g a b i j hab
    rw [hφ]
    exact leviEmb_apply_ne k e g hab i j
  have hn2 : ∀ g a b (i : m a) (j : m b), a ≠ b →
      (((φ g : levi k N β) : GL (Fin N) k)⁻¹ : GL (Fin N) k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 := by
    intro g a b i j hab
    rw [hinv]
    exact leviEmb_apply_ne k e g⁻¹ hab i j
  refine ⟨?_, ?_⟩
  · refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
    · exact hcont (fun g => (φ g : GL (Fin N) k)) (fun a u => (u : Matrix (m a) (m a) k))
        (fun a => Units.continuous_val) hs1 hn1
    · exact hcont (fun g => ((φ g : GL (Fin N) k))⁻¹) (fun a u => ((u⁻¹ : GL (m a) k) : Matrix (m a) (m a) k))
        (fun a => Units.continuous_coe_inv) hs2 hn2
  · refine continuous_pi fun a => Units.continuous_iff.2 ⟨?_, ?_⟩
    · refine continuous_pi fun i => continuous_pi fun j => ?_
      have h : ∀ h : levi k N β, ((φ.symm h a : GL (m a) k) : Matrix (m a) (m a) k) i j =
          ((h : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) := by
        intro h
        rw [← hs1, MulEquiv.apply_symm_apply]
      simp_rw [Function.comp_apply, h]
      exact (continuous_apply _).comp ((continuous_apply _).comp
        ((Units.continuous_val (M := Matrix (Fin N) (Fin N) k)).comp continuous_subtype_val))
    · refine continuous_pi fun i => continuous_pi fun j => ?_
      have h : ∀ h : levi k N β, (((φ.symm h a)⁻¹ : GL (m a) k) : Matrix (m a) (m a) k) i j =
          (((h : GL (Fin N) k))⁻¹ : GL (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) := by
        intro h
        rw [← hs2, MulEquiv.apply_symm_apply]
      simp_rw [h]
      exact (continuous_apply _).comp ((continuous_apply _).comp
        ((Units.continuous_coe_inv (M := Matrix (Fin N) (Fin N) k)).comp continuous_subtype_val))

end GlobalTheory.CompanionTheory.LeviCont
