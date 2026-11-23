import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BurnsideSurjOfIrred

noncomputable section

open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.RgFl

theorem finrank_sq_le_of_span {A V : Type} [Ring A] [Algebra ℂ A] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V) (hρ : Function.Surjective ρ) {d l : ℕ}
    (x y : Fin d → A) (a : Fin l → A)
    (hs : Submodule.span ℂ {z | ∃ i j, ∃ c ∈ Algebra.adjoin ℂ (Set.range a), z = x i * c * y j} = ⊤) :
    Module.finrank ℂ V ^ 2 ≤
      d ^ 2 * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i => ρ (a i))) := by
  classical
  set B := Algebra.adjoin ℂ (Set.range fun i => ρ (a i)) with hB
  have hmap : ∀ c ∈ Algebra.adjoin ℂ (Set.range a), ρ c ∈ B := by
    intro c hc
    have e : B = (Algebra.adjoin ℂ (Set.range a)).map ρ := by
      rw [hB, AlgHom.map_adjoin, ← Set.range_comp]
      rfl
    rw [e]
    exact ⟨c, hc, rfl⟩
  let G : Fin d × Fin d → (B →ₗ[ℂ] Module.End ℂ V) := fun p =>
    (LinearMap.mulLeft ℂ (ρ (x p.1))) ∘ₗ (LinearMap.mulRight ℂ (ρ (y p.2))) ∘ₗ B.val.toLinearMap
  let F : (Fin d × Fin d → B) →ₗ[ℂ] Module.End ℂ V :=
    ∑ p : Fin d × Fin d, G p ∘ₗ LinearMap.proj p
  have hFs : ∀ (p : Fin d × Fin d) (b : B), F (Pi.single p b) = ρ (x p.1) * b * ρ (y p.2) := by
    intro p b
    simp only [F, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single p]
    · simp [G, mul_assoc]
    · intro q _ hq
      simp [Pi.single_eq_of_ne hq]
    · simp
  have hF : LinearMap.range F = ⊤ := by
    rw [eq_top_iff]
    rintro f -
    obtain ⟨g, rfl⟩ := hρ f
    have hg : g ∈ Submodule.span ℂ {z | ∃ i j, ∃ c ∈ Algebra.adjoin ℂ (Set.range a), z = x i * c * y j} := by
      rw [hs]; exact Submodule.mem_top
    induction hg using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, j, c, hc, rfl⟩ := hz
      exact ⟨Pi.single (i, j) ⟨ρ c, hmap c hc⟩, by simp [hFs]⟩
    | zero => simp
    | add u v _ _ hu hv => simpa using Submodule.add_mem _ hu hv
    | smul t u _ hu => simpa using Submodule.smul_mem _ t hu
  have h1 : Module.finrank ℂ (Module.End ℂ V) ≤ Module.finrank ℂ (Fin d × Fin d → B) := by
    have := LinearMap.finrank_range_le F
    rwa [hF, finrank_top] at this
  have h2 : Module.finrank ℂ (Module.End ℂ V) = Module.finrank ℂ V ^ 2 := by
    rw [Module.finrank_linearMap, sq]
  have h3 : Module.finrank ℂ (Fin d × Fin d → B) = d ^ 2 * Module.finrank ℂ B := by
    rw [Module.finrank_pi_fintype]
    simp [sq]
  rw [h2, h3] at h1
  exact h1

theorem stSimple_of_stComm : StComm → StSimple := by
  intro h d l
  obtain ⟨C, hC⟩ := h l (2 * d ^ 2)
  refine ⟨C, fun A _ _ hA V _ _ _ ρ hirr => ?_⟩
  obtain ⟨x, y, a, hcomm, hs⟩ := hA
  rcases subsingleton_or_nontrivial V with hV | hV
  · simp [Module.finrank_zero_of_subsingleton]
  have hsurj := GlobalTheory.CompanionTheory.Burnside.burnside_surj_of_irred ρ hirr
  have h1 := finrank_sq_le_of_span ρ hsurj x y a hs
  have h2 := hC V (fun i => ρ (a i)) (fun i j => (hcomm i j).map ρ)
  have hm : 0 < Module.finrank ℂ V := Module.finrank_pos
  generalize Module.finrank ℂ V = m at *
  generalize Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i => ρ (a i))) = b at *
  have h3 : m * m ≤ C * m := by nlinarith
  exact Nat.le_of_mul_le_mul_right h3 hm

end GlobalTheory.CompanionTheory.RgFl

end
