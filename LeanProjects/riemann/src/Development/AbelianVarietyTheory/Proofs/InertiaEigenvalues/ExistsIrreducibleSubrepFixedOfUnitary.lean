import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOrthogonalProjectionFinite

namespace GlobalTheory.UnitarySemisimple

variable {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W]

theorem exists_orth_proj (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (hdef : ∀ v, B v v = 0 → v = 0)
    (M : Submodule ℂ W) [FiniteDimensional ℂ M] (v : W) :
    ∃ m ∈ M, ∀ z ∈ M, B z (v - m) = 0 := by
  first
  | exact @_root_.GlobalTheory.OrthogonalProjection.exists_orth_proj
  | exact _root_.GlobalTheory.OrthogonalProjection.exists_orth_proj
  | (apply _root_.GlobalTheory.OrthogonalProjection.exists_orth_proj <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrthogonalProjection.exists_orth_proj <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrthogonalProjection.exists_orth_proj <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrthogonalProjection.exists_orth_proj ..)

theorem rho_inv_rho (ρ : Representation ℂ H W) (g : H) (u : W) : ρ g⁻¹ (ρ g u) = u := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem rho_rho_inv (ρ : Representation ℂ H W) (g : H) (u : W) : ρ g (ρ g⁻¹ u) = u := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem orth_stable (ρ : Representation ℂ H W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (hinv : ∀ g u v, B (ρ g u) (ρ g v) = B u v) (Z : Subrepresentation ρ) (s : W)
    (hs : ∀ z ∈ Z.toSubmodule, B z s = 0) (g : H) : ∀ z ∈ Z.toSubmodule, B z (ρ g s) = 0 := by
  intro z hz
  calc B z (ρ g s) = B (ρ g (ρ g⁻¹ z)) (ρ g s) := by rw [rho_rho_inv]
    _ = B (ρ g⁻¹ z) s := hinv _ _ _
    _ = 0 := hs _ (Z.apply_mem_toSubmodule _ hz)

theorem exists_compl_proj (ρ : Representation ℂ H W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (hdef : ∀ v, B v v = 0 → v = 0) (hinv : ∀ g u v, B (ρ g u) (ρ g v) = B u v)
    (hadm : ∀ v, ∃ K : Subgroup H, (∀ k ∈ K, ρ k v = v) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K) ∧
      ∀ w, (Set.range fun k : K => ρ k w).Finite)
    (Z : Subrepresentation ρ) (v : W) :
    ∃ t ∈ Z.toSubmodule, ∀ z ∈ Z.toSubmodule, B z (v - t) = 0 := by
  classical
  obtain ⟨K, hvK, hfd, hfin⟩ := hadm v
  have ofF : ∀ u ∈ GlobalTheory.PRep.fixed ρ K, ∀ k ∈ K, ρ k u = u := by
    intro u hu k hk
    have := hu ⟨k, hk⟩
    simpa using this
  have memF : ∀ u, (∀ k ∈ K, ρ k u = u) → u ∈ GlobalTheory.PRep.fixed ρ K := by
    intro u hu k
    show ρ (k : H) u = ((1 : ℂˣ) : ℂ) • u
    simp [hu k k.2]
  haveI : FiniteDimensional ℂ (Z.toSubmodule ⊓ GlobalTheory.PRep.fixed ρ K : Submodule ℂ W) :=
    Submodule.finiteDimensional_of_le inf_le_right
  obtain ⟨m, hmM, hm⟩ := exists_orth_proj B hdef (Z.toSubmodule ⊓ GlobalTheory.PRep.fixed ρ K) v
  refine ⟨m, hmM.1, fun z hz => ?_⟩
  have hwK : ∀ k ∈ K, ρ k (v - m) = v - m := by
    intro k hk
    rw [map_sub, hvK k hk, ofF m hmM.2 k hk]
  set s := (hfin z).toFinset with hs
  have hmem : ∀ o ∈ s, ∃ k' : K, ρ k' z = o := by
    intro o ho
    simpa [s] using ho
  have hperm : ∀ k ∈ K, ∑ o ∈ s, ρ k o = ∑ o ∈ s, o := by
    intro k hk
    apply Finset.sum_nbij' (fun o => ρ k o) (fun o => ρ k⁻¹ o)
    · intro o ho
      obtain ⟨k', rfl⟩ := hmem o ho
      simp only [s, Set.Finite.mem_toFinset, Set.mem_range]
      exact ⟨⟨k, hk⟩ * k', by simp [map_mul, Module.End.mul_apply]⟩
    · intro o ho
      obtain ⟨k', rfl⟩ := hmem o ho
      simp only [s, Set.Finite.mem_toFinset, Set.mem_range]
      exact ⟨⟨k, hk⟩⁻¹ * k', by simp [map_mul, Module.End.mul_apply]⟩
    · intro o _; exact rho_inv_rho ρ k o
    · intro o _; exact rho_rho_inv ρ k o
    · intro o _; rfl
  have heZ : ∑ o ∈ s, o ∈ Z.toSubmodule := by
    refine Submodule.sum_mem _ (fun o ho => ?_)
    obtain ⟨k', rfl⟩ := hmem o ho
    exact Z.apply_mem_toSubmodule _ hz
  have heF : ∑ o ∈ s, o ∈ GlobalTheory.PRep.fixed ρ K := by
    refine memF _ (fun k hk => ?_)
    rw [map_sum, hperm k hk]
  have h0 := hm _ ⟨heZ, heF⟩
  have hterm : ∀ o ∈ s, B o (v - m) = B z (v - m) := by
    intro o ho
    obtain ⟨k', rfl⟩ := hmem o ho
    rw [← hinv k' z (v - m), hwK k' k'.2]
  rw [map_sum, LinearMap.sum_apply, Finset.sum_congr rfl hterm, Finset.sum_const] at h0
  have hz1 : z ∈ s := by
    simp only [s, Set.Finite.mem_toFinset, Set.mem_range]
    exact ⟨1, by simp⟩
  have hcard : s.card ≠ 0 := Finset.card_ne_zero.2 ⟨z, hz1⟩
  rw [nsmul_eq_mul] at h0
  rcases mul_eq_zero.1 h0 with h | h
  · exact absurd (by exact_mod_cast h) hcard
  · exact h

def orbSpan (ρ : Representation ℂ H W) (y : W) : Subrepresentation ρ :=
  ⟨Submodule.span ℂ (Set.range fun g => ρ g y), by
    intro g v hv
    have hle : (Submodule.span ℂ (Set.range fun g => ρ g y)).map (ρ g) ≤
        Submodule.span ℂ (Set.range fun g => ρ g y) := by
      rw [Submodule.map_span]
      apply Submodule.span_mono
      rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
      exact ⟨g * h, by simp [map_mul]⟩
    exact hle (Submodule.mem_map_of_mem hv)⟩

theorem mem_orbSpan (ρ : Representation ℂ H W) (y : W) : y ∈ (orbSpan ρ y).toSubmodule :=
  Submodule.subset_span ⟨1, by simp⟩

theorem orbSpan_le (ρ : Representation ℂ H W) (y : W) (Z : Subrepresentation ρ)
    (hy : y ∈ Z.toSubmodule) : (orbSpan ρ y).toSubmodule ≤ Z.toSubmodule :=
  Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact Z.apply_mem_toSubmodule g hy)

end GlobalTheory.UnitarySemisimple

namespace GlobalTheory.UnitarySemisimple

end GlobalTheory.UnitarySemisimple
