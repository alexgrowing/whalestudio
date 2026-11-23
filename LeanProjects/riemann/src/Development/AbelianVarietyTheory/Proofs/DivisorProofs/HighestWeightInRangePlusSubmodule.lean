import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult

theorem hw_lift_orth : ∀ (R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (φ : W →ₗ[ℂ] V) (F : Submodule ℂ V) (Λ : Ix R S → ℚ) (w : V),
    IsUnitary actW B → KStable act F → (∀ Z, IsKC Z → ∀ x, φ (actW Z x) = act Z (φ x)) →
    w ∈ LinearMap.range φ ⊔ F → w ∈ hwSub act Λ → w ∉ F →
    ∃ Ψ ∈ (F.comap φ).orthogonalBilin B, Ψ ≠ 0 ∧ Ψ ∈ hwSub actW Λ := by
  intro R S W _ _ _ actW B V _ _ act φ F Λ w hU hF hφ hw hhw hwF
  obtain ⟨_hherm, hpos, hadj⟩ := hU
  set K := F.comap φ with hK
  have hKst : ∀ Z, IsKC Z → ∀ x ∈ K, actW Z x ∈ K := by
    intro Z hZ x hx
    simp only [hK, Submodule.mem_comap] at hx ⊢
    rw [hφ Z hZ]; exact hF Z hZ _ hx
  have hperp : ∀ y, y ∈ K.orthogonalBilin B ↔ ∀ v ∈ K, B v y = 0 := fun y => Iff.rfl
  have hsame_symm : ∀ a b : Ix R S, sameBlock a b → sameBlock b a := by
    intro a b; cases a <;> cases b <;> simp [sameBlock]
  have hsame_refl : ∀ a : Ix R S, sameBlock a a := by
    intro a; cases a <;> simp [sameBlock]
  have hpos_same : ∀ a b : Ix R S, posC a b → sameBlock a b := by
    intro a b; cases a <;> cases b <;> simp [posC, sameBlock]
  have hKC_E : ∀ a b : Ix R S, sameBlock a b → IsKC (Eab a b) := by
    intro a b hab c d hcd
    simp only [Eab, Matrix.single_apply]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; exact absurd hab hcd
    · rfl
  have hperpE : ∀ a b, sameBlock a b → ∀ y ∈ K.orthogonalBilin B, actW (Eab a b) y ∈ K.orthogonalBilin B := by
    intro a b hab y hy
    rw [hperp] at hy ⊢
    intro v hv
    rw [← hadj b a (hsame_symm a b hab) v y]
    exact hy _ (hKst _ (hKC_E b a (hsame_symm a b hab)) v hv)
  have hdisj : ∀ y ∈ K, y ∈ K.orthogonalBilin B → y = 0 := by
    intro y h1 h2
    by_contra hne
    have := hpos y hne
    rw [(hperp y).1 h2 y h1] at this; simp at this
  have hdec : ∀ x, ∃ κ ∈ K, x - κ ∈ K.orthogonalBilin B := by
    intro x
    let b := Module.finBasis ℂ K
    let G : W →ₗ[ℂ] (Fin (Module.finrank ℂ K) → ℂ) := LinearMap.pi fun i => B (b i : W)
    have key : ∀ y, G y = 0 → ∀ v ∈ K, B v y = 0 := by
      intro y hy v hv
      have h1 : (B.flip y) ∘ₛₗ K.subtype = 0 := b.ext fun i => by simpa [G] using congrFun hy i
      simpa using LinearMap.congr_fun h1 ⟨v, hv⟩
    have hinj : Function.Injective (G ∘ₗ K.subtype) := by
      rw [injective_iff_map_eq_zero]
      intro z hz
      exact Subtype.ext (hdisj z z.2 ((hperp z).2 (key z hz)))
    have hsurj : Function.Surjective (G ∘ₗ K.subtype) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
    obtain ⟨z, hz⟩ := hsurj (G x)
    refine ⟨z, z.2, (hperp _).2 (key _ ?_)⟩
    rw [map_sub, ← hz]; simp
  obtain ⟨y, hy, f, hf, rfl⟩ := Submodule.mem_sup.1 hw
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨κ, hκ, hΨ⟩ := hdec x
  have hκF : φ κ ∈ F := hκ
  have hfκ : f + φ κ ∈ F := F.add_mem hf hκF
  have hφΨ : φ (x - κ) = (φ x + f) - (f + φ κ) := by rw [map_sub]; abel
  have gen : ∀ (Z : Mat R S) (c : ℂ), IsKC Z → act Z (φ x + f) = c • (φ x + f) →
      actW Z (x - κ) - c • (x - κ) ∈ K.orthogonalBilin B → actW Z (x - κ) - c • (x - κ) = 0 := by
    intro Z c hZ hw' hperpZ
    refine hdisj _ ?_ hperpZ
    show φ (actW Z (x - κ) - c • (x - κ)) ∈ F
    rw [map_sub, map_smul, hφ Z hZ, hφΨ, map_sub, hw', smul_sub]
    have : c • (φ x + f) - act Z (f + φ κ) - (c • (φ x + f) - c • (f + φ κ))
        = c • (f + φ κ) - act Z (f + φ κ) := by abel
    rw [this]
    exact F.sub_mem (F.smul_mem _ hfκ) (hF Z hZ _ hfκ)
  refine ⟨x - κ, hΨ, ?_, ?_⟩
  · intro h0
    apply hwF
    rw [sub_eq_zero.1 h0]; exact F.add_mem hκF hf
  · simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hhw ⊢
    obtain ⟨hwt, hkill⟩ := hhw
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · have e := gen (Eab a a) ((Λ a : ℚ) : ℂ) (hKC_E a a (hsame_refl a)) (hwt a)
        (Submodule.sub_mem _ (hperpE a a (hsame_refl a) _ hΨ) (Submodule.smul_mem _ _ hΨ))
      exact sub_eq_zero.1 e
    · have e := gen (Eab a b) 0 (hKC_E a b (hpos_same a b hab)) (by rw [hkill a b hab, zero_smul])
        (Submodule.sub_mem _ (hperpE a b (hpos_same a b hab) _ hΨ) (Submodule.smul_mem _ _ hΨ))
      simpa using e

end GlobalTheory.SteepMult
