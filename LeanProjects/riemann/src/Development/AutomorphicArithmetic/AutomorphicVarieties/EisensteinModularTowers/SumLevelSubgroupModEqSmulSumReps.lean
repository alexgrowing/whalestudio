import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem T_mem_Gam (N l : ℕ) : ModularGroup.T ∈ Gam N l := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.T]
  · rw [CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.T]

private theorem mul_Tm_mem (N l M : ℕ) [NeZero M] {γ : SL(2, ZMod M)} (h : γ ∈ Gs N l M) (b : ℕ) :
    γ * Tm M b ∈ Gs N l M := by
  simp only [Gs, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
  exact Subgroup.mul_mem _ h (Subgroup.mem_map_of_mem _ (Subgroup.pow_mem _ (T_mem_Gam N l) b))

theorem UpperTheory.sum_levelSubgroupMod_eq_smul_sum_reps :
    ∀ (N l M : ℕ) [NeZero M] (R : Finset SL(2, ZMod M)), IsReps N l M R → ∀ (V : Type) [AddCommMonoid V] (f : SL(2, ZMod M) → V), (∀ γ ∈ R, ∀ b : ℕ, f (γ * Tm M b) = f γ) → ∑ γ ∈ Gs N l M, f γ = M • ∑ γ ∈ R, f γ := by
  intro N l M _ R hR V _ f hf
  obtain ⟨hsub, huniq⟩ := hR
  have key : ∑ p ∈ R ×ˢ Finset.range M, f p.1 = ∑ γ ∈ Gs N l M, f γ := by
    refine Finset.sum_bij (fun p _ => p.1 * Tm M p.2) ?_ ?_ ?_ ?_
    · intro p hp
      exact mul_Tm_mem N l M (hsub (Finset.mem_product.1 hp).1) _
    · intro p hp q hq hpq
      have hp' := Finset.mem_product.1 hp
      have hq' := Finset.mem_product.1 hq
      exact (huniq _ (mul_Tm_mem N l M (hsub hp'.1) p.2)).unique
        ⟨hp'.1, Finset.mem_range.1 hp'.2, rfl⟩ ⟨hq'.1, Finset.mem_range.1 hq'.2, hpq⟩
    · intro γ hγ
      obtain ⟨p, ⟨h1, h2, h3⟩, -⟩ := huniq γ hγ
      exact ⟨p, Finset.mem_product.2 ⟨h1, Finset.mem_range.2 h2⟩, h3.symm⟩
    · intro p hp
      exact (hf _ (Finset.mem_product.1 hp).1 _).symm
  rw [← key, Finset.sum_product, Finset.smul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  simp
