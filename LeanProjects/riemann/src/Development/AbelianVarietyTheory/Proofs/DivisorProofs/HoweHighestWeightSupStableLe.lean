import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHighestWeightLiftModStableSubspaceStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem isKC_Eab_of_posC {p q : ℕ} {c d : Ix p q} (h : posC c d) : IsKC (Eab c d) := by
  intro a b hab
  have hcd : sameBlock c d := by
    cases c <;> cases d <;> simp_all [posC, sameBlock]
  simp only [Eab, Matrix.single_apply]
  split_ifs with h1
  · obtain ⟨rfl, rfl⟩ := h1
    exact absurd hcd hab
  · rfl

theorem sameBlock_refl {p q : ℕ} (a : Ix p q) : sameBlock a a := by
  cases a <;> trivial

theorem isKC_Eab_diag {p q : ℕ} (c : Ix p q) : IsKC (Eab c c) := by
  intro a b hab
  simp only [Eab, Matrix.single_apply]
  split_ifs with h1
  · rcases h1 with ⟨rfl, rfl⟩
    exact absurd (sameBlock_refl _) hab
  · rfl

theorem mem_hwSub_iff {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) :
    v ∈ hwSub act μ ↔ (∀ c, act (Eab c c) v = ((μ c : ℚ) : ℂ) • v) ∧ ∀ c d, posC c d → act (Eab c d) v = 0 := by
  simp [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem hw_sup_le (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (hG : Good act) (N N' : Submodule ℂ V) (hN : KStable act N) (hN' : KStable act N') (μ : Ix p q → ℚ) :
    (N ⊔ N') ⊓ hwSub act μ ≤ (N ⊓ hwSub act μ) ⊔ (N' ⊓ hwSub act μ) := by
  intro v hv
  obtain ⟨hvs, hvh⟩ := Submodule.mem_inf.1 hv
  obtain ⟨n, hn, n', hn', rfl⟩ := Submodule.mem_sup.1 hvs
  rw [mem_hwSub_iff] at hvh
  obtain ⟨hw, hpos⟩ := hvh
  have hI : KStable act (N ⊓ N') := fun X hX w hw' =>
    Submodule.mem_inf.2 ⟨hN X hX w (Submodule.mem_inf.1 hw').1, hN' X hX w (Submodule.mem_inf.1 hw').2⟩
  have h1 : ∀ c, act (Eab c c) n - ((μ c : ℚ) : ℂ) • n ∈ N ⊓ N' := by
    intro c
    refine Submodule.mem_inf.2 ⟨N.sub_mem (hN _ (isKC_Eab_diag c) n hn) (N.smul_mem _ hn), ?_⟩
    have e : act (Eab c c) n - ((μ c : ℚ) : ℂ) • n = -(act (Eab c c) n' - ((μ c : ℚ) : ℂ) • n') := by
      have := hw c
      rw [map_add, smul_add] at this
      rw [neg_sub, sub_eq_sub_iff_add_eq_add, this, add_comm]
    rw [e]
    exact N'.neg_mem (N'.sub_mem (hN' _ (isKC_Eab_diag c) n' hn') (N'.smul_mem _ hn'))
  have h2 : ∀ c d, posC c d → act (Eab c d) n ∈ N ⊓ N' := by
    intro c d hcd
    refine Submodule.mem_inf.2 ⟨hN _ (isKC_Eab_of_posC hcd) n hn, ?_⟩
    have e : act (Eab c d) n = -(act (Eab c d) n') := by
      have := hpos c d hcd
      rw [map_add] at this
      exact eq_neg_of_add_eq_zero_left this
    rw [e]
    exact N'.neg_mem (hN' _ (isKC_Eab_of_posC hcd) n' hn')
  obtain ⟨n1, hn1N, hn1h, hd⟩ := GlobalTheory.T.exists_highestWeight_lift_mod_stable_subspace p q V act hG (N ⊓ N') N hI hN μ n hn h1 h2
  have hdN' : n + n' - n1 ∈ N' := by
    have : n + n' - n1 = (n - n1) + n' := by abel
    rw [this]
    exact N'.add_mem (Submodule.mem_inf.1 hd).2 hn'
  have hvH : n + n' ∈ hwSub act μ := (mem_hwSub_iff act μ _).2 ⟨hw, hpos⟩
  have : n + n' = n1 + (n + n' - n1) := by abel
  rw [this]
  exact Submodule.add_mem_sup (Submodule.mem_inf.2 ⟨hn1N, hn1h⟩)
    (Submodule.mem_inf.2 ⟨hdN', (hwSub act μ).sub_mem hvH hn1h⟩)

example : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), Good act → ∀ N N' : Submodule ℂ V, KStable act N → KStable act N' → ∀ μ : Ix p q → ℚ, (N ⊔ N') ⊓ hwSub act μ ≤ (N ⊓ hwSub act μ) ⊔ (N' ⊓ hwSub act μ) := hw_sup_le

end GlobalTheory.HoweR
