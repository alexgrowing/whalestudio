import Formalism.CyclotomicNorms.StatementA

open Module

noncomputable section

namespace Formalism.CyclotomicNorms

namespace CycleChains

universe u

variable {k : Type*} [Field k]

def resR {G V : Type*} [Group G] [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (W : Submodule k V) (hW : ∀ g, ∀ x ∈ W, ρ g x ∈ W) (g : G) : W →ₗ[k] W :=
  (ρ g).restrict (hW g)

theorem chi_mul {G V : Type*} [Group G] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (N : ℕ) (I : Subgroup G) (χ : Fin N → G → k)
    (flag : Fin (N + 1) → Submodule k V)
    (hdim : ∀ i : Fin (N + 1), finrank k (flag i) = i)
    (hmono : ∀ i : Fin N, flag i.castSucc ≤ flag i.succ)
    (hstab : ∀ i, ∀ x ∈ flag i, ∀ y ∈ I, ρ y x ∈ flag i)
    (hchi : ∀ i : Fin N, ∀ x ∈ flag i.succ, ∀ y ∈ I, ρ y x - χ i y • x ∈ flag i.castSucc)
    (i : Fin N) : χ i 1 = 1 ∧ ∀ y ∈ I, ∀ z ∈ I, χ i (y * z) = χ i y * χ i z := by
  have hlt : flag i.castSucc < flag i.succ := by
    refine lt_of_le_of_ne (hmono i) fun h => ?_
    have := congrArg (fun S : Submodule k V => finrank k S) h
    simp only [hdim, Fin.val_castSucc, Fin.val_succ] at this
    omega
  obtain ⟨x, hx, hxn⟩ := SetLike.exists_of_lt hlt
  have hz : ∀ a : k, a • x ∈ flag i.castSucc → a = 0 := by
    intro a ha
    by_contra hne
    exact hxn ((Submodule.smul_mem_iff _ hne).mp ha)
  refine ⟨?_, ?_⟩
  · have h := hchi i x hx 1 I.one_mem
    simp only [map_one, Module.End.one_apply] at h
    have : (1 - χ i 1) • x ∈ flag i.castSucc := by rwa [sub_smul, one_smul]
    have := hz _ this
    rw [sub_eq_zero] at this
    exact this.symm
  · intro y hy z hz'
    have h1 := hchi i x hx (y * z) (I.mul_mem hy hz')
    have h2 := hchi i x hx y hy
    have h3 := hchi i x hx z hz'
    have h4 := hstab i.castSucc _ h3 y hy
    have key : (χ i (y * z) - χ i y * χ i z) • x =
        (ρ y (ρ z x - χ i z • x) + χ i z • (ρ y x - χ i y • x)) -
          (ρ (y * z) x - χ i (y * z) • x) := by
      rw [map_mul, Module.End.mul_apply, map_sub, map_smul]
      module
    have hm : (χ i (y * z) - χ i y * χ i z) • x ∈ flag i.castSucc := by
      rw [key]
      exact Submodule.sub_mem _ (Submodule.add_mem _ h4 (Submodule.smul_mem _ _ h2)) h1
    have := hz _ hm
    rwa [sub_eq_zero] at this

end CycleChains

end Formalism.CyclotomicNorms
