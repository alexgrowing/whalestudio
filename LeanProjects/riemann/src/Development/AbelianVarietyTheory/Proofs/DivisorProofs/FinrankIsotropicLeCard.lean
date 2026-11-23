import Mathlib

open Matrix

theorem GlobalTheory.isotropic_finrank_le_card (K : Type) [Field K] (κ : Type) [Fintype κ]
    (L : Submodule K ((κ → K) × (κ → K)))
    (hL : ∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) :
    Module.finrank K L ≤ Fintype.card κ := by
  classical
  let ψ : ((κ → K) × (κ → K)) →ₗ[K] Module.Dual K ((κ → K) × (κ → K)) :=
    LinearMap.mk₂ K (fun a b => a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2)
      (by intro a a' b; simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
      (by intro c a b; simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
      (by intro a b b'; simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
      (by intro c a b; simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
  have hψ : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro a ha
    rw [LinearMap.mem_ker] at ha
    have h1 : ∀ i, a.1 i = 0 := by
      intro i
      have := LinearMap.congr_fun ha ((0 : κ → K), Pi.single i 1)
      simpa [ψ, dotProduct_single] using this
    have h2 : ∀ i, a.2 i = 0 := by
      intro i
      have := LinearMap.congr_fun ha ((Pi.single i 1 : κ → K), 0)
      simpa [ψ, single_dotProduct] using this
    ext i
    · exact h1 i
    · exact h2 i
  let g : L →ₗ[K] L.dualAnnihilator :=
    (ψ.comp L.subtype).codRestrict L.dualAnnihilator (by
      intro x
      rw [Submodule.mem_dualAnnihilator]
      intro b hb
      show (x : (κ → K) × (κ → K)).1 ⬝ᵥ b.2 - b.1 ⬝ᵥ (x : (κ → K) × (κ → K)).2 = 0
      rw [hL _ x.2 b hb, sub_self])
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply hψ
    have := congrArg Subtype.val hxy
    simpa [g] using this
  have h3 := LinearMap.finrank_le_finrank_of_injective hg
  have h4 := Subspace.finrank_add_finrank_dualAnnihilator_eq L
  have h5 : Module.finrank K ((κ → K) × (κ → K)) = Fintype.card κ + Fintype.card κ := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
  omega
