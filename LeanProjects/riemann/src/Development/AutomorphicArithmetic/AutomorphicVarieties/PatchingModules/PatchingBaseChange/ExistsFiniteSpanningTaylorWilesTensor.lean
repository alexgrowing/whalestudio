import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SinfRel
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SpFin
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem tens_fin {Λ B S R M : Type} [CommRing Λ] [CommRing B] [CommRing S] [CommRing R] [Algebra B S]
    [AddCommGroup M] [Module B M] [Module Λ M] [Module.Finite B S] [Module.Finite Λ M]
    (lam : Λ → B) (hl : ∀ (a : Λ) (m : M), a • m = lam a • m) (θ : R →+* S)
    (hθ : ∀ a : Λ, ∃ t : R, θ t = algebraMap B S (lam a)) :
    ∃ s : Finset (S ⊗[B] M), ∀ z, ∃ c : S ⊗[B] M → R, z = ∑ g ∈ s, θ (c g) • g := by
  classical
  obtain ⟨a, ha⟩ := Module.Finite.fg_top (R := B) (M := S)
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := Λ) (M := M)
  let s : Finset (S ⊗[B] M) := Finset.image₂ (fun x y => x ⊗ₜ[B] y) a t
  refine ⟨s, ?_⟩
  have h1 : ∀ x ∈ a, ∀ y : M, x ⊗ₜ[B] y ∈ Submodule.span θ.range (s : Set (S ⊗[B] M)) := by
    intro x hx y
    have hy : y ∈ Submodule.span Λ (t : Set M) := ht ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image₂_of_mem hx hy))
    | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add y y' _ _ h h' => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ h h'
    | smul c y _ h =>
      obtain ⟨w, hw⟩ := hθ c
      rw [hl, TensorProduct.tmul_smul, ← algebraMap_smul S]
      exact Submodule.smul_mem _ (⟨algebraMap B S (lam c), w, hw⟩ : θ.range) h
  have h2 : ∀ x : S, ∀ y : M, x ⊗ₜ[B] y ∈ Submodule.span θ.range (s : Set (S ⊗[B] M)) := by
    intro x
    have hx : x ∈ Submodule.span B (a : Set S) := ha ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => exact h1 x hx
    | zero => intro y; rw [TensorProduct.zero_tmul]; exact Submodule.zero_mem _
    | add x x' _ _ h h' => intro y; rw [TensorProduct.add_tmul]; exact Submodule.add_mem _ (h y) (h' y)
    | smul c x _ h => intro y; rw [TensorProduct.smul_tmul]; exact h _
  intro z
  have hz : z ∈ Submodule.span θ.range (s : Set (S ⊗[B] M)) := by
    induction z using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul x y => exact h2 x y
    | add z z' h h' => exact Submodule.add_mem _ h h'
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 hz
  choose c hc using fun g => (f g).2
  refine ⟨c, ?_⟩
  rw [← hf]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [hc]
  rfl

theorem UpperTheory.V.Pa.BC.exists_finite_spanning_taylorWiles_tensor :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (σ : Type) (D : ℕ) (b : TWBase u J σ D) (G : Glob l L) (h : G.Hom G0) (q : ℕ) (ut : Fin q → Fin n → O) (N : ℕ) (A : TWRing b h ut N) (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀) (ex : ℕ) (m : TWMaps Nq ph ta A ex), ∃ s : Finset (SpAt u (fun j => h.p₀ (ph j)) ut ⊗[B] b.M), ∀ z, ∃ c : _ → A.R, z = ∑ g ∈ s, m.θ (c g) • g := by
  intro l _ L G0 n O _ _ _ r B _ _ _ u J σ D b G h q ut N A Nq ph ta ex m
  haveI : Module.Finite B (SpAt u (fun j => h.p₀ (ph j)) ut) := (UpperTheory.V.Pa.BC.sp_fin B q n _ _).1
  haveI := b.fin
  exact tens_fin (Λ := abelian₂ O σ D) (fun a => b.lam a) b.smul_lam m.θ.toRingHom fun a =>
    ⟨A.s (MvPowerSeries.C a), by
      have := m.theta_coefficientMap_eq (MvPowerSeries.C a)
      rw [MvPowerSeries.constantCoeff_C] at this
      exact this⟩
