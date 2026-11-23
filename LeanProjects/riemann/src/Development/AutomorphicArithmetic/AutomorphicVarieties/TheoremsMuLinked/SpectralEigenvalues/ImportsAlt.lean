import Mathlib

open IsLocalRing Polynomial

theorem UpperTheory.V.Th.Sp.der :
    ∀ (O S T M X : Type) [CommRing O] [CommRing S] [CommRing T] [Algebra O S] [Algebra O T] [AddCommGroup M] [Module S M] [Module T M] [SMulCommClass S T M] [AddCommGroup X] [Module O X] (th : S →ₐ[O] O) (x : T →ₐ[O] O) (ell : S →ₗ[O] X) (lam : M →+ O) (Φ : M →+ X) (t : T) (v : M), (∀ (o : O) (m : M), algebraMap O S o • m = algebraMap O T o • m) → ell 1 = 0 → (∀ (σ : S) m, lam (σ • m) = th σ * lam m) → (∀ (σ : S) m, Φ (σ • m) = th σ • Φ m + lam m • ell σ) → (∀ a, x a = 0 → ∀ m : M, (t * a) • m ∈ (RingHom.ker th • ⊤ : Submodule S M)) → ∃ del : T →ₗ[O] X, (∀ a b, del (a * b) = x a • del b + x b • del a) ∧ (∀ (τ : T) (σ : S), (∀ m : M, τ • m = σ • m) → x τ = th σ → del τ = lam ((t * t) • v) • ell σ) ∧ ∀ a, x a = 0 → (∀ m : M, (t * a) • m = 0) → del a = 0 := by
  intro O S T M X _ _ _ _ _ _ _ _ _ _ _ th x ell lam Φ t v hO hell1 hlam hΦ hker
  set m0 : M := (t * t) • v with hm0
  have hell : ∀ o : O, ell (algebraMap O S o) = 0 := by
    intro o
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hell1, smul_zero]
  have hΦO : ∀ (o : O) (m : M), Φ (algebraMap O S o • m) = o • Φ m := by
    intro o m
    rw [hΦ, AlgHom.commutes, Algebra.algebraMap_self_apply, hell, smul_zero, add_zero]
  have hlamK : ∀ m ∈ (RingHom.ker th • ⊤ : Submodule S M), lam m = 0 := by
    intro m hm
    refine Submodule.smul_induction_on (p := fun m => lam m = 0) hm ?_ ?_
    · intro σ hσ n _
      rw [hlam, (RingHom.mem_ker).1 hσ, zero_mul]
    · intro y z hy hz
      rw [map_add, hy, hz, add_zero]
  have hΦK : ∀ a, x a = 0 → ∀ m ∈ (RingHom.ker th • ⊤ : Submodule S M), Φ ((t * a) • m) = 0 := by
    intro a ha m hm
    refine Submodule.smul_induction_on (p := fun m => Φ ((t * a) • m) = 0) hm ?_ ?_
    · intro σ hσ n _
      rw [← smul_comm σ (t * a) n, hΦ, (RingHom.mem_ker).1 hσ, zero_smul, zero_add,
        hlamK _ (hker a ha n), zero_smul]
    · intro y z hy hz
      rw [smul_add, map_add, hy, hz, add_zero]
  have hx0 : ∀ a, x (a - algebraMap O T (x a)) = 0 := by
    intro a
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
  refine ⟨{ toFun := fun a => Φ ((a - algebraMap O T (x a)) • m0), map_add' := ?_, map_smul' := ?_ }, ?_, ?_, ?_⟩
  · intro a b
    rw [map_add x, map_add (algebraMap O T),
      show a + b - (algebraMap O T (x a) + algebraMap O T (x b)) = (a - algebraMap O T (x a)) + (b - algebraMap O T (x b)) by ring,
      add_smul, map_add]
  · intro o a
    have h : o • a - algebraMap O T (x (o • a)) = algebraMap O T o * (a - algebraMap O T (x a)) := by
      rw [map_smul x, smul_eq_mul, Algebra.smul_def, map_mul]
      ring
    show Φ ((o • a - algebraMap O T (x (o • a))) • m0) = o • Φ ((a - algebraMap O T (x a)) • m0)
    rw [h, mul_smul, ← hO, hΦO]
  · intro a b
    show Φ ((a * b - algebraMap O T (x (a * b))) • m0) = x a • Φ ((b - algebraMap O T (x b)) • m0) + x b • Φ ((a - algebraMap O T (x a)) • m0)
    have h : a * b - algebraMap O T (x (a * b)) = (a - algebraMap O T (x a)) * (b - algebraMap O T (x b)) + algebraMap O T (x a) * (b - algebraMap O T (x b)) + algebraMap O T (x b) * (a - algebraMap O T (x a)) := by
      rw [map_mul, map_mul]
      ring
    have hz : Φ (((a - algebraMap O T (x a)) * (b - algebraMap O T (x b))) • m0) = 0 := by
      rw [hm0, ← mul_smul,
        show (a - algebraMap O T (x a)) * (b - algebraMap O T (x b)) * (t * t) = (t * (a - algebraMap O T (x a))) * (t * (b - algebraMap O T (x b))) by ring,
        mul_smul]
      exact hΦK _ (hx0 a) _ (hker _ (hx0 b) v)
    rw [h, add_smul, add_smul, map_add, map_add, hz, zero_add, mul_smul (algebraMap O T (x a)), mul_smul (algebraMap O T (x b)), ← hO, ← hO, hΦO, hΦO]
  · intro τ σ hτσ hxτ
    show Φ ((τ - algebraMap O T (x τ)) • m0) = lam m0 • ell σ
    rw [sub_smul, hτσ, hxτ, ← hO, ← sub_smul, hΦ, map_sub th, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self,
      zero_smul, zero_add, map_sub ell, hell, sub_zero]
  · intro a ha hta
    show Φ ((a - algebraMap O T (x a)) • m0) = 0
    rw [ha, map_zero, sub_zero, hm0, ← mul_smul, show a * (t * t) = (t * a) * t by ring, mul_smul, hta, map_zero]
