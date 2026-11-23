import Mathlib

open IsLocalRing Polynomial

theorem UpperTheory.V.Th.Sp.phi :
    ∀ (S M O X : Type) [CommRing S] [AddCommGroup M] [Module S M] [Module.Projective S M] [CommRing O] [AddCommGroup X] [Module O X] (th : S →+* O) (ell : S →+ X) (lam : M →+ O), (∀ a b, ell (a * b) = th a • ell b + th b • ell a) → (∀ (σ : S) m, lam (σ • m) = th σ * lam m) → ∃ Φ : M →+ X, ∀ (σ : S) m, Φ (σ • m) = th σ • Φ m + lam m • ell σ := by
  intro S M O X _ _ _ _ _ _ _ th ell lam hell hlam
  obtain ⟨s, hs⟩ := Module.Projective.out (R := S) (P := M)
  have key : ∀ m, lam m = (s m).sum (fun i a => th a * lam i) := by
    intro m
    conv_lhs => rw [← hs m]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finsupp.sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [hlam]
  refine ⟨{ toFun := fun m => (s m).sum (fun i a => lam i • ell a),
            map_zero' := by simp,
            map_add' := ?_ }, ?_⟩
  · intro m n
    simp only [map_add]
    exact Finsupp.sum_add_index' (fun i => by simp) (fun i a b => by simp [smul_add])
  · intro σ m
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_smul]
    rw [Finsupp.sum_smul_index' (fun i => by simp), key m, Finsupp.sum, Finsupp.sum, Finsupp.sum,
      Finset.smul_sum, Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_eq_mul, hell, smul_add, smul_smul, smul_smul, smul_smul, mul_comm (lam i) (th σ),
      mul_comm (lam i) (th ((s m) i))]
