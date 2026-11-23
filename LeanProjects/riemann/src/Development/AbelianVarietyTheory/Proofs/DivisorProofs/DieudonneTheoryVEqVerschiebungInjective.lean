import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFunctorBaseFunctorPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFrobeniusTwistBijectiveRelFrobeniusStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem theory_V_verschiebung : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), Function.Injective (T.F G) ∧ Function.Injective (T.V G) ∧ (∀ m, T.smap (frobProj (p_eq_zero p k) G) (T.V G m) = T.map (verschiebung (p_eq_zero p k) G) m) ∧ (∀ (H : PDivGroup p k) (φ : T.M H →ₗ[(WittVector p k)] T.M G), (∀ m, φ (T.F H m) = T.F G (φ m)) → ∀ m, φ (T.V H m) = T.V G (φ m)) ∧ ∀ (H : PDivGroup p k) (f : G ⟶ H) (m : T.M H), T.map f (T.V H m) = T.V G (T.map f m) := by
  intro p _ T k _ _ _ G

  have tor : ∀ (K : PDivGroup p k) (m : T.M K), p • m = 0 → m = 0 := by
    intro K m hm
    have h := (GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k K K K trivial trivial trivial).2.2.2.2.2.2.2.2 1 m
    exact h (by simpa using hm)
  have Finj : ∀ K : PDivGroup p k, Function.Injective (T.F K) := by
    intro K x y hxy
    have h1 : p • x = p • y := by rw [← T.V_F K x, ← T.V_F K y]; exact congrArg _ hxy
    have : p • (x - y) = 0 := by rw [smul_sub, h1, sub_self]
    exact sub_eq_zero.mp (tor K _ this)
  have Vinj : ∀ K : PDivGroup p k, Function.Injective (T.V K) := by
    intro K x y hxy
    have h1 : p • x = p • y := by rw [← T.F_V K x, ← T.F_V K y]; exact congrArg _ hxy
    have : p • (x - y) = 0 := by rw [smul_sub, h1, sub_self]
    exact sub_eq_zero.mp (tor K _ this)
  have comm : ∀ (H : PDivGroup p k) (φ : T.M H →ₗ[(WittVector p k)] T.M G),
      (∀ m, φ (T.F H m) = T.F G (φ m)) → ∀ m, φ (T.V H m) = T.V G (φ m) := by
    intro H φ hφ m
    apply Finj G
    rw [← hφ, T.F_V H m, T.F_V G, map_nsmul]
  refine ⟨Finj G, Vinj G, ?_, comm, ?_⟩
  · intro m
    have ht := GlobalTheory.T.dieudonne_frobeniusTwist_bijective_relFrobenius p T.base k G
    obtain ⟨n, hn⟩ := ht.1.2 (T.map (verschiebung (p_eq_zero p k) G) m)
    have hF : T.F G n = p • m := ht.2.2 m n hn
    have : n = T.V G m := Finj G (by rw [hF, T.F_V])
    rw [← this]; exact hn
  · intro H f m
    exact comm H (T.map f)
      (fun m => (GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k G H H trivial trivial trivial).2.2.2.2.2.2.1 f m) m

end GlobalTheory.Dieu
