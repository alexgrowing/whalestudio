import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisAdaptedLatticeSubspace

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem tate_free_of_card :
    ∀ (p : ℕ) [Fact p.Prime] (M : Type) [CommGroup M] (r : ℕ), (∀ n : ℕ, Nat.card {x : M // x ^ p ^ n = 1} = p ^ (r * n)) → Nonempty (Tate p M ≃ₗ[ℤ_[p]] (Fin r → ℤ_[p])) ∧ (∀ (n : ℕ) (x : M), x ^ p ^ n = 1 → ∃ t : Tate p M, t.lev n = x) ∧ ∀ (n : ℕ) (t : Tate p M), t.lev n = 1 ↔ ∃ s : Tate p M, t = (p : ℤ_[p]) ^ n • s := by
  intro p _ M _ r h
  obtain ⟨T, _, _, π, hfree, hfin, hrk, hs, h0, hsm, hon, hker, huniq⟩ :=
    GlobalTheory.exists_tateModule_of_card (Additive M) p r (fun n => by
      rw [← h n]
      exact Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun x => Iff.rfl))
  have hkill : ∀ n x, p ^ n • π n x = 0 := fun n x => by
    induction n with
    | zero => simp [h0]
    | succ n ih => rw [pow_succ, mul_smul, hs, ih]
  let f : T →ₗ[ℤ_[p]] Tate p M :=
    { toFun := fun x => Tate.mk (fun n => Additive.toMul (π n x)) fun n =>
        ⟨congrArg Additive.toMul (hkill n x), congrArg Additive.toMul (hs n x)⟩
      map_add' := fun x y => Tate.ext fun n => congrArg Additive.toMul (map_add (π n) x y)
      map_smul' := fun a x => Tate.ext fun n => congrArg Additive.toMul (hsm n a x) }
  have hf : ∀ x n, (f x).lev n = Additive.toMul (π n x) := fun _ _ => rfl
  have hu : ∀ t : Tate p M, ∃! x, ∀ n, π n x = Additive.ofMul (t.lev n) := fun t =>
    huniq (fun n => Additive.ofMul (t.lev n))
      (by have := t.lev_pow 0
          rw [pow_zero, pow_one] at this
          rw [this]; rfl)
      (fun n => congrArg Additive.ofMul (t.lev_succ n))
  have hsurj : Function.Surjective f := fun t => by
    obtain ⟨x, hx, -⟩ := hu t
    exact ⟨x, Tate.ext fun n => by rw [hf, hx]; rfl⟩
  have hinj : Function.Injective f := fun x y hxy =>
    (hu (f y)).unique (fun n => by rw [← hxy]; rfl) (fun n => rfl)
  refine ⟨⟨(LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).symm.trans
    (LinearEquiv.ofFinrankEq _ _ (by simpa using hrk))⟩, fun n x hx => ?_, fun n t => ?_⟩
  · obtain ⟨y, hy⟩ := hon n (Additive.ofMul x) (congrArg Additive.ofMul hx)
    exact ⟨f y, by rw [hf, hy]; rfl⟩
  · obtain ⟨x, rfl⟩ := hsurj t
    have key : ∀ y : T, f (p ^ n • y) = (p : ℤ_[p]) ^ n • f y := fun y => by
      rw [map_nsmul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    refine Iff.trans (hker n x) ⟨?_, ?_⟩
    · rintro ⟨y, rfl⟩
      exact ⟨f y, key y⟩
    · rintro ⟨s, hs'⟩
      obtain ⟨y, rfl⟩ := hsurj s
      exact ⟨y, hinj (hs'.trans (key y).symm)⟩

end GlobalTheory
