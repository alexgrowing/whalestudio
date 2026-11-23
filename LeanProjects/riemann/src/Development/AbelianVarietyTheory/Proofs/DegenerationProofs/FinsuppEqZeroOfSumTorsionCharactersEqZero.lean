import Mathlib

open Module

namespace GlobalTheory

theorem exists_eq_add_nsmul_of_torsion_characters_eq (k X : Type) [Field k] [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (N : ℕ) (ζ : k) (hN : 0 < N)
    (hζ : IsPrimitiveRoot ζ N) (α β : X)
    (h : ∀ t : Multiplicative X →* kˣ, t ^ N = 1 →
      t (Multiplicative.ofAdd α) = t (Multiplicative.ofAdd β)) :
    ∃ w, α = β + N • w := by
  classical
  have hu : IsUnit ζ := hζ.isUnit hN.ne'
  obtain ⟨u, rfl⟩ := hu
  have hu' : IsPrimitiveRoot u N := IsPrimitiveRoot.coe_units_iff.mp hζ
  let b := Module.Free.chooseBasis ℤ X
  have key : ∀ i, (N : ℤ) ∣ b.repr (α - β) i := by
    intro i
    let t : Multiplicative X →* kˣ :=
      { toFun := fun x => u ^ (b.repr (Multiplicative.toAdd x) i)
        map_one' := by simp
        map_mul' := by
          intro x y
          simp [zpow_add] }
    have ht : t ^ N = 1 := by
      refine MonoidHom.ext fun x => ?_
      have : (u ^ (b.repr (Multiplicative.toAdd x) i)) ^ N = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu'.pow_eq_one,
          one_zpow]
      rw [MonoidHom.pow_apply, MonoidHom.one_apply]
      exact this
    have h1 : u ^ (b.repr α i) = u ^ (b.repr β i) := h t ht
    rw [← hu'.zpow_eq_one_iff_dvd, map_sub, Finsupp.sub_apply, zpow_sub, h1, mul_inv_cancel]
  choose d hd using key
  refine ⟨∑ i, d i • b i, ?_⟩
  rw [← sub_eq_iff_eq_add', ← b.sum_repr (α - β), Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hd i, mul_smul, natCast_zsmul]

theorem finsupp_eq_zero_of_sum_torsion_characters_eq_zero :
    ∀ (k X : Type) [Field k] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (N : ℕ) (ζ : k), 0 < N → IsPrimitiveRoot ζ N → ∀ (M : Type) [AddCommGroup M] [Module k M] (c : X →₀ M), (∀ α ∈ c.support, ∀ β ∈ c.support, (∃ w, α = β + N • w) → α = β) → (∀ t : Multiplicative X →* kˣ, t ^ N = 1 → c.sum (fun α m => (t (Multiplicative.ofAdd α) : k) • m) = 0) → c = 0 := by
  intro k X _ _ _ _ N ζ hN hζ M _ _ c hc hsum
  classical
  let G : Subgroup (Multiplicative X →* kˣ) := (powMonoidHom N).ker
  let ev : c.support → (G →* k) := fun α =>
    { toFun := fun t => ((t : Multiplicative X →* kˣ) (Multiplicative.ofAdd (α : X)) : k)
      map_one' := by simp
      map_mul' := by
        intro s t
        simp }
  have hinj : Function.Injective ev := by
    intro α β hαβ
    apply Subtype.ext
    refine hc _ α.2 _ β.2
      (exists_eq_add_nsmul_of_torsion_characters_eq k X N ζ hN hζ _ _ fun t ht => ?_)
    exact Units.ext (DFunLike.congr_fun hαβ (⟨t, ht⟩ : G))
  have hli : LinearIndependent k (fun α : c.support => (ev α : G → k)) :=
    (linearIndependent_monoidHom G k).comp ev hinj
  ext α
  by_contra hα
  have hmem : α ∈ c.support := Finsupp.mem_support_iff.mpr hα
  apply hα
  rw [Finsupp.zero_apply, ← Module.forall_dual_apply_eq_zero_iff k]
  intro φ
  refine Fintype.linearIndependent_iff.mp hli (fun β => φ (c β)) ?_ ⟨α, hmem⟩
  funext t
  have h0 := congrArg φ (hsum t t.2)
  rw [Finsupp.sum, map_sum, map_zero, ← Finset.sum_coe_sort] at h0
  rw [Finset.sum_apply, Pi.zero_apply, ← h0]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
  rfl

end GlobalTheory
