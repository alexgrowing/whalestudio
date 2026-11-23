import Mathlib

namespace DiscreteGroups.sglob.DzType

theorem addChar_eq_trace {g : ℕ} [Fact g.Prime] {K : Type} [Field K] [Finite K] [Algebra (ZMod g) K]
    (ψ₀ : AddChar (ZMod g) Circle) (h₀ : ψ₀ ≠ 1) (ψb : AddChar K Circle) :
    ∃ β : K, ∀ x : K, ψb x = ψ₀ (Algebra.trace (ZMod g) K (β * x)) := by
  classical
  have := Fintype.ofFinite K
  let F : K → AddChar K Circle := fun β =>
    (ψ₀.compAddMonoidHom (Algebra.trace (ZMod g) K).toAddMonoidHom).mulShift β
  have hF : ∀ β x, F β x = ψ₀ (Algebra.trace (ZMod g) K (β * x)) := fun β x => rfl
  have hinj : Function.Injective F := by
    intro a b hab
    by_contra hne
    have hd : a - b ≠ 0 := sub_ne_zero.2 hne
    apply h₀
    ext c
    obtain ⟨y, rfl⟩ := Algebra.trace_surjective (ZMod g) K c
    have h1 := DFunLike.congr_fun hab ((a - b)⁻¹ * y)
    rw [hF, hF] at h1
    have h2 : y = a * ((a - b)⁻¹ * y) - b * ((a - b)⁻¹ * y) := by
      rw [← sub_mul, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]
    rw [h2, map_sub, AddChar.map_sub_eq_div, h1, div_self', AddChar.one_apply]
  have hfin : Finite (AddChar K Circle) := Finite.of_equiv _ (AddChar.circleEquivComplex (α := K)).toEquiv.symm
  have hc : Nat.card K = Nat.card (AddChar K Circle) := by
    rw [Nat.card_congr (AddChar.circleEquivComplex (α := K)).toEquiv, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, AddChar.card_eq]
  obtain ⟨β, hβ⟩ := ((Nat.bijective_iff_injective_and_card F).2 ⟨hinj, hc⟩).2 ψb
  exact ⟨β, fun x => by rw [← hβ, hF]⟩

theorem algebraMap_norm_eq_pow {g n : ℕ} [Fact g.Prime] {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Nat.card K = g ^ n) (x : K) :
    algebraMap (ZMod g) K (Algebra.norm (ZMod g) x) = x ^ ((g ^ n - 1) / (g - 1)) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (Fact.out : g.Prime).ne_zero)
  rw [FiniteField.algebraMap_norm_eq_pow, hK, Nat.card_zmod]

theorem char_orbit {G : Type*} [Group G] (α β : G →* ℂˣ) (N : ℕ) (hN : 0 < N) (hα : ∀ t, α t ^ N = 1) (q : ℕ)
    (h1 : ∀ t, ∃ j : ℕ, β t = α t ^ q ^ j) : ∃ j : ℕ, ∀ t, β t = α t ^ q ^ j := by
  have : NeZero N := ⟨hN.ne'⟩
  have hle : α.range ≤ rootsOfUnity N ℂ := by
    rintro _ ⟨t, rfl⟩
    exact (mem_rootsOfUnity _ _).2 (hα t)
  have : Finite α.range := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  obtain ⟨⟨_, t₀, rfl⟩, h0⟩ := IsCyclic.exists_generator (α := α.range)
  obtain ⟨j, hj⟩ := h1 t₀
  refine ⟨j, fun t => ?_⟩
  obtain ⟨k, hk⟩ := h0 ⟨α t, t, rfl⟩
  have hk' : α t₀ ^ k = α t := congrArg Subtype.val hk
  obtain ⟨i, hi⟩ := h1 (t * (t₀ ^ k)⁻¹)
  rw [map_mul α, map_inv α, map_zpow α, hk', mul_inv_cancel, one_pow, map_mul, map_inv, map_zpow,
    mul_inv_eq_one] at hi
  rw [hi, hj, ← hk', ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

end DiscreteGroups.sglob.DzType
