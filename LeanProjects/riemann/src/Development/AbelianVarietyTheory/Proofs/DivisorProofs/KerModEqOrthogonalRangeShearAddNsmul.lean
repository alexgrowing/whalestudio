import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivOfIsometryApply
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem ker_mod_eq_perp_range_add : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ), 0 < n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) → ∀ t : Z →ₗ[𝓞 E] D.La, (∀ z : Z, t z - z ∈ perp D Z') →
    (∀ z z' : Z, D.EF (t z) (t z') = 0) → (∀ (z : Z) (a : D.La), (∃ e, y a = n • e) → (n : ℤ) ∣ D.EF (t z) a) →
    ∀ a, (∃ e, y a = n • e) ↔ ∃ b ∈ perp D (LinearMap.range t), ∃ e, a = b + n • e := by
  intro E _ _ _ H D X _ _ y n hn Z Z' h hsurj t ht hiso hdiv a
  have hW : IsOpp D (LinearMap.range t) Z' := (h.symm.shear t ht hiso).symm

  have hdivZ : ∀ b ∈ Z', (∀ z : Z, (n : ℤ) ∣ D.EF (t z) b) → ∃ b'', b = n • b'' := by
    intro b hb hbd
    have hx : ∀ x : LinearMap.range t, (n : ℤ) ∣ D.EF x b := by
      rintro ⟨_, z, rfl⟩
      exact hbd z
    let φ : LinearMap.range t →+ ℤ := AddMonoidHom.mk' (fun x => D.EF x b / n) fun x x' => by
      simp only [Submodule.coe_add, map_add, LinearMap.add_apply]
      exact Int.add_ediv_of_dvd_left (hx x)
    obtain ⟨b'', hb'', -⟩ := hW.2.2.1 φ
    refine ⟨b'', ?_⟩
    have h0 : (n • (b'' : D.La)) - b = 0 := by
      refine hW.eq_zero (sub_mem (Z'.nsmul_mem b''.2 n) hb) fun w hw => ?_
      have e1 := hb'' ⟨w, hw⟩
      simp only [φ, AddMonoidHom.mk'_apply] at e1
      have e2 : (n : ℤ) ∣ D.EF w b := hx ⟨w, hw⟩
      rw [ef_swap, map_sub, map_nsmul, e1, nsmul_eq_mul, Int.mul_ediv_cancel' e2]
      simp
    exact (sub_eq_zero.1 h0).symm
  have hperp0 : ∀ (k : D.La), k ∈ perp D (LinearMap.range t) → ∀ z : Z, D.EF (t z) k = 0 := by
    intro k hk z
    rw [ef_swap, hk _ ⟨z, rfl⟩, neg_zero]
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨b, hb, hk⟩ := hW.exists_sub_mem_perp a
    obtain ⟨b'', hb''⟩ := hdivZ b hb fun z => by
      have h1 := hdiv z a ⟨e, he⟩
      have h2 : D.EF (t z) b = D.EF (t z) a - D.EF (t z) (a - b) := by
        rw [map_sub]; ring
      rw [h2, hperp0 _ hk z, sub_zero]
      exact h1
    refine ⟨a - b, hk, b'', ?_⟩
    rw [← hb'', sub_add_cancel]
  · rintro ⟨k, hk, e, rfl⟩
    obtain ⟨b, hb, e₁, hb1⟩ := hsurj (y k)
    obtain ⟨b'', rfl⟩ := hdivZ b hb fun z => by
      have h1 := hdiv z (k - b) ⟨-e₁, by rw [map_sub, hb1, smul_neg]; abel⟩
      rw [map_sub, hperp0 _ hk z, zero_sub, Int.dvd_neg] at h1
      exact h1
    refine ⟨y b'' - e₁ + y e, ?_⟩
    rw [map_nsmul] at hb1
    rw [map_add, map_nsmul, smul_add, smul_sub, hb1]
    abel

end GlobalTheory.LowFilt
