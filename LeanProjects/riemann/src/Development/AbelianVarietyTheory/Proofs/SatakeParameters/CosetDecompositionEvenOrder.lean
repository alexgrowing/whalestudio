import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

namespace GlobalTheory

theorem pow_mem_iff_even_of_index_two_notMem {G : Type} [Group G] (H : Subgroup G) (hH : H.index = 2)
    (a : G) (ha : a ∉ H) (k : ℕ) : a ^ k ∈ H ↔ Even k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Subgroup.mul_mem_iff_of_index_two hH, Nat.even_add_one, ih]
    simp [ha]

theorem frobenius_orbit_positions_comm (G : Type) [CommGroup G] [Finite G] (H : Subgroup G) (φ c : G)
    (hH : H.index = 2) (hφ : φ ∉ H) (hc : c ∉ H) (hcc : c * c = 1) (hcZ : c ∉ Subgroup.zpowers φ) :
    2 ≤ orderOf φ ∧ Even (orderOf φ) ∧ ∃ (N : ℕ) (g : Fin N → G) (pos : (Σ _ : Fin N, Fin (orderOf φ)) ≃ H), 0 < N ∧ (∀ v s, (pos ⟨v, s⟩ : G) = φ ^ s.val * g v * c ^ s.val) ∧ (∀ v v', g v' * (g v)⁻¹ ∈ Subgroup.zpowers φ → v = v') ∧ (∀ v v', g v' * c * (g v)⁻¹ ∉ Subgroup.zpowers φ) ∧ ∀ x : G, ∃ v, g v * x⁻¹ ∈ Subgroup.zpowers φ ∨ g v * c * x⁻¹ ∈ Subgroup.zpowers φ := by
  classical
  have hφk := pow_mem_iff_even_of_index_two_notMem H hH φ hφ
  have hck := pow_mem_iff_even_of_index_two_notMem H hH c hc
  have hev : Even (orderOf φ) := (hφk _).1 (by rw [pow_orderOf_eq_one]; exact H.one_mem)
  have hpos : 0 < orderOf φ := orderOf_pos φ
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have hce : ∀ k : ℕ, Even k → c ^ k = 1 := by
    rintro k ⟨m, rfl⟩
    rw [pow_add, ← mul_pow, hcc, one_pow]
  have hco : ∀ k : ℕ, ¬ Even k → c ^ k = c := by
    intro k hk
    obtain ⟨m, rfl⟩ := Nat.not_even_iff_odd.1 hk
    rw [pow_succ, hce _ (even_two_mul m), one_mul]
  refine ⟨by obtain ⟨m, hm⟩ := hev; omega, hev, ?_⟩
  set Z := Subgroup.zpowers φ with hZ
  let D : Subgroup G := Z ⊔ Subgroup.zpowers c
  have hZD : Z ≤ D := le_sup_left
  have hcD : c ∈ D := (le_sup_right : Subgroup.zpowers c ≤ D) (Subgroup.mem_zpowers c)
  have hφD : φ ∈ D := hZD (Subgroup.mem_zpowers φ)
  have hD : ∀ x ∈ D, x ∈ Z ∨ x * c ∈ Z := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
    obtain ⟨k, rfl⟩ := (mem_powers_iff_mem_zpowers.2 hz : z ∈ Submonoid.powers c)
    by_cases hk : Even k
    · left; simpa [hce k hk] using hy
    · right; simpa [hco k hk, mul_assoc, hcc] using hy
  have hZpow : ∀ x ∈ Z, ∃ s : Fin (orderOf φ), φ ^ s.val = x := by
    intro x hx
    obtain ⟨k, rfl⟩ := (mem_powers_iff_mem_zpowers.2 hx : x ∈ Submonoid.powers φ)
    exact ⟨⟨k % orderOf φ, Nat.mod_lt _ hpos⟩, pow_mod_orderOf φ k⟩
  have hr : ∀ q : G ⧸ D, ∃ a : G, a ∈ H ∧ (a : G ⧸ D) = q := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    by_cases ha : a ∈ H
    · exact ⟨a, ha, rfl⟩
    · refine ⟨a * c, ?_, ?_⟩
      · rw [Subgroup.mul_mem_iff_of_index_two hH]; simp [ha, hc]
      · exact QuotientGroup.mk_mul_of_mem a hcD
  choose r hrH hrq using hr
  let e : Fin (Nat.card (G ⧸ D)) ≃ G ⧸ D := (Finite.equivFin (G ⧸ D)).symm
  let g : Fin (Nat.card (G ⧸ D)) → G := fun v => r (e v)
  have hgH : ∀ v, g v ∈ H := fun v => hrH _
  have key : ∀ v v', g v' * (g v)⁻¹ ∈ D → v = v' := by
    intro v v' h
    apply e.injective
    rw [← hrq (e v), ← hrq (e v'), QuotientGroup.eq, mul_comm]
    exact h
  have cover : ∀ x : G, ∃ v, g v * x⁻¹ ∈ D := by
    intro x
    refine ⟨e.symm (x : G ⧸ D), ?_⟩
    have h := hrq (x : G ⧸ D)
    rw [eq_comm, QuotientGroup.eq, mul_comm] at h
    simpa [g] using h
  let f : (Σ _ : Fin (Nat.card (G ⧸ D)), Fin (orderOf φ)) → H := fun p =>
    ⟨φ ^ p.2.val * g p.1 * c ^ p.2.val, by
      rw [Subgroup.mul_mem_iff_of_index_two hH, H.mul_mem_cancel_right (hgH _), hφk, hck]⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨v, s⟩ ⟨v', t⟩ h
      have h' : φ ^ s.val * g v * c ^ s.val = φ ^ t.val * g v' * c ^ t.val := congrArg Subtype.val h
      have hv : v = v' := by
        apply key
        have : g v' * (g v)⁻¹ = φ ^ s.val * c ^ s.val * (φ ^ t.val * c ^ t.val)⁻¹ := by
          rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]
          calc g v' * (φ ^ t.val * c ^ t.val) = φ ^ t.val * g v' * c ^ t.val := by ac_rfl
            _ = φ ^ s.val * g v * c ^ s.val := h'.symm
            _ = _ := by ac_rfl
        rw [this]
        exact D.mul_mem (D.mul_mem (D.pow_mem hφD _) (D.pow_mem hcD _))
          (D.inv_mem (D.mul_mem (D.pow_mem hφD _) (D.pow_mem hcD _)))
      subst hv
      have h2 : φ ^ s.val * c ^ s.val = φ ^ t.val * c ^ t.val := by
        apply mul_left_cancel (a := g v)
        calc g v * (φ ^ s.val * c ^ s.val) = φ ^ s.val * g v * c ^ s.val := by ac_rfl
          _ = φ ^ t.val * g v * c ^ t.val := h'
          _ = _ := by ac_rfl
      have hZp : ∀ k : ℕ, φ ^ k ∈ Z := fun k => Z.pow_mem (Subgroup.mem_zpowers φ) k
      have h3 : φ ^ s.val = φ ^ t.val := by
        by_cases hs : Even s.val <;> by_cases ht : Even t.val
        · simpa [hce _ hs, hce _ ht] using h2
        · exfalso
          rw [hce _ hs, hco _ ht, mul_one] at h2
          exact hcZ ((Z.mul_mem_cancel_left (hZp t.val)).1 (h2 ▸ hZp s.val))
        · exfalso
          rw [hco _ hs, hce _ ht, mul_one] at h2
          exact hcZ ((Z.mul_mem_cancel_left (hZp s.val)).1 (h2 ▸ hZp t.val))
        · rw [hco _ hs, hco _ ht] at h2
          exact mul_right_cancel h2
      have h4 : s = t := Fin.ext (pow_injOn_Iio_orderOf s.2 t.2 h3)
      subst h4
      rfl
    · rintro ⟨h, hh⟩
      obtain ⟨v, hv⟩ := cover h
      have hv' : h * (g v)⁻¹ ∈ D := by
        have := D.inv_mem hv
        rwa [mul_inv_rev, inv_inv] at this
      have hH' : h * (g v)⁻¹ ∈ H := H.mul_mem hh (H.inv_mem (hgH v))
      rcases hD _ hv' with h1 | h1
      · obtain ⟨s, hs⟩ := hZpow _ h1
        refine ⟨⟨v, s⟩, Subtype.ext ?_⟩
        have hes : Even s.val := (hφk _).1 (hs ▸ hH')
        show φ ^ s.val * g v * c ^ s.val = h
        rw [hce _ hes, hs]; simp
      · obtain ⟨s, hs⟩ := hZpow _ h1
        refine ⟨⟨v, s⟩, Subtype.ext ?_⟩
        have hes : ¬ Even s.val := by
          rw [← hφk, hs, H.mul_mem_cancel_left hH']; exact hc
        show φ ^ s.val * g v * c ^ s.val = h
        rw [hco _ hes, hs]
        calc h * (g v)⁻¹ * c * g v * c = h * ((g v)⁻¹ * g v) * (c * c) := by ac_rfl
          _ = h := by simp [hcc]
  refine ⟨Nat.card (G ⧸ D), g, Equiv.ofBijective f hf, Nat.card_pos, fun v s => rfl,
    fun v v' h => key v v' (hZD h), ?_, ?_⟩
  · intro v v' h
    have h1 : g v' * c * (g v)⁻¹ = g v' * (g v)⁻¹ * c := by ac_rfl
    rw [h1] at h
    have hv := key v v' ((D.mul_mem_cancel_right hcD).1 (hZD h))
    subst hv
    exact hcZ (by simpa using h)
  · intro x
    obtain ⟨v, hv⟩ := cover x
    refine ⟨v, (hD _ hv).imp id fun h => ?_⟩
    have h1 : g v * c * x⁻¹ = g v * x⁻¹ * c := by ac_rfl
    rwa [h1]

theorem frobenius_orbit_positions : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (φ c : G), (∀ a b : G, a * b = b * a) → H.index = 2 → φ ∉ H → c ∉ H → c * c = 1 → c ∉ Subgroup.zpowers φ → 2 ≤ orderOf φ ∧ Even (orderOf φ) ∧ ∃ (N : ℕ) (g : Fin N → G) (pos : (Σ _ : Fin N, Fin (orderOf φ)) ≃ H), 0 < N ∧ (∀ v s, (pos ⟨v, s⟩ : G) = φ ^ s.val * g v * c ^ s.val) ∧ (∀ v v', g v' * (g v)⁻¹ ∈ Subgroup.zpowers φ → v = v') ∧ (∀ v v', g v' * c * (g v)⁻¹ ∉ Subgroup.zpowers φ) ∧ ∀ x : G, ∃ v, g v * x⁻¹ ∈ Subgroup.zpowers φ ∨ g v * c * x⁻¹ ∈ Subgroup.zpowers φ := by
  intro G inst _ H φ c hcomm
  letI : CommGroup G := { inst with mul_comm := hcomm }
  exact frobenius_orbit_positions_comm G H φ c

end GlobalTheory
