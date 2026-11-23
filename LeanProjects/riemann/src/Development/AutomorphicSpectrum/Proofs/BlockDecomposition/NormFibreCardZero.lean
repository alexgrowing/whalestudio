import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens.NormZero

variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}

abbrev Fx (τ : E →+* E) : Type := {a : E // τ a = a}

def zeroFx (τ : E →+* E) : Fx τ := ⟨0, map_zero τ⟩

theorem finite_of_resAlg (h : ResAlg E τ q ε) : Finite E := by
  apply Nat.finite_of_card_ne_zero
  rw [h.card]
  have := h.one_lt
  positivity

theorem nontrivial_of_resAlg (h : ResAlg E τ q ε) : Nontrivial E := by
  haveI := finite_of_resAlg h
  apply Finite.one_lt_card_iff_nontrivial.1
  rw [h.card]
  have := h.one_lt
  nlinarith

theorem card_fx (h : ResAlg E τ q ε) : Nat.card (Fx τ) = q := by
  obtain ⟨u, hu, hb⟩ := h.basis
  let φ : Fx τ × Fx τ → E := fun p => (p.1 : E) + (p.2 : E) * u
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ hxy
      have h1 : x + y * u = x' + y' * u := hxy
      have h2 : x + y * τ u = x' + y' * τ u := by
        have := congrArg τ h1
        simpa [hx, hy, hx', hy'] using this
      have h3 : (y - y') * (u - τ u) = 0 := by linear_combination h1 - h2
      have h4 : y = y' := sub_eq_zero.1 (hu.mul_left_eq_zero.1 h3)
      have h5 : x = x' := by
        subst h4
        exact add_right_cancel h1
      subst h4 h5
      rfl
    · intro a
      obtain ⟨x, y, hx, hy, rfl⟩ := hb a
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  have h1 : Nat.card (Fx τ × Fx τ) = Nat.card E := Nat.card_congr (Equiv.ofBijective φ hφ)
  rw [Nat.card_prod, h.card] at h1
  have h2 : Nat.card (Fx τ) ^ 2 = q ^ 2 := by rw [← h1]; ring
  exact (Nat.pow_left_inj (by norm_num)).1 h2

theorem exists_idem (h : ResAlg E τ q ε) (hf : ¬ IsField E) :
    ∃ e : E, e * e = e ∧ τ e = 1 - e := by
  haveI := nontrivial_of_resAlg h
  obtain ⟨a, ha0, hau⟩ : ∃ a : E, a ≠ 0 ∧ ¬ IsUnit a := by
    by_contra hc
    push_neg at hc
    refine hf ⟨exists_pair_ne E, mul_comm, fun {a} ha => ?_⟩
    obtain ⟨b, hb⟩ := (hc a ha).exists_right_inv
    exact ⟨b, hb⟩
  obtain ⟨u, hu, -⟩ := h.basis
  have hN : a * τ a = 0 := by
    by_contra hN
    have hfix : τ (a * τ a) = a * τ a := by rw [map_mul, h.inv, mul_comm]
    exact hau (isUnit_of_mul_isUnit_left (h.fixedUnit _ hfix hN))
  have htfix : τ (a + τ a) = a + τ a := by rw [map_add, h.inv, add_comm]
  by_cases ht : a + τ a = 0
  · exfalso
    have hτa : τ a = -a := by linear_combination ht
    have hfix : τ (a * (u - τ u)) = a * (u - τ u) := by
      rw [map_mul, map_sub, h.inv, hτa]
      ring
    have hne : a * (u - τ u) ≠ 0 := fun h0 => ha0 (hu.mul_left_eq_zero.1 h0)
    exact hau (isUnit_of_mul_isUnit_left (h.fixedUnit _ hfix hne))
  · obtain ⟨s, hs⟩ := (h.fixedUnit _ htfix ht).exists_right_inv
    have hτs : τ s = s := by
      have h1 : (a + τ a) * τ s = 1 := by
        have := congrArg τ hs
        rwa [map_mul, htfix, map_one] at this
      calc τ s = (s * (a + τ a)) * τ s := by rw [mul_comm s, hs, one_mul]
        _ = s * ((a + τ a) * τ s) := by ring
        _ = s := by rw [h1, mul_one]
    have hτe : τ (a * s) = 1 - a * s := by
      rw [map_mul, hτs]
      linear_combination hs
    refine ⟨a * s, ?_, hτe⟩
    linear_combination (-(s * s)) * hN + (a * s) * hs

theorem card_axes {F : Type} [Finite F] (z : F) :
    Nat.card {p : F × F // p.1 = z ∨ p.2 = z} + 1 = 2 * Nat.card F := by
  classical
  haveI := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h1 : (Finset.univ.filter fun p : F × F => p.1 = z ∨ p.2 = z)
      = (({z} : Finset F) ×ˢ (Finset.univ : Finset F)) ∪ ((Finset.univ : Finset F) ×ˢ ({z} : Finset F)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_product, Finset.mem_singleton,
      Finset.mem_univ, and_true, true_and]
  have h2 : (({z} : Finset F) ×ˢ (Finset.univ : Finset F)) ∩ ((Finset.univ : Finset F) ×ˢ ({z} : Finset F))
      = {(z, z)} := by
    ext ⟨a, b⟩
    simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ, and_true,
      true_and, Prod.mk.injEq]
  have h3 := Finset.card_union_add_card_inter (({z} : Finset F) ×ˢ (Finset.univ : Finset F))
    ((Finset.univ : Finset F) ×ˢ ({z} : Finset F))
  rw [h2] at h3
  rw [h1]
  simp only [Finset.card_product, Finset.card_singleton, Finset.card_univ, one_mul, mul_one] at h3
  omega

theorem card_zero_split (h : ResAlg E τ q ε) {e : E} (he : e * e = e) (hτ : τ e = 1 - e) :
    Nat.card {a : E // a * τ a = 0} + 1 = 2 * q := by
  have hτf : τ (1 - e) = e := by rw [map_sub, map_one, hτ]; ring
  let g : Fx τ × Fx τ → E := fun p => (p.1 : E) * e + (p.2 : E) * (1 - e)
  have hnorm : ∀ p, g p * τ (g p) = (p.1 : E) * (p.2 : E) := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    show (x * e + y * (1 - e)) * τ (x * e + y * (1 - e)) = x * y
    rw [map_add, map_mul, map_mul, hx, hy, hτ, hτf]
    linear_combination (2 * x * y - x ^ 2 - y ^ 2) * he
  have hg : Function.Bijective g := by
    constructor
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ hxy
      have h1 : x * e + y * (1 - e) = x' * e + y' * (1 - e) := hxy
      have h2 : x * (1 - e) + y * e = x' * (1 - e) + y' * e := by
        have := congrArg τ h1
        simpa only [map_add, map_mul, hx, hy, hx', hy', hτ, hτf] using this
      have hxe : x * e = x' * e := by
        linear_combination e * h1 + (y - y' - x + x') * he
      have hye : y * e = y' * e := by
        linear_combination e * h2 + (x - x' - y + y') * he
      have h5 : x = x' := by linear_combination h2 + hxe - hye
      have h6 : y = y' := by linear_combination h1 - hxe + hye
      subst h5 h6
      rfl
    · intro a
      refine ⟨(⟨a * e + τ a * (1 - e), ?_⟩, ⟨a * (1 - e) + τ a * e, ?_⟩), ?_⟩
      · rw [map_add, map_mul, map_mul, h.inv, hτ, hτf]; ring
      · rw [map_add, map_mul, map_mul, h.inv, hτ, hτf]; ring
      · show (a * e + τ a * (1 - e)) * e + (a * (1 - e) + τ a * e) * (1 - e) = a
        linear_combination (2 * a - 2 * τ a) * he
  have hz : ∀ p : Fx τ × Fx τ, (p.1 = zeroFx τ ∨ p.2 = zeroFx τ) ↔ g p * τ (g p) = 0 := by
    intro p
    rw [hnorm]
    constructor
    · rintro (h0 | h0)
      · rw [h0]; simp [zeroFx]
      · rw [h0]; simp [zeroFx]
    · intro h0
      by_cases hx : (p.1 : E) = 0
      · exact Or.inl (Subtype.ext hx)
      · exact Or.inr (Subtype.ext ((h.fixedUnit _ p.1.2 hx).mul_right_eq_zero.1 h0))
  have hcard : Nat.card {p : Fx τ × Fx τ // p.1 = zeroFx τ ∨ p.2 = zeroFx τ}
      = Nat.card {a : E // a * τ a = 0} :=
    Nat.card_congr ((Equiv.ofBijective g hg).subtypeEquiv hz)
  haveI := finite_of_resAlg h
  rw [← hcard, card_axes, card_fx h]

theorem card_norm_zero : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε →
    (Nat.card {a : E // a * τ a = 0} : ℤ) = q * (1 + ε) - ε := by
  intro E _ τ q ε h
  rcases h.eps with ⟨rfl, hf⟩ | ⟨rfl, hf⟩
  · haveI : IsDomain E := hf.isDomain
    have hu : ∀ a : {a : E // a * τ a = 0}, a = ⟨0, by simp⟩ := by
      rintro ⟨a, ha⟩
      apply Subtype.ext
      rcases mul_eq_zero.1 ha with h0 | h0
      · exact h0
      · have := h.inv a
        rw [h0, map_zero] at this
        exact this.symm
    have h1 : Nat.card {a : E // a * τ a = 0} = 1 := by
      haveI : Unique {a : E // a * τ a = 0} := ⟨⟨⟨0, by simp⟩⟩, hu⟩
      exact Nat.card_unique
    rw [h1]
    simp
  · obtain ⟨e, he, hτ⟩ := exists_idem h hf
    have h1 := card_zero_split h he hτ
    have h2 : (Nat.card {a : E // a * τ a = 0} : ℤ) + 1 = 2 * q := by exact_mod_cast h1
    linarith

end GlobalTheory.CompanionTheory.UnrDens.NormZero
