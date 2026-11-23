import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzStickValMain

noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace DiscreteGroups.sglob.DzPin

theorem pow_eq_pow_of_modEq {M : Type*} [Monoid M] {x : M} {N a b : ℕ} (h : x ^ N = 1)
    (hab : a ≡ b [MOD N]) : x ^ a = x ^ b := by
  have e1 : ∀ c : ℕ, x ^ c = x ^ (c % N) := by
    intro c
    conv_lhs => rw [← Nat.mod_add_div c N, pow_add, pow_mul, h, one_pow, mul_one]
  rw [e1 a, e1 b, show a % N = b % N from hab]

theorem modEq_twist {N t u k b e : ℕ} (htu : t * u ≡ 1 [MOD N]) :
    t * ((u * k + b * e) % N) ≡ k + e * (t * b) [MOD N] := by
  have h1 : t * ((u * k + b * e) % N) ≡ t * (u * k + b * e) [MOD N] :=
    (Nat.mod_modEq _ _).mul_left t
  have h2 : t * (u * k + b * e) = t * u * k + e * (t * b) := by ring
  have h3 : t * u * k + e * (t * b) ≡ 1 * k + e * (t * b) [MOD N] :=
    (htu.mul_right k).add_right _
  rw [one_mul] at h3
  rw [h2] at h1
  exact h1.trans h3

theorem modEq_twist0 {N t u k : ℕ} (htu : t * u ≡ 1 [MOD N]) : t * (u * k % N) ≡ k [MOD N] := by
  have h := modEq_twist (b := 0) (e := 0) (k := k) htu
  simpa using h

theorem exists_eq_pow_of_injective {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
    (Ω θ : G →* ℂˣ) (hΩ : Function.Injective Ω) : ∃ k : ℕ, θ = Ω ^ k := by
  classical
  have := Fintype.ofFinite G
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := G)
  have hord : orderOf γ = Fintype.card G :=
    (orderOf_eq_card_of_forall_mem_zpowers hγ).trans Nat.card_eq_fintype_card
  have : NeZero (Fintype.card G) := ⟨Fintype.card_ne_zero⟩
  have h1 : IsPrimitiveRoot γ (Fintype.card G) := hord ▸ IsPrimitiveRoot.orderOf γ
  have hprim : IsPrimitiveRoot ((Ω γ : ℂˣ) : ℂ) (Fintype.card G) :=
    (h1.map_of_injective hΩ).map_of_injective (f := Units.coeHom ℂ) Units.val_injective
  have hθ : ((θ γ : ℂˣ) : ℂ) ^ Fintype.card G = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
  obtain ⟨k, -, hk⟩ := hprim.eq_pow_of_pow_eq_one hθ
  refine ⟨k, MonoidHom.ext fun z => Units.ext ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, γ ^ j = z := by
    have hz := hγ z
    rw [← mem_powers_iff_mem_zpowers] at hz
    exact hz
  rw [MonoidHom.pow_apply, map_pow, map_pow, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val, ← hk, ← pow_mul, ← pow_mul, mul_comm]

theorem dsum_eq_of_pow_eq {p f : ℕ} [Fact p.Prime] {k : Type*} [Field k] [Fintype k]
    [Algebra (ZMod p) k] {A : Type*} [CommRing A] [IsDedekindDomain A] {Q : HeightOneSpectrum A}
    (D : Stick.GSDatum p f k A Q) {a₁ a₂ a₃ a₄ r : ℕ} (h₁ : a₁ < p ^ f - 1) (h₂ : a₂ < p ^ f - 1)
    (h₃ : a₃ < p ^ f - 1) (h₄ : a₄ < p ^ f - 1) (hr : 0 < r)
    (h : (D.g a₁ * D.g a₂) ^ r = (D.g a₃ * D.g a₄) ^ r) :
    Stick.dsum p a₁ + Stick.dsum p a₂ = Stick.dsum p a₃ + Stick.dsum p a₄ := by
  have hv := congrArg Q.intValuation h
  simp only [map_pow, map_mul, D.val_g h₁, D.val_g h₂, D.val_g h₃, D.val_g h₄, ← pow_add,
    ← pow_mul] at hv
  have h0 : 0 < Q.intValuation (D.ζ - 1) := zero_lt_iff.2 D.val_ζ_sub_one_ne_zero
  have h1 : Q.intValuation (D.ζ - 1) < 1 := (Q.intValuation_lt_one_iff_mem _).2 D.ζ_sub_one_mem
  have := (pow_right_strictAnti₀ h0 h1).injective hv
  exact Nat.eq_of_mul_eq_mul_right hr this

theorem addChar_apply_eq_pow {g : ℕ} [Fact g.Prime] (ψ₀ : AddChar (ZMod g) Circle) (y : ZMod g) :
    ((ψ₀ y : Circle) : ℂ) = ((ψ₀ 1 : Circle) : ℂ) ^ y.val := by
  have h : y = y.val • (1 : ZMod g) := by rw [nsmul_one, ZMod.natCast_zmod_val]
  conv_lhs => rw [h, AddChar.map_nsmul_eq_pow]
  rw [Circle.coe_pow]

theorem sum_units_eq {K : Type*} [Field K] [Fintype K] [DecidableEq K] (F : K → ℂ) (hF : F 0 = 0) :
    ∑ u : Kˣ, F u = ∑ x : K, F x := by
  rw [← Finset.sum_erase Finset.univ hF,
    Finset.sum_subtype (Finset.univ.erase (0 : K)) (p := fun x => x ≠ 0) (by simp) F]
  exact Fintype.sum_equiv unitsEquivNeZero _ _ (fun _ => rfl)

theorem gs_eq {g : ℕ} [Fact g.Prime] (ψ₀ : AddChar (ZMod g) Circle) {K : Type*} [Field K]
    [Fintype K] [Algebra (ZMod g) K] {A : Type*} [CommRing A] (Φ : A →+* ℂ) (ω : MulChar K A)
    (ζ : A) (hζ : ζ ^ g = 1) (hΦζ : Φ ζ = ((ψ₀ 1 : Circle) : ℂ)) (η : Kˣ →* ℂˣ) (a : ℕ)
    (hη : ∀ z : Kˣ, ((η z : ℂˣ) : ℂ) = Φ (ω z) ^ a) :
    (∑ᶠ z : Kˣ, (((η⁻¹) z : ℂˣ) : ℂ) * ((ψ₀ (Algebra.trace (ZMod g) K (z : K)) : Circle) : ℂ)) =
      Φ (gaussSum (ω ^ a)⁻¹ (Stick.psi g K ζ hζ)) := by
  classical
  rw [finsum_eq_sum_of_fintype, gaussSum, map_sum]
  rw [← sum_units_eq (fun x => Φ ((ω ^ a)⁻¹ x * Stick.psi g K ζ hζ x))
    (by rw [MulChar.map_zero, zero_mul, map_zero])]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [map_mul, Stick.psi_apply, map_pow, hΦζ, ← addChar_apply_eq_pow, MulChar.inv_apply',
    ← Units.val_inv_eq_inv_val, MulChar.pow_apply_coe, map_pow, ← hη, MonoidHom.inv_apply,
    ← map_inv]

end DiscreteGroups.sglob.DzPin
