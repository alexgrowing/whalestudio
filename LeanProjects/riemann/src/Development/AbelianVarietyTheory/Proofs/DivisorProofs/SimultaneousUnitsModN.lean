import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.DualUnit

theorem exists_unit_of_perfect {R : Type} [CommRing R] (bar : R ≃+* R) (hbar : ∀ a, bar (bar a) = a)
    (N : ℕ) (hN : 0 < N) [Finite (R ⧸ Ideal.span {(N : R)})] (T₁ T₂ : R →+ ℤ)
    (s₁ : ∀ c, T₁ (bar c) = - T₁ c) (s₂ : ∀ c, T₂ (bar c) = - T₂ c)
    (p₁ : ∀ c : R, (∀ d : R, (N : ℤ) ∣ T₁ (c * d)) → ∃ b : R, c = N • b)
    (p₂ : ∀ c : R, (∀ d : R, (N : ℤ) ∣ T₂ (c * d)) → ∃ b : R, c = N • b) :
    ∃ μ ν : R, (∃ b : R, μ * ν - 1 = N • b) ∧ (∃ b : R, bar μ - μ = N • b) ∧
      ∀ c : R, (N : ℤ) ∣ T₁ (μ * c) - T₂ c := by
  classical
  haveI : NeZero N := ⟨hN.ne'⟩
  set I : Ideal R := Ideal.span {(N : R)} with hI
  have memI : ∀ x, x ∈ I ↔ ∃ b : R, x = N • b := by
    intro x
    rw [hI, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨a, by rw [nsmul_eq_mul, mul_comm]⟩
    · rintro ⟨b, rfl⟩; exact ⟨b, by rw [nsmul_eq_mul, mul_comm]⟩
  have hTI : ∀ (T : R →+ ℤ) x, x ∈ I → (N : ℤ) ∣ T x := by
    intro T x hx
    obtain ⟨b, rfl⟩ := (memI x).1 hx
    rw [map_nsmul, nsmul_eq_mul]
    exact dvd_mul_right _ _
  let tq : (R →+ ℤ) → (R ⧸ I →+ ZMod N) := fun T =>
    QuotientAddGroup.lift I.toAddSubgroup ((Int.castAddHom (ZMod N)).comp T) (fun x hx => by
      show ((T x : ℤ) : ZMod N) = 0
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (hTI T x hx))
  have htq : ∀ T x, tq T (Ideal.Quotient.mk I x) = (T x : ZMod N) := fun T x => rfl
  have hπ : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  let Φ : R ⧸ I → (R ⧸ I →+ ZMod N) := fun q => (tq T₁).comp (AddMonoidHom.mulLeft q)
  have hΦ : ∀ x d, Φ (Ideal.Quotient.mk I x) (Ideal.Quotient.mk I d) = (T₁ (x * d) : ZMod N) := by
    intro x d
    simp only [Φ, AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, ← map_mul, htq]
  have hinj : Function.Injective Φ := by
    intro q q' h
    obtain ⟨x, rfl⟩ := hπ q
    obtain ⟨x', rfl⟩ := hπ q'
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, memI]
    apply p₁
    intro d
    have h1 := DFunLike.congr_fun h (Ideal.Quotient.mk I d)
    rw [hΦ, hΦ] at h1
    rw [sub_mul, map_sub]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1.symm
  haveI : Finite (R ⧸ I →+ ZMod N) := Finite.of_injective _ DFunLike.coe_injective
  have hcard : Nat.card (R ⧸ I →+ ZMod N) ≤ Nat.card (R ⧸ I) := by
    have := Fintype.ofFinite (R ⧸ I)
    have hF : Function.Injective
        (fun φ : R ⧸ I →+ ZMod N => (ZMod.stdAddChar (N := N)).compAddMonoidHom φ) := fun φ ψ h => by
      ext m
      exact ZMod.injective_stdAddChar (DFunLike.congr_fun h m)
    have h := Nat.card_le_card_of_injective _ hF
    rwa [Nat.card_eq_fintype_card (α := AddChar (R ⧸ I) ℂ), AddChar.card_eq,
      ← Nat.card_eq_fintype_card] at h
  have hbij := hinj.bijective_of_nat_card_le hcard
  obtain ⟨m, hm⟩ := hbij.2 (tq T₂)
  obtain ⟨μ, rfl⟩ := hπ m
  have hμ : ∀ c, (N : ℤ) ∣ T₁ (μ * c) - T₂ c := by
    intro c
    have h1 := DFunLike.congr_fun hm (Ideal.Quotient.mk I c)
    rw [hΦ, htq] at h1
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1.symm
  have hmulinj : Function.Injective (fun q : R ⧸ I => Ideal.Quotient.mk I μ * q) := by
    intro q q' h
    obtain ⟨x, rfl⟩ := hπ q
    obtain ⟨x', rfl⟩ := hπ q'
    simp only at h
    rw [← map_mul, ← map_mul, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem] at h
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, memI]
    apply p₂
    intro d
    have h1 := hμ ((x - x') * d)
    have h2 : (N : ℤ) ∣ T₁ (μ * ((x - x') * d)) := by
      rw [← mul_assoc, mul_sub]
      exact hTI T₁ _ (I.mul_mem_right d h)
    have h3 := dvd_sub h2 h1
    rwa [sub_sub_cancel] at h3
  obtain ⟨q, hq⟩ := (Finite.injective_iff_surjective.1 hmulinj) 1
  obtain ⟨ν, rfl⟩ := hπ q
  refine ⟨μ, ν, ?_, ?_, hμ⟩
  · rw [← memI, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one]
    exact sub_eq_zero.2 hq
  · apply p₁
    intro c
    have e1 : T₁ (bar μ * c) = - T₁ (μ * bar c) := by
      rw [← s₁, map_mul bar, hbar]
    have hX := hμ (bar c)
    have hY := hμ c
    have e2 := s₂ c
    have e3 : T₁ ((bar μ - μ) * c) = -(T₁ (μ * bar c) - T₂ (bar c)) - (T₁ (μ * c) - T₂ c) := by
      rw [sub_mul, map_sub, e1, e2]
      ring
    rw [e3]
    exact (dvd_neg.2 hX).sub hY

theorem dual_unit : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (N : ℕ), 0 < N →
    ∀ T₁ T₂ : 𝓞 E →+ ℤ, (∀ c, T₁ (H.bar c) = - T₁ c) → (∀ c, T₂ (H.bar c) = - T₂ c) →
    (∀ c : 𝓞 E, (∀ d : 𝓞 E, (N : ℤ) ∣ T₁ (c * d)) → ∃ b : 𝓞 E, c = N • b) →
    (∀ c : 𝓞 E, (∀ d : 𝓞 E, (N : ℤ) ∣ T₂ (c * d)) → ∃ b : 𝓞 E, c = N • b) →
    ∃ μ ν : 𝓞 E, (∃ b : 𝓞 E, μ * ν - 1 = N • b) ∧ (∃ b : 𝓞 E, H.bar μ - μ = N • b) ∧
      ∀ c : 𝓞 E, (N : ℤ) ∣ T₁ (μ * c) - T₂ c := by
  intro E _ _ _ H N hN T₁ T₂ s₁ s₂ p₁ p₂
  have hbar : ∀ a, H.bar (H.bar a) = a := fun a => by
    have h1 := H.bar_eq (H.bar a)
    have h2 := H.bar_eq a
    apply RingOfIntegers.ext
    rw [h1, h2, IsCMField.complexConj_apply_apply]
  haveI : Finite (𝓞 E ⧸ Ideal.span {((N : ℕ) : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN.ne')
  exact exists_unit_of_perfect H.bar hbar N hN T₁ T₂ s₁ s₂ p₁ p₂

end GlobalTheory.DualUnit
