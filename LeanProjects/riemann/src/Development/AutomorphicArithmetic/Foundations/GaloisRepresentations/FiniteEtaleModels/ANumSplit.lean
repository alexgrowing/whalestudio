import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.GalOfKer

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

private theorem natCast_gcd_mem {A : Type} [CommRing A] {I : Ideal A} {x y : ℕ} (hx : (x : A) ∈ I) (hy : (y : A) ∈ I) :
    ((Nat.gcd x y : ℕ) : A) ∈ I := by
  have h : ((Nat.gcd x y : ℕ) : A) = (x : A) * (Nat.gcdA x y : A) + (y : A) * (Nat.gcdB x y : A) := by
    have := congrArg (Int.cast : ℤ → A) (Nat.gcd_eq_gcd_ab x y)
    push_cast at this
    exact this
  rw [h]
  exact I.add_mem (I.mul_mem_right _ hx) (I.mul_mem_right _ hy)

private theorem natCast_mem_of_isGen {A : Type} [CommRing A] {a : A} {N : ℕ} {𝔞 : Ideal A} (h : IsGen a N 𝔞) :
    (N : A) ∈ 𝔞 := by
  unfold IsGen at h
  have hN : (N : A) ∈ Ideal.span {(N : A)} := Ideal.mem_span_singleton_self _
  rw [← h] at hN
  have hle : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 ≤ 𝔞 := Ideal.mul_le_right
  exact hle hN

theorem UpperTheory.Gal.FiniteEtaleModels.numSplit_holds :
    NumSplit := by
  intro A _ _ _ 𝔟₁ 𝔟₂ M₁ M₂ Q a₁ a₂ hM₁ hM₂ hle h₁ h₂ hQ
  have hgM₁ : Nat.gcd Q (Nat.gcd M₁ M₂) ∣ M₁ := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  have hgM₂ : Nat.gcd Q (Nat.gcd M₁ M₂) ∣ M₂ := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  have hgQ : Nat.gcd Q (Nat.gcd M₁ M₂) ∣ Q := Nat.gcd_dvd_left _ _
  have hg_mem : ((Nat.gcd Q (Nat.gcd M₁ M₂) : ℕ) : A) ∈ 𝔟₂ :=
    natCast_gcd_mem (hle hQ) (natCast_gcd_mem (hle (natCast_mem_of_isGen h₁)) (natCast_mem_of_isGen h₂))
  have hgpos : 0 < Nat.gcd Q (Nat.gcd M₁ M₂) := Nat.pos_of_dvd_of_pos hgM₂ hM₂
  generalize Nat.gcd Q (Nat.gcd M₁ M₂) = g at hgM₁ hgM₂ hgQ hg_mem hgpos
  obtain ⟨m₁, hm₁⟩ := hgM₁
  obtain ⟨m₂, hm₂⟩ := hgM₂
  have h1 : a₂ * (g : A) ∈ Ideal.span {(M₂ : A)} := by
    rw [← h₂]
    exact Ideal.mul_mem_mul (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a₂)) hg_mem
  rw [Ideal.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  have hg0 : (g : A) ≠ 0 := by exact_mod_cast hgpos.ne'
  have hm₂pos : 0 < m₂ := by
    rcases Nat.eq_zero_or_pos m₂ with h | h
    · subst h; omega
    · exact h
  have hm₂0 : (m₂ : A) ≠ 0 := by exact_mod_cast hm₂pos.ne'
  have hM₂c : (M₂ : A) = (g : A) * (m₂ : A) := by rw [hm₂]; push_cast; ring
  have ha : a₂ = (m₂ : A) * c := by
    apply mul_right_cancel₀ hg0
    rw [hc, hM₂c]; ring
  refine ⟨g, m₁, m₂, c, hgQ, hm₁, hm₂, ha, ?_⟩
  unfold IsGen at h₂ ⊢
  have hs : Ideal.span {(m₂ : A)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hm₂0
  apply mul_left_cancel₀ hs
  calc Ideal.span {(m₂ : A)} * ((Ideal.span {c} ⊔ Ideal.span {(g : A)}) * 𝔟₂)
      = (Ideal.span {(m₂ : A)} * Ideal.span {c} ⊔ Ideal.span {(m₂ : A)} * Ideal.span {(g : A)}) * 𝔟₂ := by
        rw [← _root_.mul_assoc, Ideal.mul_sup]
    _ = (Ideal.span {a₂} ⊔ Ideal.span {(M₂ : A)}) * 𝔟₂ := by
        rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton, ← ha, hM₂c,
          _root_.mul_comm (m₂ : A)]
    _ = Ideal.span {(M₂ : A)} := h₂
    _ = Ideal.span {(m₂ : A)} * Ideal.span {(g : A)} := by
        rw [Ideal.span_singleton_mul_span_singleton, hM₂c, _root_.mul_comm]
