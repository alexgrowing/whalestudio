import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass

set_option autoImplicit false

namespace GlobalTheory.SquareNorm

open NumberField IsDedekindDomain Formalism.L2.Pj

theorem exists_eq_mul_map {R : Type} [CommRing R] [IsDedekindDomain R] (e : R ≃+* R) (he : ∀ x, e (e x) = x)
    (𝔡 : Ideal R) : 𝔡 ≠ ⊥ → 𝔡.map (e : R →+* R) = 𝔡 →
      (∀ P : Ideal R, P.IsPrime → 𝔡 ≤ P → P.map (e : R →+* R) ≠ P) →
      ∃ 𝔞 : Ideal R, 𝔡 = 𝔞 * 𝔞.map (e : R →+* R) := by
  have hee : ∀ I : Ideal R, (I.map (e : R →+* R)).map (e : R →+* R) = I := fun I => by
    rw [Ideal.map_map]
    have : (e : R →+* R).comp (e : R →+* R) = RingHom.id R := RingHom.ext he
    rw [this, Ideal.map_id]
  induction 𝔡 using WellFoundedGT.induction with
  | ind 𝔡 ih =>
  intro h0 hinv hmv
  by_cases ht : 𝔡 = ⊤
  · exact ⟨⊤, by rw [ht, Ideal.map_top, Ideal.top_mul]⟩
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal 𝔡 ht
  have hQ : (P.map (e : R →+* R)).IsMaximal := Ideal.IsMaximal.map_bijective (e : R →+* R) e.bijective hP
  have hne := hmv P hP.isPrime hle
  have hle' : 𝔡 ≤ P.map (e : R →+* R) := by
    have := Ideal.map_mono (f := (e : R →+* R)) hle
    rwa [hinv] at this
  have hcop : IsCoprime P (P.map (e : R →+* R)) :=
    Ideal.isCoprime_iff_sup_eq.2 (hP.coprime_of_ne hQ hne.symm)
  obtain ⟨𝔟, hb⟩ := hcop.mul_dvd (Ideal.dvd_iff_le.2 hle) (Ideal.dvd_iff_le.2 hle')
  have hPQ : P * P.map (e : R →+* R) ≠ 0 := fun h => h0 (by rw [hb, h, zero_mul]; rfl)
  have hb0 : 𝔟 ≠ ⊥ := fun h => h0 (by rw [hb, h, Ideal.mul_bot])
  have hdb : 𝔡 ≤ 𝔟 := Ideal.le_of_dvd ⟨P * P.map (e : R →+* R), by rw [mul_comm]; exact hb⟩
  have hlt : 𝔡 < 𝔟 := by
    refine lt_of_le_of_ne hdb fun h => ?_
    have h1 : P * P.map (e : R →+* R) * 𝔟 = 1 * 𝔟 := by rw [← hb, one_mul, h]
    have h2 := mul_right_cancel₀ hb0 h1
    have h3 : (1 : Ideal R) ≤ P := Ideal.le_of_dvd ⟨_, h2.symm⟩
    rw [Ideal.one_eq_top] at h3
    exact hP.ne_top (top_le_iff.1 h3)
  have hbinv : 𝔟.map (e : R →+* R) = 𝔟 := by
    apply mul_left_cancel₀ hPQ
    rw [← hb]
    conv_rhs => rw [← hinv, hb]
    rw [Ideal.map_mul, Ideal.map_mul, hee, mul_comm P]
  obtain ⟨𝔞, ha⟩ := ih 𝔟 hlt hb0 hbinv fun Q hQ' h => hmv Q hQ' (hdb.trans h)
  refine ⟨P * 𝔞, ?_⟩
  rw [hb, Ideal.map_mul]
  conv_lhs => rw [ha]
  ring

theorem isSquare_absNorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (𝔡 : Ideal (𝓞 E)), 𝔡 ≠ ⊥ → 𝔡.map (H.bar : 𝓞 E →+* 𝓞 E) = 𝔡 → (∀ P : Ideal (𝓞 E), P.IsPrime → 𝔡 ≤ P → P.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ P) → IsSquare (Ideal.absNorm 𝔡) := by
  intro E _ _ _ H 𝔡 h0 hinv hmv
  have he : ∀ x, H.bar (H.bar x) = x := fun x => RingOfIntegers.ext (by
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply])
  obtain ⟨𝔞, ha⟩ := exists_eq_mul_map H.bar he 𝔡 h0 hinv hmv
  have hN : Ideal.absNorm (𝔞.map (H.bar : 𝓞 E →+* 𝓞 E)) = Ideal.absNorm 𝔞 := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr (Ideal.quotientEquiv 𝔞 _ H.bar rfl).toEquiv).symm
  exact ⟨Ideal.absNorm 𝔞, by rw [ha, map_mul, hN]⟩

end GlobalTheory.SquareNorm
