import Development.AutomorphicArithmetic.CoprimeRanks.SecondSetNoRelation
import Development.AutomorphicArithmetic.CoprimeRanks.AnyFramewindow
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.ExistsHostAxEven

open NumberField Formalism.FrobeniusOrbits Formalism.HC

noncomputable section

namespace HostParam.Seam

variable {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M))

private theorem conductor_divisor_bounds {φ : Frame} {H : HostRaw φ} {e b : ℕ} (hQ : H.QS ∣ Nat.lcm (2 ^ (e + 2)) M) (hb : 4 * M ≤ b) :
    (∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ H.QS → l ∣ M ∧ 4 * l ≤ b) ∧ H.QS ≤ 4 * M * 2 ^ e := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have h1 := hQ.trans (Nat.lcm_dvd_mul _ _)
  refine ⟨fun l hl h2 h => ?_, (Nat.le_of_dvd (by positivity) h1).trans (le_of_eq (by ring))⟩
  have h3 : l ∣ M := (hl.dvd_mul.1 (h.trans h1)).resolve_left fun h4 =>
    h2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow h4))
  have := Nat.le_of_dvd hM h3
  exact ⟨h3, by omega⟩

theorem exists_fieldRows_any_ord {e q d b : ℕ} (hH : HostHyp q d) (hq3 : q ≠ 3) (hc : Nat.Coprime M (q * d))
    (he : 4 * M ≤ 2 ^ e) (ho : Nat.card Ξ ^ 64 ≤ 2 ^ e) (hb : 4 * M ≤ b)
    (hs : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ b → jacobiSym (-(d : ℤ)) p = 1) :
    ∃ (φ : Frame) (H : HostAx φ), φ.ord = (AnyGrp.frame Ξ e).ord ∧ φ.e = e ∧ H.q = q ∧ H.d = d ∧ φ.o = Nat.card Ξ ∧ FieldRows H.toHostRaw b ∧
      H.QS ∣ Nat.lcm (2 ^ (e + 2)) M ∧ H.QS ≤ 4 * M * φ.ord ∧
      H.KeptInXp (Level.ofSub Ξ).KEPT ∧ H.ExceptionalCharacterKept (Level.ofSub Ξ).KEPT (Level.ofSub Ξ).psK ∧
      (Nat.Coprime M 15 → H.CoprimeFifteen) ∧ ((∃ j : ℕ, Nat.card Ξ = 2 ^ j) → φ.TwoGroup) ∧
      ((∀ χ ∈ Ξ, χ.Even) → H.MuPM ∧ H.KeptEqChat (Level.ofSub Ξ).KEPT) := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have he2 : 2 ≤ e := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).1 (by omega)
  have hs' : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ M → jacobiSym (-(d : ℤ)) l = 1 := fun l hl h2 h =>
    hs l hl h2 (by have := Nat.le_of_dvd hM h; omega)
  have fin : ∀ {φ : Frame} {H : HostRaw φ}, φ.e = e → H.QS ≤ 4 * M * 2 ^ e → H.QS ≤ 4 * M * φ.ord := fun {φ H} h1 h2 =>
    h2.trans (Nat.mul_le_mul_left _ (h1 ▸ φ.two_pow_le_ord))
  by_cases hev : ∀ χ ∈ Ξ, χ.Even
  · obtain ⟨r1, r2⟩ := conductor_divisor_bounds (H := EvenGrp.host Ξ e hev hH hc he2 hs') (EvenGrp.QS_dvd Ξ e) hb
    exact ⟨_, HostAx.ofRaw (EvenGrp.host Ξ e hev hH hc he2 hs'), (anyFrame_window Ξ).2.1 e hev, rfl, rfl, rfl,
      EvenGrp.o_eq Ξ e hev,
      ⟨EvenGrp.psQ Ξ e hev hH hc he2 hs', EvenGrp.exists_sqq Ξ e hev hH hc he2 hs', EvenGrp.exact Ξ e hev hH hc he2 hs',
        EvenGrp.QS_le Ξ e hev he, by rw [EvenGrp.o_eq]; exact ho, hq3, hs, fun l h1 h2 h3 => (r1 l h1 h2 h3).2⟩,
      EvenGrp.QS_dvd Ξ e, fin rfl r2, EvenGrp.keptInXp Ξ e hev hH hc he2 hs', EvenGrp.exceptional_character_condition Ξ e hev hH hc he2 hs',
      EvenGrp.coprimeFifteen_of_coprime Ξ e hev hH hc he2 hs', EvenGrp.twoGroup Ξ e hev,
      fun _ => ⟨EvenGrp.muPM Ξ e hev hH hc he2 hs' hq3, EvenGrp.keptEqChat Ξ e hev hH hc he2 hs'⟩⟩
  · obtain ⟨r1, r2⟩ := conductor_divisor_bounds (H := AnyGrp.host Ξ e hH hc he2 hs') (EvenGrp.QS_dvd Ξ e) hb
    exact ⟨_, HostAx.ofRaw (AnyGrp.host Ξ e hH hc he2 hs'), rfl, rfl, rfl, rfl, AnyGrp.o_eq Ξ e,
      ⟨AnyGrp.psQ Ξ e hH hc he2 hs', AnyGrp.exists_sqq Ξ e hH hc he2 hs', AnyGrp.exact Ξ e hH hc he2 hs',
        AnyGrp.QS_le Ξ e he, by rw [AnyGrp.o_eq]; exact ho, hq3, hs, fun l h1 h2 h3 => (r1 l h1 h2 h3).2⟩,
      EvenGrp.QS_dvd Ξ e, fin rfl r2, AnyGrp.keptInXp Ξ e hH hc he2 hs', AnyGrp.exceptional_character_condition Ξ e hH hc he2 hs',
      AnyGrp.coprimeFifteen_of_coprime Ξ e hH hc he2 hs', AnyGrp.twoGroup Ξ e, fun h => absurd h hev⟩

end HostParam.Seam

end
