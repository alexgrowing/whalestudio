import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiftUnit

set_option autoImplicit false

noncomputable section

open GlobalTheory.UPel.HT.Gen

namespace UpperTheory.Gal.FiniteEtaleModels.O

theorem tResim : TResim := by
  intro G k _ Q _ act e I g hg
  have hn : ∀ n : ℕ, 0 < n → ∀ z : G.La, I.ev n (n • z) = 1 := fun n h0 z =>
    (I.ker n h0 _).2 ⟨z, rfl⟩
  have hadd : ∀ n : ℕ, 0 < n → ∀ (x z : G.La), I.ev n (x + n • z) = I.ev n x := by
    intro n h0 x z
    rw [I.add, hn n h0, mul_one]
  refine ⟨{ ζ := I.ζ
            ζ_prim := I.ζ_prim
            ζ_pow := I.ζ_pow
            ev := fun n x => if 0 < n then I.ev n (g n x) else I.ev n x
            add := ?_
            lin := ?_
            ker := ?_
            onto := ?_
            tower := ?_
            isom := ?_ }, ?_⟩
  · intro n x y
    by_cases h0 : 0 < n
    · simp only [if_pos h0, map_add, I.add]
    · simp only [if_neg h0, I.add]
  · intro n b x
    by_cases h0 : 0 < n
    · simp only [if_pos h0]
      obtain ⟨z, hz⟩ := hg.lin n h0 b x
      rw [hz, hadd n h0, I.lin]
    · simp only [if_neg h0, I.lin]
  · intro n h0 x
    simp only [if_pos h0]
    rw [I.ker n h0]
    constructor
    · rintro ⟨y, hy⟩
      exact hg.inj n h0 x y hy
    · rintro ⟨v, rfl⟩
      exact ⟨g n v, map_nsmul (g n) n v⟩
  · intro n h0 q
    simp only [if_pos h0]
    rw [I.onto n h0]
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, z, hy⟩ := hg.onto n h0 x
      exact ⟨y, by rw [hy, hadd n h0]⟩
    · rintro ⟨x, hx⟩
      exact ⟨g n x, hx⟩
  · intro n m hn0 hm0 x
    have h0 : 0 < n * m := Nat.mul_pos hn0 hm0
    simp only [if_pos h0, if_pos hn0]
    rw [I.tower n m hn0 hm0]
    obtain ⟨z, hz⟩ := hg.tow n m hn0 hm0 x
    rw [hz, hadd n hn0]
  · intro n h0 x y
    simp only [if_pos h0]
    have h := I.isom n h0 (g n x) (g n y)
    obtain ⟨c, hc⟩ := hg.iso n h0 x y
    have hz : I.ζ n ^ (n : ℤ) = 1 := by
      rw [zpow_natCast]
      exact (I.ζ_prim n h0).pow_eq_one
    have hE : I.ζ n ^ (2 * G.EF (g n x) (g n y)) = I.ζ n ^ (2 * G.EF x y) := by
      have : 2 * G.EF (g n x) (g n y) = 2 * G.EF x y + (n : ℤ) * (2 * c) := by
        linarith [hc]
      rw [this, zpow_add, zpow_mul (I.ζ n) (n : ℤ), hz, one_zpow, mul_one]
    rw [hE] at h
    exact h
  · intro n h0 x
    simp only [if_pos h0]

end UpperTheory.Gal.FiniteEtaleModels.O
