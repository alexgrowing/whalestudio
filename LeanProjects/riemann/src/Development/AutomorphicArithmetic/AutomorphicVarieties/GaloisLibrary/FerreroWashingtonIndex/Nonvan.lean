import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.EvenTot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Sinnott
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CharPer
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.GcShift
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.PushDiff
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.GcNeg

open UpperTheory.V.FW

theorem UpperTheory.V.FW.nonvan :
    ∀ (l : ℕ) [Fact l.Prime] (f c : ℕ), f.Coprime l → Odd c → 1 < c → c.Coprime (f * l) → ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ (n : ℕ) [NeZero (f * l ^ n)] (h : l ^ n₀ ∣ f * l ^ n), n₀ ≤ n → ∀ (k : Type) [Field k] [CharP k l] (χ : (ZMod (f * l ^ n))ˣ →* kˣ), χ (-1) = -1 → tw χ (piQ l n₀ h) (toK k _ (thetaH (f * l ^ n) c)) ≠ 0 := by
  intro l _ f c hf hc1 hc hcop
  obtain ⟨R, hRne, hRW, hRind, hRneg, hRcov, -, -⟩ := reps l
  have hl := (Fact.out : l.Prime)
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hl.one_lt.ne' (Nat.coprime_zero_left l |>.mp hf)
  have hN0 : c * (f * l) ≠ 0 :=
    Nat.mul_ne_zero (by omega) (Nat.mul_ne_zero hf0 hl.ne_zero)
  haveI : Nonempty R := hRne.to_subtype
  obtain ⟨n₁, hn₁⟩ := sinnott l R (fun r => (r : ℤ_[l]ˣ)) (c * (f * l)) hN0
    (fun i j hij a b hab => hRind i i.2 j j.2 (fun e => hij (Subtype.ext e)) a b hab)
  refine ⟨max n₁ 2, le_max_right _ _, ?_⟩
  intro n _ h hn k _ _ χ hχ htw
  have hcf := Nat.coprime_mul_iff_right.mp hcop
  have hcM : c.Coprime (f * l ^ n) :=
    Nat.coprime_mul_iff_right.mpr ⟨hcf.1, Nat.Coprime.pow_right n hcf.2⟩
  have hn1 : 1 ≤ n := le_trans (by omega) (le_trans (le_max_right n₁ 2) hn)
  have hn2 : 2 ≤ n := le_trans (le_max_right n₁ 2) hn
  haveI : Fact (1 < f * l ^ n) := ⟨by
    have h1 : 1 < l ^ n := Nat.one_lt_pow (by omega) hl.one_lt
    have h2 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr hf0
    calc 1 < l ^ n := h1
      _ ≤ f * l ^ n := Nat.le_mul_of_pos_left _ h2⟩
  have hodd : ∀ s : (ZMod (f * l ^ n))ˣ,
      gc (f * l ^ n) c (-(s : ZMod (f * l ^ n))) = -gc (f * l ^ n) c s :=
    fun s => gcNeg _ c _ hcM hc1 s.ne_zero
  have hsum := twCoef l (f * l ^ n) (max n₁ 2) h k χ (gc (f * l ^ n) c) R
    (le_max_right _ _) hχ hodd hRW hRneg hRcov htw
  set Ψ : ZMod (f * l ^ n) → k := ⇑(MulChar.ofUnitHom χ) with hΨ
  have hper : ∀ x : ZMod (f * l ^ n), Ψ (x + ↑(f * l)) = Ψ x :=
    fun x => charPer l f n k χ x hf hn1
  have hshift := fun s => gcShift (f * l ^ n) c (f * l) k Ψ s hcM hper
  have hpush := pushDiff k (f * l ^ n) (l ^ max n₁ 2) h (c * (f * l))
    (fun j => Ψ ↑j * (1 - if c ∣ j then (c : k) else 0))
    (fun s => ((gc (f * l ^ n) c s : ℤ) : k) * Ψ s) hshift
  have hP := hn₁ (max n₁ 2) (le_max_left _ _) k
    (fun j => Ψ ↑j * (1 - if c ∣ j then (c : k) else 0))
    (push h fun s => ((gc (f * l ^ n) c s : ℤ) : k) * Ψ s) hpush hsum 1
    (by
      have : 1 ≤ f * l := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hf0 hl.ne_zero)
      nlinarith)
  have hndvd : ¬ c ∣ 1 := by
    intro hd
    have := Nat.le_of_dvd one_pos hd
    omega
  simp only [hndvd, if_false, sub_zero, mul_one, Nat.cast_one, hΨ, map_one] at hP
  exact one_ne_zero hP
