import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ToKOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.AmbCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ConjEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CardRangeInfTorsionLeIndexPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.StickH
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SgnCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.PTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.POddRelIndexLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ReflOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.EmbedDeg
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CardClDualOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.cyc (l : ℕ) [hl : Fact l.Prime] (f : ℕ) (hf : f.Coprime l) (h1 : 1 < f) :
    ∃ B n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {f * l ^ n} ℚ L],
      IsTotallyComplex L ∧ (powR (Cl L) l).index ≤ B := by
  classical
  have hf0 : 0 < f := by omega
  have hl0 : 0 < l := hl.out.pos
  have hfl0 : 0 < f * l := Nat.mul_pos hf0 hl0
  have hcodd : Odd (2 * (f * l) + 1) := ⟨f * l, by ring⟩
  have hc1 : 1 < 2 * (f * l) + 1 := by omega
  have hcfl : (2 * (f * l) + 1).Coprime (f * l) := by
    simp [Nat.coprime_mul_left_add_left]
  obtain ⟨N, n₀, hn₀2, hmem⟩ := memZ l f (2 * (f * l) + 1) hf hcodd hc1 hcfl
  obtain ⟨B, hB⟩ := ambCyc l f hf
  by_cases hl2 : l = 2
  · subst hl2
    refine ⟨((2 ^ (f * 2 ^ ee 2).totient) ^ N * B ^ N) ^ 2, n₀, ?_⟩
    intro n hn L _ _ _
    haveI : NeZero (f * 2 ^ n) := ⟨(Nat.mul_pos hf0 (pow_pos hl0 n)).ne'⟩
    have hM2 : 2 < f * 2 ^ n := by
      have : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      nlinarith
    haveI : IsCMField L := IsCyclotomicExtension.Rat.isCMField L ⟨f * 2 ^ n, Set.mem_singleton _, hM2⟩
    refine ⟨inferInstance, ?_⟩
    obtain ⟨γ, hγ1, hγidx, hγmem⟩ := hmem n hn
    have hcM : (2 * (f * 2) + 1).Coprime (f * 2 ^ n) := by
      obtain ⟨h1, h2⟩ := Nat.coprime_mul_iff_right.mp hcfl
      exact Nat.coprime_mul_iff_right.mpr ⟨h1, h2.pow_right n⟩
    have hcore := core 2 (ZMod (f * 2 ^ n))ˣ (Cl L) (cycRep (f * 2 ^ n) L) (-1) γ
      (clA (f * 2 ^ n) L (-1)) (clA (f * 2 ^ n) L γ) (thetaH (f * 2 ^ n) (2 * (f * 2) + 1)) N
      (by simp) (fun x => cycRep_apply _ _ _ x) (fun x => cycRep_apply _ _ _ x)
      (stickH _ _ L hcM hcodd hM2) hγmem
    have hamb := hB n L γ (by omega) hγ1
    have hbound : Nat.card ↥(difR (clA (f * 2 ^ n) L (-1)) ⊓ torK (Cl L) 2) ≤ B ^ N :=
      hcore.trans (Nat.pow_le_pow_left hamb N)
    have hfodd : Odd f := Nat.coprime_two_right.mp hf
    obtain ⟨_, hcE2⟩ := conjEq (f * 2 ^ n) L
    have hsgn := sgnCyc f n (2 * (f * 2) + 1) N L γ hfodd h1 (by omega) hcM hcodd hγmem
    rw [← hcE2, hγidx] at hsgn
    have hinv : ∀ x : Cl L, clA (f * 2 ^ n) L (-1) (clA (f * 2 ^ n) L (-1) x) = x := by
      intro x
      apply Additive.ofMul.injective
      rw [← cycRep_apply, ← cycRep_apply, ← Module.End.mul_apply, ← map_mul]
      simp
    have hp := pTwo (Cl L) (clA (f * 2 ^ n) L (-1)) hinv
    exact hp.trans (Nat.pow_le_pow_left (Nat.mul_le_mul hsgn hbound) 2)
  · refine ⟨l * (B ^ N) ^ 2, n₀, ?_⟩
    intro n hn L _ _ _
    haveI : NeZero (f * l ^ n) := ⟨(Nat.mul_pos hf0 (pow_pos hl0 n)).ne'⟩
    have hl3 : 3 ≤ l := by
      have := hl.out.two_le
      omega
    have hM2 : 2 < f * l ^ n := by
      have : 3 ≤ l ^ n := by
        calc 3 ≤ l := hl3
          _ = l ^ 1 := (pow_one l).symm
          _ ≤ l ^ n := Nat.pow_le_pow_right hl0 (by omega)
      nlinarith
    haveI : IsCMField L := IsCyclotomicExtension.Rat.isCMField L ⟨f * l ^ n, Set.mem_singleton _, hM2⟩
    refine ⟨inferInstance, ?_⟩
    obtain ⟨γ, hγ1, _, hγmem⟩ := hmem n hn
    have hcM : (2 * (f * l) + 1).Coprime (f * l ^ n) := by
      obtain ⟨h1, h2⟩ := Nat.coprime_mul_iff_right.mp hcfl
      exact Nat.coprime_mul_iff_right.mpr ⟨h1, h2.pow_right n⟩
    have hcore := core l (ZMod (f * l ^ n))ˣ (Cl L) (cycRep (f * l ^ n) L) (-1) γ
      (clA (f * l ^ n) L (-1)) (clA (f * l ^ n) L γ) (thetaH (f * l ^ n) (2 * (f * l) + 1)) N
      (by simp) (fun x => cycRep_apply _ _ _ x) (fun x => cycRep_apply _ _ _ x)
      (stickH _ _ L hcM hcodd hM2) hγmem
    have hamb := hB n L γ (by omega) hγ1
    have hbound : Nat.card ↥(difR (clA (f * l ^ n) L (-1)) ⊓ torK (Cl L) l) ≤ B ^ N :=
      hcore.trans (Nat.pow_le_pow_left hamb N)
    have hlodd : Odd l := hl.out.odd_of_ne_two hl2
    obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ L (Set.mem_singleton (f * l ^ n))
      (NeZero.ne _)
    have hsplit : f * l ^ n = f * l ^ (n - 1) * l := by
      rw [mul_assoc, ← pow_succ]
      congr 2
      omega
    have hζl : IsPrimitiveRoot (ζ ^ (f * l ^ (n - 1))) l := hζ.pow (NeZero.pos _) hsplit
    obtain ⟨_, hcE2⟩ := conjEq (f * l ^ n) L
    have hrefl := reflOdd L l _ hl2 hζl
    rw [← hcE2] at hrefl
    have hp := pOdd l (Cl L) (clA (f * l ^ n) L (-1)) hlodd hrefl
    exact hp.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbound 2))

theorem UpperTheory.V.FW.ferreroWashington : UpperTheory.V.Published.FerreroWashington := by
  unfold UpperTheory.V.Published.FerreroWashington
  intro l _ K _ _ _ _
  obtain ⟨f, D, hf, h1, hemb⟩ := embed l K
  obtain ⟨B, n₀, hB⟩ := cyc l f hf h1
  refine ⟨D * l ^ n₀ * B, ?_⟩
  intro n K' _ _ _ _
  obtain ⟨m, L, iF, iN, iA, iC, hm, hdeg⟩ := hemb n n₀ K'
  obtain ⟨htc, hidx⟩ := hB m hm L
  have hd := desc l K' L htc
  have hl2 : 1 < l := (Fact.out : l.Prime).one_lt
  have key : Nat.card (ClassGroup (𝓞 K') ⧸ (powMonoidHom l).range) ≤ D * l ^ n₀ * B := by
    have e : Nat.card (ClassGroup (𝓞 K') ⧸ (powMonoidHom l).range) = (powR (Cl K') l).index := rfl
    rw [e]
    exact hd.trans (Nat.mul_le_mul hdeg hidx)
  exact key.trans (Nat.lt_pow_self hl2).le
