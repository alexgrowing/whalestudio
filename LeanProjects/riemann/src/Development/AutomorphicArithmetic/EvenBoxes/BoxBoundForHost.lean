import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AutomorphicArithmetic.CharacterBoxes.RealSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KroneckerTwoNegEqJacobiSymTwo
import Development.AutomorphicArithmetic.MeanSquareBounds.IndUnique
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.HC GlobalTheory.EX UpperTheory.Top

private theorem boxH_dvd (C N : ℕ) [NeZero N] (hC : C ≠ 0) (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive)
    (f : (ZMod C)ˣ →* ℂˣ)
    (h : ∀ (a : ℕ) (h : a.Coprime C), χ (a : ZMod N) = ((f (ZMod.unitOfCoprime a h) : ℂˣ) : ℂ)) : N ∣ C := by
  haveI : NeZero C := ⟨hC⟩
  let η : DirichletCharacter ℂ C := MulChar.ofUnitHom f
  haveI : NeZero η.conductor := ⟨η.conductor_ne_zero⟩
  have he := QH.ind_unique N η.conductor C χ η.primitiveCharacter hC hp η.primitiveCharacter_isPrimitive (fun n hn => by
    have h1 := η.primitiveCharacter_apply_of_isCoprime (a := (n : ℤ)) (Nat.isCoprime_iff_coprime.2 hn)
    have h2 : η.primitiveCharacter (n : ZMod η.conductor) = η (n : ZMod C) := by simpa using h1
    rw [h n hn, h2, ← ZMod.coe_unitOfCoprime n hn]
    exact (MulChar.ofUnitHom_coe f _).symm)
  have heN : N = η.conductor := congrArg Sigma.fst he
  rw [heN]
  exact η.conductor_dvd_level

private theorem boxH_jac {x p : ℕ} (h : x ≡ 1 [MOD p]) : jacobiSym (x : ℤ) p = 1 := by
  rw [jacobiSym.mod_left' (a₂ := 1) (by exact_mod_cast h), jacobiSym.one_left]

private theorem boxH_even (R : Ranks) (H : Host R) (hinj : Function.Injective R.h) (hQ : H.QS = 2 ^ (R.e + 2)) :
    ∃ (a : ℕ) (h : a.Coprime H.condN), a % 8 = 7 ∧ a ≡ 1 [MOD H.q] ∧ a ≡ 1 [MOD H.d] ∧
      H.art (ZMod.unitOfCoprime a h) = 1 := by
  have hcop : (2 ^ (R.e + 2)).Coprime (H.q * H.d) := hQ ▸ H.QS_coprime
  have hpos : 1 ≤ 2 ^ (R.e + 2) := Nat.one_le_two_pow
  obtain ⟨a, h1, h2⟩ := Nat.chineseRemainder hcop (2 ^ (R.e + 2) - 1) 1
  have hN : H.condN = 2 ^ (R.e + 2) * (H.q * H.d) := by
    rw [← hQ, ← mul_assoc]
  have hc : a.Coprime H.condN := by
    rw [hN]
    refine Nat.Coprime.mul_right ?_ ?_
    · unfold Nat.Coprime; rw [h1.gcd_eq]
      exact (Nat.coprime_self_sub_left hpos).2 (by simp)
    · unfold Nat.Coprime; rw [h2.gcd_eq]; simp
  have hv : ((ZMod.unitOfCoprime a hc : (ZMod H.condN)ˣ) : ZMod H.condN).val ≡ a [MOD H.condN] := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact Nat.mod_modEq _ _
  have hq : a ≡ 1 [MOD H.q] := h2.of_dvd (dvd_mul_right _ _)
  have hd : a ≡ 1 [MOD H.d] := h2.of_dvd (dvd_mul_left _ _)
  have h8 : 8 ∣ 2 ^ (R.e + 2) := pow_dvd_pow 2 (m := 3) (by have := H.two_le_e; omega)
  refine ⟨a, hc, ?_, hq, hd, Prod.ext (Prod.ext ?_ ?_) ?_⟩
  · have h3 : a % 8 = (2 ^ (R.e + 2) - 1) % 8 := h1.of_dvd h8
    omega
  · apply Units.ext
    rw [H.flPS, boxH_jac ((hv.of_dvd (by rw [hN]; exact (dvd_mul_right _ _).mul_left _)).trans hq)]
    rfl
  · apply Units.ext
    rw [H.der.art_ch, boxH_jac ((hv.of_dvd (by rw [hN]; exact (dvd_mul_left _ _).mul_left _)).trans hd)]
    rfl
  · have h3 := H.art_h (ZMod.unitOfCoprime a hc) (-1) (by
      rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 ((hv.of_dvd (by rw [hN]; exact dvd_mul_right _ _)).trans h1),
        Nat.cast_sub hpos, ZMod.natCast_self]
      simp)
    have h4 : Formalism.FrobeniusOrbits.hcl R.e (-1) = 1 :=
      (Formalism.FrobeniusOrbits.hcl_eq_hcl_iff (e := R.e) (u := -1) (v := 1)).2 (Or.inr rfl)
    rw [h4, Frame.hH_apply] at h3
    have h5 : R.h (R.iotaInv (H.art (ZMod.unitOfCoprime a hc)).2) = R.h 0 := by
      rw [map_zero]; exact h3
    exact hinj h5

private theorem boxH_rho (ρ : Formalism.HC.PChar) (h8 : ρ.N ∣ 8) (h7 : ρ.val 7 = 1) :
    (∀ a : ℕ, a % 2 = 1 → ρ.val a = 1) ∨ (∀ a : ℕ, a % 2 = 1 → ρ.val a = GlobalTheoryTheory.chi8 a) := by
  have hm : ∀ a : ℕ, ρ.val a = ρ.val (a % 8) := fun a =>
    congrArg ρ.χ ((ZMod.natCast_eq_natCast_iff _ _ _).2 ((Nat.mod_modEq a 8).symm.of_dvd h8))
  have hmul : ∀ a b : ℕ, ρ.val (a * b) = ρ.val a * ρ.val b := fun a b => by
    show ρ.χ ((a * b : ℕ) : ZMod ρ.N) = ρ.χ (a : ZMod ρ.N) * ρ.χ (b : ZMod ρ.N)
    rw [Nat.cast_mul, map_mul]
  have h1 : ρ.val 1 = 1 := by
    show ρ.χ ((1 : ℕ) : ZMod ρ.N) = 1
    rw [Nat.cast_one, map_one]
  have h5 : ρ.val 5 = ρ.val 3 := by
    have := hmul 3 7
    rw [hm, h7, mul_one] at this
    exact this
  have h3 : ρ.val 3 * ρ.val 3 = 1 := by
    rw [← hmul, hm]; exact h1
  have hc : ∀ a : ℕ, a % 2 = 1 → GlobalTheoryTheory.chi8 a = ((ZMod.χ₈ ((a % 8 : ℕ) : ZMod 8) : ℤ) : ℂ) := fun a ha => by
    rw [GlobalTheoryTheory.chi8, GlobalTheoryTheory.kron, GlobalTheory.kronSym_neg_eq_jacobiSym_and_two.2 a (Nat.odd_iff.2 ha), ZMod.natCast_mod]
  rcases mul_self_eq_one_iff.1 h3 with h | h
  · left
    intro a ha
    rw [hm]
    have : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by omega
    rcases this with e | e | e | e <;> rw [e] <;> simp only [h1, h5, h, h7]
  · right
    intro a ha
    rw [hm, hc a ha]
    have : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by omega
    have c1 : ZMod.χ₈ ((1 : ℕ) : ZMod 8) = 1 := by decide
    have c3 : ZMod.χ₈ ((3 : ℕ) : ZMod 8) = -1 := by decide
    have c5 : ZMod.χ₈ ((5 : ℕ) : ZMod 8) = -1 := by decide
    have c7 : ZMod.χ₈ ((7 : ℕ) : ZMod 8) = 1 := by decide
    rcases this with e | e | e | e <;> rw [e] <;>
      simp only [h1, h5, h, h7, c1, c3, c5, c7, Int.cast_one, Int.cast_neg]

theorem UpperTheory.box_bound_for_host :
    ∀ (R : Ranks) (H : Host R) (Y eps : ℝ), Function.Injective R.h → H.QS = 2 ^ (R.e + 2) → Boxq Y eps H.q H.d → BoxH H Y eps := by
  intro R H Y eps hinj hQ hB N _ χ hχ hr
  obtain ⟨hp, ψ, hψ⟩ := hχ
  have hq := H.hyp.1
  have hd := H.hyp.2.1
  have hq4 : H.q % 4 = 3 := by have := H.hyp.2.2.1; omega
  have hd4 : H.d % 4 = 3 := by have := H.hyp.2.2.2.1; omega
  have hqd : H.q ≠ H.d := by have := H.hyp.2.2.1; have := H.hyp.2.2.2.1; omega
  have hS : 0 < H.QS := H.QS_pos
  have hN : N ∣ H.condN := boxH_dvd _ N (mul_ne_zero (mul_ne_zero hS.ne' hq.ne_zero) hd.ne_zero) χ hp (ψ.comp H.art) hψ
  have hoc : ordCompl[2] H.QS = 1 := by
    rw [hQ, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same, Nat.div_self (by positivity)]
  obtain ⟨ρ, i, j, -, h8, hNe, hval⟩ := UpperTheory.Top.realSplit ⟨N, χ, hp⟩ H.QS H.q H.d hr hS hq hd (by omega) (by omega)
    hqd H.QS_coprime hN
  rw [hoc, mul_one] at h8
  have hNe' : N = ρ.N * H.q ^ (i : ℕ) * H.d ^ (j : ℕ) := hNe
  have hval' : ∀ a : ℕ, a.Coprime N → χ (a : ZMod N) = tw ρ.val H.q H.d i j a := hval
  have h7 : ρ.val 7 = 1 := by
    obtain ⟨a, hc, a8, aq, ad, ha⟩ := boxH_even R H hinj hQ
    have h1 := hψ a hc
    rw [ha, map_one, hval' a (hc.coprime_dvd_right hN), tw, boxH_jac aq, boxH_jac ad] at h1
    have h2 : ρ.val a = ρ.val (a % 8) :=
      congrArg ρ.χ ((ZMod.natCast_eq_natCast_iff _ _ _).2 ((Nat.mod_modEq a 8).symm.of_dvd h8))
    rw [← a8, ← h2]
    simpa using h1
  have hps : ∀ q a : ℕ, q % 4 = 3 → a % 2 = 1 → GlobalTheoryTheory.kron (-(q : ℤ)) a = ((jacobiSym (a : ℤ) q : ℤ) : ℂ) :=
    fun q a h ha => by rw [GlobalTheoryTheory.kron, GlobalTheory.kronSym_neg_eq_jacobiSym_and_two.1 q a h (by omega)]
  have hI : ∀ f : ℕ → ℂ, (∀ a : ℕ, a % 2 = 1 → tw ρ.val H.q H.d i j a = f a) →
      GlobalTheoryTheory.Induces χ f (8 * H.q * H.d) := fun f hf => ⟨hp, fun a ha => by
    have h2 : a.Coprime 2 := Nat.Coprime.coprime_dvd_right (Dvd.intro (4 * H.q * H.d) (by ring)) ha
    rw [← hf a (Nat.odd_iff.1 (Nat.coprime_two_right.1 h2))]
    refine hval' a ?_
    have c8 : a.Coprime 8 := ha.coprime_mul_right_right.coprime_mul_right_right
    have cq : a.Coprime H.q := ha.coprime_mul_right_right.coprime_mul_left_right
    have cd : a.Coprime H.d := ha.coprime_mul_left_right
    rw [hNe']
    exact ((c8.coprime_dvd_right h8).mul_right (cq.pow_right _)).mul_right (cd.pow_right _)⟩
  have h8p : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ ρ.N := fun p hp hp2 hd =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow (n := 3) (hd.trans h8)))
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hB
  rw [hoc, Nat.cast_one, mul_one]
  refine ⟨fun h => ?_, fun h h' => ?_⟩
  · have hj : j = 1 := by
      by_contra hj
      have hj0 : j = 0 := by omega
      subst hj0
      rw [hNe'] at h
      simp only [Fin.val_zero, pow_zero, mul_one] at h
      rcases (Nat.Prime.dvd_mul hd).1 h with h | h
      · exact h8p _ hd (by omega) h
      · exact hqd ((Nat.prime_dvd_prime_iff_eq hd hq).1 (hd.dvd_of_dvd_pow h)).symm
    subst hj
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl <;> rcases boxH_rho ρ h8 h7 with hρ | hρ
    · exact b3 N χ (hI _ fun a ha => by simp [tw, GlobalTheoryTheory.chDir, hρ a ha, hps _ a hd4 ha])
    · exact b4 N χ (hI _ fun a ha => by simp [tw, GlobalTheoryTheory.chDir, hρ a ha, hps _ a hd4 ha])
    · exact b5 N χ (hI _ fun a ha => by
        simp only [tw, GlobalTheoryTheory.chDir, GlobalTheoryTheory.psDir, hρ a ha, hps _ a hd4 ha, hps _ a hq4 ha, Fin.val_one]; ring)
    · exact b6 N χ (hI _ fun a ha => by
        simp only [tw, GlobalTheoryTheory.chDir, GlobalTheoryTheory.psDir, hρ a ha, hps _ a hd4 ha, hps _ a hq4 ha, Fin.val_one]; ring)
  · have hj : j = 0 := by
      by_contra hj
      have hj0 : j = 1 := by omega
      subst hj0
      exact h' (by rw [hNe']; simp)
    subst hj
    have hi : i = 1 := by
      by_contra hi
      have hi0 : i = 0 := by omega
      subst hi0
      rw [hNe'] at h
      simp only [Fin.val_zero, pow_zero, mul_one] at h
      exact h8p _ hq (by omega) h
    subst hi
    rcases boxH_rho ρ h8 h7 with hρ | hρ
    · exact b1 N χ (hI _ fun a ha => by simp [tw, GlobalTheoryTheory.psDir, hρ a ha, hps _ a hq4 ha])
    · exact b2 N χ (hI _ fun a ha => by simp [tw, GlobalTheoryTheory.psDir, hρ a ha, hps _ a hq4 ha])
