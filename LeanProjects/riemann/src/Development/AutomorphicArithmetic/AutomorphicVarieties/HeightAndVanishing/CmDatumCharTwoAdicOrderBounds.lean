import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.OrdProjNDvd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostSb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem arith (l a o : ℕ) (hl : l.Prime) (hl2 : l ≠ 2) (ho : 0 < o) (ha : a ∣ 2 * o) (hla : ¬ l ∣ a) :
    0 < orderOf (l : ZMod (Nat.lcm 4 a)) ∧ 2 ≤ (l ^ orderOf (l : ZMod (Nat.lcm 4 a)) - 1).factorization 2 ∧
      2 ^ (l ^ orderOf (l : ZMod (Nat.lcm 4 a)) - 1).factorization 2 < l ^ Nat.totient (4 * o) := by
  have hl3 : 3 ≤ l := by
    have := hl.two_le
    omega
  set M := Nat.lcm 4 a with hM
  have hMdvd : M ∣ 4 * o :=
    Nat.lcm_dvd (Dvd.intro o rfl) (ha.trans (Nat.mul_dvd_mul_right (by norm_num : 2 ∣ 4) o))
  have hMpos : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · rw [h0] at hMdvd
      have := Nat.eq_zero_of_zero_dvd hMdvd
      omega
    · exact h0
  have hcop : l.Coprime M := by
    rw [hl.coprime_iff_not_dvd]
    intro hdvd
    have h4a : l ∣ 4 * a := hdvd.trans (Nat.lcm_dvd (dvd_mul_right 4 a) (dvd_mul_left a 4))
    rcases (Nat.Prime.dvd_mul hl).mp h4a with h4 | ha'
    · exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp
        (hl.dvd_of_dvd_pow (show l ∣ 2 ^ 2 by simpa using h4)))
    · exact hla ha'
  have hpow : (l : ZMod M) ^ Nat.totient M = 1 := by
    have h1 := Nat.ModEq.pow_totient hcop
    have h2 : ((l ^ Nat.totient M : ℕ) : ZMod M) = ((1 : ℕ) : ZMod M) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1
    simpa using h2
  have htot : 0 < Nat.totient M := Nat.totient_pos.2 hMpos
  have hfpos : 0 < orderOf (l : ZMod M) :=
    orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨_, htot, hpow⟩)
  set f := orderOf (l : ZMod M) with hf
  have hlf : (l : ZMod M) ^ f = 1 := pow_orderOf_eq_one _
  have hmod : l ^ f ≡ 1 [MOD M] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    exact hlf
  have h4 : 4 ∣ l ^ f - 1 := by
    have hM4 : 4 ∣ M := Nat.dvd_lcm_left 4 a
    exact hM4.trans ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp hmod.symm)
  have hne : l ^ f - 1 ≠ 0 := by
    have : l ≤ l ^ f := Nat.le_self_pow (by omega) l
    omega
  have hv : 2 ≤ (l ^ f - 1).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hne).mp (by simpa using h4)
  have hfle : f ≤ Nat.totient (4 * o) := by
    have h1 : f ∣ Nat.totient M := orderOf_dvd_of_pow_eq_one hpow
    have h2 : Nat.totient M ∣ Nat.totient (4 * o) := Nat.totient_dvd_of_dvd hMdvd
    exact Nat.le_of_dvd (Nat.totient_pos.2 (by omega)) (h1.trans h2)
  refine ⟨hfpos, hv, ?_⟩
  calc 2 ^ (l ^ f - 1).factorization 2 ≤ l ^ f - 1 := Nat.le_of_dvd (by omega) (Nat.ordProj_dvd _ _)
    _ < l ^ f := by omega
    _ ≤ l ^ Nat.totient (4 * o) := Nat.pow_le_pow_right (by omega) hfle

theorem UpperTheory.V.HV.cmDatum_char_two_adic_order_bounds :
    ∀ (h : Host) (O : Type) [CommRing O] [IsDomain O] (ψ : DirichletCharacter O h.N), h.IsChar ψ → ∀ l, l.Prime → l ≠ 2 →
      0 < f0 l ψ ∧ 2 ≤ n0 l ψ ∧ 2 ^ n0 l ψ < l ^ Nat.totient (4 * h.o) ∧ h.R1 l ψ ≤ 16 * h.o * (l * h.q) ^ 2 * l ^ (2 * Nat.totient (4 * h.o)) ∧
      (h.R1 l ψ ≤ 2 ^ c2 ψ → 12 ≤ c2 ψ ∧ ∀ v ∈ Tb l ψ, 8 * h.o * v ^ 2 < 2 ^ c2 ψ) := by
  intro h O _ _ ψ hψ l hl hl2
  have ho : 0 < h.o := by
    haveI := h.chi.ne
    exact orderOf_pos _
  have hq : 0 < h.q := Nat.pos_of_neZero h.q
  have hl3 : 3 ≤ l := by
    have := hl.two_le
    omega
  have hlq : 0 < l * h.q := Nat.mul_pos (by omega) hq
  obtain ⟨-, -, ha, hla, -⟩ := hostTh1 h O ψ hψ l hl hl2
  obtain ⟨hf, hn, hlt⟩ := arith l (orderOf (th1 l ψ)) h.o hl hl2 ho ha hla
  have hn' : 2 ≤ n0 l ψ := hn
  have hlt' : 2 ^ n0 l ψ < l ^ Nat.totient (4 * h.o) := hlt
  have hR1 : h.R1 l ψ = 16 * h.o * (l * h.q) ^ 2 * 4 ^ n0 l ψ := rfl
  have hR : h.R1 l ψ ≤ 16 * h.o * (l * h.q) ^ 2 * l ^ (2 * Nat.totient (4 * h.o)) := by
    rw [hR1]
    apply Nat.mul_le_mul_left
    calc 4 ^ n0 l ψ = (2 ^ n0 l ψ) ^ 2 := by
          rw [← pow_mul', pow_mul]
          norm_num
      _ ≤ (l ^ Nat.totient (4 * h.o)) ^ 2 := Nat.pow_le_pow_left hlt'.le 2
      _ = l ^ (2 * Nat.totient (4 * h.o)) := (pow_mul' l 2 _).symm
  refine ⟨hf, hn', hlt', hR, fun hc => ?_⟩
  have hpos : 0 < h.o * (l * h.q) ^ 2 := Nat.mul_pos ho (pow_pos hlq 2)
  have h4 : 16 ≤ 4 ^ n0 l ψ := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ 4 ^ n0 l ψ := Nat.pow_le_pow_right (by norm_num) hn'
  constructor
  · have h9 : 9 ≤ (l * h.q) ^ 2 := by
      have h3 : 3 ≤ l * h.q := le_trans hl3 (Nat.le_mul_of_pos_right l hq)
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ (l * h.q) ^ 2 := Nat.pow_le_pow_left h3 2
    have hbig : 2 ^ 11 < 2 ^ c2 ψ := by
      calc 2 ^ 11 < 16 * 1 * 9 * 16 := by norm_num
        _ ≤ 16 * h.o * (l * h.q) ^ 2 * 4 ^ n0 l ψ :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl (show 1 ≤ h.o from ho)) h9) h4
        _ = h.R1 l ψ := hR1.symm
        _ ≤ 2 ^ c2 ψ := hc
    by_contra hlt2
    have hle : 2 ^ c2 ψ ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · intro v hv
    have hvd : v ∣ l * h.q := (hostSb h O ψ hψ l hl hl2).2.2.2.2 v hv
    have hvle : v ≤ l * h.q := Nat.le_of_dvd hlq hvd
    have h8 : 8 < 16 * 4 ^ n0 l ψ := by omega
    calc 8 * h.o * v ^ 2 ≤ 8 * h.o * (l * h.q) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hvle 2)
      _ = (h.o * (l * h.q) ^ 2) * 8 := by ring
      _ < (h.o * (l * h.q) ^ 2) * (16 * 4 ^ n0 l ψ) := Nat.mul_lt_mul_of_pos_left h8 hpos
      _ = 16 * h.o * (l * h.q) ^ 2 * 4 ^ n0 l ψ := by ring
      _ = h.R1 l ψ := hR1.symm
      _ ≤ 2 ^ c2 ψ := hc
