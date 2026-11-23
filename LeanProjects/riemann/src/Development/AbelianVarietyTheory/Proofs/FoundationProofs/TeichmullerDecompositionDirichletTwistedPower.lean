import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ChSumSubCMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSubOnePowThreeLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumUnitsPrimePowTeichmullerReindex

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

namespace GlobalTheory.TeichDec

variable {l : ℕ} [Fact l.Prime]

noncomputable def emb (l : ℕ) [Fact l.Prime] : ℤ_[l] →+* Qbar l := (algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom

theorem norm_emb (x : ℤ_[l]) : ‖emb l x‖ = ‖x‖ := PadicAlgCl.norm_extends l (x : ℚ_[l])

theorem norm_emb_le_of_dvd {d x : ℤ_[l]} (h : d ∣ x) : ‖emb l x‖ ≤ ‖emb l d‖ := by
  obtain ⟨y, rfl⟩ := h
  rw [map_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (by rw [norm_emb]; exact PadicInt.norm_le_one y)

theorem norm_l_lt_one : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [map_natCast] at h
  rw [h]
  exact Padic.norm_p_lt_one

theorem norm_eq_one_of_pow {x : Qbar l} (hx : x ^ (l - 1) = 1) : ‖x‖ = 1 := by
  have h2 := (Fact.out : l.Prime).two_le
  have h1 := congrArg norm hx
  rw [norm_pow, norm_one] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 h1

theorem eq_of_pow_eq_one {x y : Qbar l} (hx : x ^ (l - 1) = 1) (hy : y ^ (l - 1) = 1) (h : ‖x - y‖ < 1) : x = y := by
  have h2 := (Fact.out : l.Prime).two_le
  by_contra hne
  have hx1 := norm_eq_one_of_pow hx
  have hy1 := norm_eq_one_of_pow hy
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy1
  set z := x / y with hz
  have hz1 : z ^ (l - 1) = 1 := by rw [hz, div_pow, hx, hy, div_one]
  have hzn : ‖z‖ = 1 := norm_eq_one_of_pow hz1
  have hzne : z - 1 ≠ 0 := by
    intro h0
    exact hne ((div_eq_one_iff_eq hy0).1 (sub_eq_zero.1 h0))
  have hzd : ‖z - 1‖ = ‖x - y‖ := by
    have : z - 1 = (x - y) / y := by rw [hz]; field_simp
    rw [this, norm_div, hy1, div_one]
  have hs : ∑ i ∈ Finset.range (l - 1), z ^ i = 0 := by
    have := geom_sum_mul z (l - 1)
    rw [hz1, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right hzne
  have hb : ‖∑ i ∈ Finset.range (l - 1), (z ^ i - 1)‖ ≤ ‖z - 1‖ := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
    rw [← geom_sum_mul, norm_mul]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    rw [norm_pow, hzn, one_pow]
  have hsum : (1 : Qbar l) = (l : Qbar l) + ∑ i ∈ Finset.range (l - 1), (z ^ i - 1) := by
    rw [Finset.sum_sub_distrib, hs, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_sub (by omega)]
    push_cast
    ring
  have h3 := IsUltrametricDist.norm_add_le_max (l : Qbar l) (∑ i ∈ Finset.range (l - 1), (z ^ i - 1))
  rw [← hsum, norm_one] at h3
  exact absurd h3 (not_le.2 (max_lt norm_l_lt_one (hb.trans_lt (hzd ▸ h))))

theorem norm_natCast_eq_one {n : ℕ} (hn : ¬ l ∣ n) : ‖(n : ℤ_[l])‖ = 1 := by
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => hn ?_)
  have h1 : ‖((n : ℤ) : ℤ_[l])‖ < 1 := by simpa using h
  exact Int.natCast_dvd_natCast.1 ((PadicInt.norm_int_lt_one_iff_dvd _).1 h1)

theorem exists_root {c : ℕ} (hc : ¬ l ∣ c) : ∃ z : ℤ_[l], z ^ (l - 1) = 1 ∧ (l : ℤ_[l]) ∣ z - c := by
  have hp : l.Prime := Fact.out
  have h2 := hp.two_le
  have hd : ‖Polynomial.aeval (c : ℤ_[l]) (Polynomial.derivative (Polynomial.X ^ (l - 1) - 1 : Polynomial ℤ_[l]))‖ = 1 := by
    have : Polynomial.aeval (c : ℤ_[l]) (Polynomial.derivative (Polynomial.X ^ (l - 1) - 1 : Polynomial ℤ_[l]))
        = (((l - 1) * c ^ (l - 1 - 1) : ℕ) : ℤ_[l]) := by
      simp [Polynomial.derivative_X_pow]
    rw [this]
    refine norm_natCast_eq_one fun h => ?_
    rcases (hp.dvd_mul).1 h with h | h
    · exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
    · exact hc (hp.dvd_of_dvd_pow h)
  have hv : ‖Polynomial.aeval (c : ℤ_[l]) (Polynomial.X ^ (l - 1) - 1 : Polynomial ℤ_[l])‖ < 1 := by
    have : Polynomial.aeval (c : ℤ_[l]) (Polynomial.X ^ (l - 1) - 1 : Polynomial ℤ_[l])
        = (((c : ℤ) ^ (l - 1) - 1 : ℤ) : ℤ_[l]) := by
      simp
    rw [this, PadicInt.norm_int_lt_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card_sub_one_eq_one (by rwa [Ne, ZMod.natCast_eq_zero_iff]), sub_self]
  obtain ⟨z, hz, hz1, -⟩ := hensels_lemma (F := (Polynomial.X ^ (l - 1) - 1 : Polynomial ℤ_[l])) (a := (c : ℤ_[l]))
    (by rw [hd, one_pow]; exact hv)
  rw [hd] at hz1
  refine ⟨z, ?_, (PadicInt.norm_lt_one_iff_dvd _).1 hz1⟩
  simpa [sub_eq_zero] using hz

theorem exists_decomp (hl : l ≠ 2) (R : ℕ) {j : ℕ} (hj : ¬ l ∣ j) :
    ∃ c t : ℕ, ¬ l ∣ c ∧ j ≡ c ^ (l ^ R) * (1 + l) ^ t [MOD l ^ (R + 1)] := by
  classical
  have hp : l.Prime := Fact.out
  haveI : NeZero (l ^ (R + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have h := GlobalTheory.sum_units_primePow_teichmuller_reindex l hl R ℕ
    (fun x => if x = (j : ZMod (l ^ (R + 1))) then 1 else 0)
  have hcop : Nat.Coprime j (l ^ (R + 1)) := Nat.Coprime.pow_right _ ((hp.coprime_iff_not_dvd).2 hj).symm
  have hne : ∑ b : (ZMod (l ^ (R + 1)))ˣ, (if (b : ZMod (l ^ (R + 1))) = (j : ZMod (l ^ (R + 1))) then 1 else 0 : ℕ) ≠ 0 := by
    intro h0
    have := Finset.sum_eq_zero_iff.1 h0 (ZMod.unitOfCoprime j hcop) (Finset.mem_univ _)
    simp at this
  rw [h] at hne
  obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  refine ⟨(c : ZMod l).val, t, fun hd => ?_, ?_⟩
  · have h0 : (((c : ZMod l).val : ℕ) : ZMod l) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hd
    rw [ZMod.natCast_zmod_val] at h0
    exact c.ne_zero h0
  · refine ((ZMod.natCast_eq_natCast_iff _ _ _).1 ?_).symm
    by_contra h1
    exact ht (if_neg h1)

theorem dvd_of_modEq {n a b : ℕ} (h : a ≡ b [MOD n]) : (n : ℤ_[l]) ∣ (b : ℤ_[l]) - a := by
  have h1 := map_dvd (Int.castRingHom ℤ_[l]) (Nat.modEq_iff_dvd.1 h)
  simpa using h1

theorem teich : ∀ (l : ℕ) [Fact l.Prime] (φ : DirichletCharacter (Qbar l) l) (e R j : ℕ), l ≠ 2 →
    ∃ (ε : Qbar l) (t : ℕ), (ε = 0 ∨ ε ^ (l - 1) = 1) ∧
      Cg R (φ (j : ZMod l) * (j : Qbar l) ^ e) (ε * ((1 + (l : Qbar l)) ^ e) ^ t) ∧
      ∀ m, 1 ≤ m → m ≤ R → ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), InComp φ e ψ →
        ψ⁻¹ (j : ZMod (l ^ m)) = ε * (ψ⁻¹ (1 + (l : ZMod (l ^ m)))) ^ t := by
  intro l _ φ e R j hl
  have hp : l.Prime := Fact.out
  by_cases hj : l ∣ j
  · refine ⟨0, 0, Or.inl rfl, ?_, fun m hm _ ψ _ => ?_⟩
    · rw [(ZMod.natCast_eq_zero_iff _ _).2 hj, MulChar.map_nonunit _ not_isUnit_zero]
      simp [Cg]
    · rw [zero_mul]
      refine MulChar.map_nonunit _ fun hu => ?_
      have h1 := (ZMod.isUnit_iff_coprime _ _).1 hu
      have h2 : l ∣ Nat.gcd j (l ^ m) := Nat.dvd_gcd hj (dvd_pow_self l (by omega))
      rw [h1] at h2
      exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  obtain ⟨c, t, hc, hjc⟩ := exists_decomp hl R hj
  obtain ⟨z, hz, hzc⟩ := exists_root hc
  set b : ℕ := c ^ (l ^ R) with hb
  set w : ℤ_[l] := z ^ (l ^ R) with hw
  have hw1 : w ^ (l - 1) = 1 := by rw [hw, ← pow_mul, mul_comm, pow_mul, hz, one_pow]
  have hwb : (l : ℤ_[l]) ^ (R + 1) ∣ w - b := by
    have := dvd_sub_pow_of_dvd_sub hzc R
    rw [hb]; push_cast; exact this
  have hj0 : (j : ZMod l) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hφ : φ (j : ZMod l) ^ (l - 1) = 1 := by rw [← map_pow, ZMod.pow_card_sub_one_eq_one hj0, map_one]
  have hφn := norm_eq_one_of_pow hφ
  have hε : (emb l w ^ e * φ (j : ZMod l)) ^ (l - 1) = 1 := by
    rw [mul_pow, hφ, mul_one, ← pow_mul, mul_comm, pow_mul, ← map_pow, hw1, map_one, one_pow]
  refine ⟨emb l w ^ e * φ (j : ZMod l), t, Or.inr hε, ?_, fun m hm hmR ψ hψ => ?_⟩
  · have h1 : (l : ℤ_[l]) ^ (R + 1) ∣ (j : ℤ_[l]) - w * (1 + l) ^ t := by
      have h2 := dvd_of_modEq (l := l) hjc.symm
      push_cast at h2
      have h3 : (j : ℤ_[l]) - w * (1 + l) ^ t = (j - b * (1 + l) ^ t) - (w - b) * (1 + l) ^ t := by ring
      rw [h3]
      exact dvd_sub h2 (hwb.mul_right _)
    have h4 : (l : ℤ_[l]) ^ R ∣ (j : ℤ_[l]) ^ e - (w * (1 + l) ^ t) ^ e :=
      ((pow_dvd_pow _ (Nat.le_succ R)).trans h1).trans (sub_dvd_pow_sub_pow _ _ _)
    have h5 := norm_emb_le_of_dvd h4
    simp only [map_sub, map_pow, map_mul, map_add, map_one, map_natCast] at h5
    unfold Cg
    have h6 : φ (j : ZMod l) * (j : Qbar l) ^ e - emb l w ^ e * φ (j : ZMod l) * ((1 + (l : Qbar l)) ^ e) ^ t
        = φ (j : ZMod l) * ((j : Qbar l) ^ e - (emb l w * (1 + (l : Qbar l)) ^ t) ^ e) := by ring
    rw [h6, norm_mul, hφn, one_mul]
    exact h5
  · haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hp.ne_zero⟩
    have hmd : l ^ m ∣ l ^ (R + 1) := pow_dvd_pow _ (by omega)
    have hld : l ∣ l ^ m := dvd_pow_self l (by omega)
    have hcc : Nat.Coprime c l := ((hp.coprime_iff_not_dvd).2 hc).symm
    have hbcop : Nat.Coprime b (l ^ m) := Nat.Coprime.pow _ _ hcc
    have hb1 : b ^ (l - 1) ≡ 1 [MOD l ^ m] := by
      have h1 := Nat.ModEq.pow_totient (Nat.Coprime.pow_right (R + 1) hcc)
      rw [Nat.totient_prime_pow_succ hp, pow_mul] at h1
      exact h1.of_dvd hmd
    have hb2 : (b : ZMod (l ^ m)) ^ (l - 1) = 1 := by
      have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hb1
      simpa using this
    have hu : ZMod.unitOfCoprime b hbcop ^ (l - 1) = 1 := Units.ext (by simpa using hb2)
    have h7 := hψ _ hu
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast] at h7
    have hvb : b % l ^ m ≡ b [MOD l] := (Nat.mod_modEq b (l ^ m)).of_dvd hld
    have hbj : (b : ZMod l) = (j : ZMod l) := by
      have := (ZMod.natCast_eq_natCast_iff _ _ _).2 (hjc.of_dvd (dvd_pow_self l (Nat.succ_ne_zero R)))
      rw [this]; push_cast; simp
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 hvb, hbj] at h7
    have h8 : (l : ℤ_[l]) ∣ ((b % l ^ m : ℕ) : ℤ_[l]) ^ e - w ^ e := by
      refine Dvd.dvd.trans ?_ (sub_dvd_pow_sub_pow _ _ _)
      have h2 := dvd_of_modEq (l := l) hvb.symm
      have h3 : ((b % l ^ m : ℕ) : ℤ_[l]) - w = (((b % l ^ m : ℕ) : ℤ_[l]) - b) - (w - b) := by ring
      rw [h3]
      exact dvd_sub h2 ((dvd_pow_self _ (Nat.succ_ne_zero R)).trans hwb)
    have h9 := (norm_emb_le_of_dvd h8).trans_lt (by rw [map_natCast]; exact norm_l_lt_one)
    rw [map_sub, map_pow, map_pow, map_natCast] at h9
    have hψb : ψ⁻¹ (b : ZMod (l ^ m)) ^ (l - 1) = 1 := by rw [← map_pow, hb2, map_one]
    have h10 : ψ⁻¹ (b : ZMod (l ^ m)) = emb l w ^ e * φ (j : ZMod l) := by
      refine eq_of_pow_eq_one hψb hε ?_
      have h3 : ψ⁻¹ (b : ZMod (l ^ m)) - emb l w ^ e * φ (j : ZMod l) =
          (ψ⁻¹ (b : ZMod (l ^ m)) - ((b % l ^ m : ℕ) : Qbar l) ^ e * φ (j : ZMod l)) +
            (((b % l ^ m : ℕ) : Qbar l) ^ e - emb l w ^ e) * φ (j : ZMod l) := by ring
      rw [h3]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h7 ?_)
      rw [norm_mul, hφn, mul_one]
      exact h9
    rw [← h10, ← map_pow, ← map_mul, (ZMod.natCast_eq_natCast_iff _ _ _).2 (hjc.of_dvd hmd)]
    push_cast
    rfl

end GlobalTheory.TeichDec
