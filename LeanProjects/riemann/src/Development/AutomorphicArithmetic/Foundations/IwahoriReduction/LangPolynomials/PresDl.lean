import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.KumAlg
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.KumTriv
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.DvdOfNormLe
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PolyEx
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.WdVal
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.DlogCmp

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem mem_of_pow_mem {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {v : Ω} {N : ℕ} (hN : N ≠ 0)
    (h : v ^ N ∈ A) : v ∈ A := by
  rcases A.mem_or_inv_mem v with hv | hv
  · exact hv
  · by_cases h0 : v = 0
    · rw [h0]
      exact zero_mem A
    · obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
      have e : v = v ^ (m + 1) * v⁻¹ ^ m := by
        rw [pow_succ, inv_pow, mul_comm (v ^ m) v, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ h0), mul_one]
      rw [e]
      exact mul_mem h (pow_mem hv _)

private theorem coord_eq {l : ℕ} [Fact l.Prime] {c : Coef l} (β : Bas c) {n : ℕ} {z : Qbar l}
    (k k' : Fin β.d → ZMod (l ^ n)) (h : Cg n z (∑ i, β.val i * ((k i).val : Qbar l)))
    (h' : Cg n z (∑ i, β.val i * ((k' i).val : Qbar l))) (i : Fin β.d) : k i = k' i := by
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hB := ((pBasEx l c).2 β).2.1 n (fun i => ((k i).val : ℤ_[l]) - ((k' i).val : ℤ_[l])) ?_ i
  · obtain ⟨d, hd⟩ := hB
    have h2 := congrArg (PadicInt.toZModPow n) hd
    simp only [map_sub, map_natCast, map_mul, map_pow, ZMod.natCast_zmod_val] at h2
    have hl : ((l : ZMod (l ^ n))) ^ n = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    rw [hl, zero_mul, sub_eq_zero] at h2
    exact h2
  · unfold Cg at h h' ⊢
    simp only [map_sub, map_natCast, mul_sub, Finset.sum_sub_distrib, sub_zero]
    have key := (IsUltrametricDist.norm_add_le_max (z - ∑ i, β.val i * ((k' i).val : Qbar l))
      (-(z - ∑ i, β.val i * ((k i).val : Qbar l)))).trans (max_le h' (by rwa [norm_neg]))
    have e : (∑ x, β.val x * ((k x).val : Qbar l)) - ∑ x, β.val x * ((k' x).val : Qbar l)
        = (z - ∑ i, β.val i * ((k' i).val : Qbar l)) + -(z - ∑ i, β.val i * ((k i).val : Qbar l)) := by
      ring
    rw [e]
    exact key

private theorem ser_rel {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω}
    {j : Ω →+* Qbar l} (Φ : Fr l A j) (P P' Q : Polynomial (R0 A)) (N : ℕ) :
    Φ.ser (P - P' * Q ^ N) = Φ.ser P - Φ.ser P' * Φ.ser Q ^ N := by
  unfold Fr.ser
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.eval₂_sub,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow]

theorem UpperTheory.Kd.C7.pPresDl :
    UpperTheory.Kd.C7.SPresDl := by
  intro l _ hl2 Ω _ _ _ A hA j Φ c β ζ hζ Z m n hm P P' hP hP' i
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hlN : l ^ n ≠ 0 := pow_ne_zero _ hl0
  unfold BPres KumPres at hP hP'
  obtain ⟨-, hnm, hPu, -, hPk⟩ := hP
  obtain ⟨-, -, hP'u, -, hP'k⟩ := hP'
  beta_reduce at hPu hP'u hPk hP'k
  obtain ⟨huA, hu0, huiA⟩ := hPu i
  obtain ⟨hu'A, hu'0, hu'iA⟩ := hP'u i
  have hKum : ∀ s ∈ Hm l A m, KumVal (l := l) n (ζ n) (pv (P i) (ζ m) * (pv (P' i) (ζ m))⁻¹) s 0 := by
    intro s hs
    have hs' := hs
    unfold Hm at hs'
    obtain ⟨hsI, hsc⟩ := Subgroup.mem_inf.mp hs'
    rw [MonoidHom.mem_ker] at hsc
    haveI : ∀ i : ℕ, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => ⟨⟨ζ i, (hζ i).1⟩, inferInstance⟩
    have hfix : s (ζ n) = ζ n := fix_of_cycMod hnm hsc (hζ n).1.pow_eq_one
    obtain ⟨k, hk, hkZ⟩ := hPk s hsI hsc hfix
    obtain ⟨k', hk', hk'Z⟩ := hP'k s hsI hsc hfix
    have hkk : k i = k' i := coord_eq β k k' hkZ hk'Z i
    have hKA := pKumAlg l hl2 Ω A hA ζ hζ m n hnm s hs
    have hinv := (hKA.1 _ _ _ _ (hk' i) (hk' i)).2.1
    have hmul := (hKA.1 _ _ _ _ (hk i) hinv).1
    rw [hkk, add_neg_cancel] at hmul
    exact hmul
  obtain ⟨v, hv, hvfix⟩ := pKumTriv l hl2 Ω A hA ζ hζ m n hnm _ (mul_ne_zero hu0 (inv_ne_zero hu'0)) hKum
  have hvA : v ∈ A := mem_of_pow_mem A hlN (by rw [hv]; exact mul_mem huA hu'iA)
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, zero_pow hlN] at hv
    exact mul_ne_zero hu0 (inv_ne_zero hu'0) hv.symm
  have hviA : v⁻¹ ∈ A := mem_of_pow_mem A hlN (by
    rw [inv_pow, hv, mul_inv, inv_inv]
    exact mul_mem huiA hu'A)
  obtain ⟨Q, hQ⟩ := pPolyEx l hl2 Ω A hA ζ hζ m v hvA hvfix
  have hQu : pv Q (ζ m) ∈ A ∧ pv Q (ζ m) ≠ 0 ∧ (pv Q (ζ m))⁻¹ ∈ A := by
    rw [hQ]
    exact ⟨hvA, hv0, hviA⟩
  have heq : pv (P i) (ζ m) = pv (P' i) (ζ m) * pv Q (ζ m) ^ l ^ n := by
    rw [hQ, hv, mul_comm (pv (P i) (ζ m)), ← mul_assoc, mul_inv_cancel₀ hu'0, one_mul]
  refine ⟨⟨Q, hQu, heq⟩, ?_⟩
  have hWD := pWD l hl2 Ω A hA j Φ ζ hζ m hm
  have hUP := (hWD (P i)).2 ⟨huA, hu0, huiA⟩
  have hUP' := (hWD (P' i)).2 ⟨hu'A, hu'0, hu'iA⟩
  have hUQ := (hWD Q).2 hQu
  have hpv : pv (P i - P' i * Q ^ l ^ n) (ζ m) = pv (P i) (ζ m) - pv (P' i) (ζ m) * pv Q (ζ m) ^ l ^ n := by
    simp only [pv, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow]
  have hz : pv (P i - P' i * Q ^ l ^ n) (ζ m) = 0 := by
    rw [hpv, ← heq, sub_self]
  have h0 := (hWD (P i - P' i * Q ^ l ^ n)).1 hz
  rw [ser_rel] at h0
  have hLC : LC l m (m - 1) (Φ.ser (P i)) (Φ.ser (P' i) * Φ.ser Q ^ l ^ n) := by
    unfold LC
    rw [← map_sub, h0]
    exact Ideal.zero_mem _
  have hD := pDlogCmp Φ.R l m n (m - 1) hm _ _ _ hUP hUP' hUQ hLC
  rwa [min_self] at hD
