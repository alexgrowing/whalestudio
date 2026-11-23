import Mathlib
import Formalism.PeriodIntegrals.ClassNumImQ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticDedekindZeta.Development

open NumberField

namespace PI.ClassNumImQ.ZetaNonvanishing₂

theorem sup_mul_sup_eq {R : Type*} [CommRing R] (A M N : Ideal R) (hMN : M ⊔ N = ⊤)
    (h : M * N ≤ A) : (A ⊔ M) * (A ⊔ N) = A := by
  apply le_antisymm
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    have r1 : ∀ X : Ideal R, A * X ≤ A := fun X => Ideal.mul_le.mpr fun x hx y _ => Ideal.mul_mem_right y _ hx
    have r2 : ∀ X : Ideal R, X * A ≤ A := fun X => Ideal.mul_le.mpr fun x _ y hy => Ideal.mul_mem_left _ x hy
    exact sup_le (sup_le (r1 _) (r1 _)) (sup_le (r2 _) h)
  · calc A = A * (M ⊔ N) := by rw [hMN, Ideal.mul_top]
      _ = A * M ⊔ A * N := Ideal.mul_sup _ _ _
      _ ≤ (A ⊔ M) * (A ⊔ N) := by
        refine sup_le ?_ (Ideal.mul_mono le_sup_left le_sup_right)
        rw [mul_comm]
        exact Ideal.mul_mono le_sup_right le_sup_left

theorem span_natCast_sup_eq_top {S : Type*} [CommRing S] {m n : ℕ} (h : m.Coprime n) :
    Ideal.span {(m : S)} ⊔ Ideal.span {(n : S)} = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h1 : ((m : ℤ) * Nat.gcdA m n + (n : ℤ) * Nat.gcdB m n : ℤ) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one h]
    simp
  have h2 : ((m : S) * (Nat.gcdA m n : S) + (n : S) * (Nat.gcdB m n : S)) = 1 := by
    have := congrArg (Int.cast : ℤ → S) h1
    push_cast at this
    exact this
  rw [← h2]
  exact Ideal.add_mem _
    (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
    (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

variable {K : Type} [Field K] [NumberField K]

theorem span_le_of_absNorm {I : Ideal (𝓞 K)} {m : ℕ} (hI : Ideal.absNorm I = m) :
    Ideal.span {(m : 𝓞 K)} ≤ I := by
  rw [← hI]
  exact Ideal.span_singleton_absNorm_le I

theorem cnt_one : cnt K 1 = 1 := by
  unfold cnt
  rw [Nat.card_eq_one_iff_exists]
  exact ⟨⟨⊤, Ideal.absNorm_top⟩, fun y => Subtype.ext (Ideal.absNorm_eq_one_iff.mp y.2)⟩

theorem le_of_mul_eq {m n : ℕ} (hmn : m.Coprime n) {I J I' J' : Ideal (𝓞 K)}
    (hI : Ideal.absNorm I = m) (hJ' : Ideal.absNorm J' = n) (h : I * J = I' * J') : I' ≤ I := by
  have hcop : IsCoprime I J' := by
    rw [Ideal.isCoprime_iff_sup_eq, eq_top_iff, ← span_natCast_sup_eq_top hmn]
    exact sup_le_sup (span_le_of_absNorm hI) (span_le_of_absNorm hJ')
  have hd : I ∣ I' * J' := ⟨J, h.symm⟩
  exact Ideal.le_of_dvd (hcop.dvd_of_dvd_mul_right hd)

theorem sup_parts {m n : ℕ} (hmn : m.Coprime n) (hm : 0 < m) (hn : 0 < n) {A : Ideal (𝓞 K)}
    (hA : Ideal.absNorm A = m * n) :
    (A ⊔ Ideal.span {(m : 𝓞 K)}) * (A ⊔ Ideal.span {(n : 𝓞 K)}) = A ∧
      Ideal.absNorm (A ⊔ Ideal.span {(m : 𝓞 K)}) = m ∧
      Ideal.absNorm (A ⊔ Ideal.span {(n : 𝓞 K)}) = n := by
  have hprod : (A ⊔ Ideal.span {(m : 𝓞 K)}) * (A ⊔ Ideal.span {(n : 𝓞 K)}) = A := by
    refine sup_mul_sup_eq A _ _ (span_natCast_sup_eq_top hmn) ?_
    rw [Ideal.span_singleton_mul_span_singleton, ← Nat.cast_mul]
    exact span_le_of_absNorm hA
  have hN := congrArg Ideal.absNorm hprod
  rw [map_mul, hA] at hN
  set a := Ideal.absNorm (A ⊔ Ideal.span {(m : 𝓞 K)})
  set c := Ideal.absNorm (A ⊔ Ideal.span {(n : 𝓞 K)})
  have ha : a ∣ m ^ Module.finrank ℤ (𝓞 K) := by
    rw [← Ideal.absNorm_span_natCast]
    exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
  have hc : c ∣ n ^ Module.finrank ℤ (𝓞 K) := by
    rw [← Ideal.absNorm_span_natCast]
    exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
  have ha' : a ∣ m := by
    have hcop : a.Coprime n := Nat.Coprime.coprime_dvd_left ha (Nat.Coprime.pow_left _ hmn)
    exact hcop.dvd_of_dvd_mul_right ⟨c, hN.symm⟩
  have hc' : c ∣ n := by
    have hcop : c.Coprime m := Nat.Coprime.coprime_dvd_left hc (Nat.Coprime.pow_left _ hmn.symm)
    exact hcop.dvd_of_dvd_mul_left ⟨a, by rw [← hN]; ring⟩
  have ha1 : a ≤ m := Nat.le_of_dvd hm ha'
  have hc1 : c ≤ n := Nat.le_of_dvd hn hc'
  have hae : a = m := by
    by_contra hne
    have hlt : a < m := lt_of_le_of_ne ha1 hne
    have : a * c < m * n := by
      calc a * c ≤ a * n := Nat.mul_le_mul_left _ hc1
        _ < m * n := Nat.mul_lt_mul_of_pos_right hlt hn
    omega
  have hce : c = n := by
    rw [hae] at hN
    exact Nat.eq_of_mul_eq_mul_left hm hN
  exact ⟨hprod, hae, hce⟩

theorem cntMul : CntMul := by
  intro K _ _ m n hmn
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.coprime_zero_left] at hmn
    subst hmn
    simp [cnt_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.coprime_zero_right] at hmn
    subst hmn
    simp [cnt_one]
  let Φ : {I : Ideal (𝓞 K) // Ideal.absNorm I = m} × {J : Ideal (𝓞 K) // Ideal.absNorm J = n} →
      {A : Ideal (𝓞 K) // Ideal.absNorm A = m * n} :=
    fun x => ⟨x.1.1 * x.2.1, by rw [map_mul, x.1.2, x.2.2]⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨⟨I, hI⟩, ⟨J, hJ⟩⟩ ⟨⟨I', hI'⟩, ⟨J', hJ'⟩⟩ h
      have h' : I * J = I' * J' := congrArg Subtype.val h
      have hII : I = I' :=
        le_antisymm (le_of_mul_eq hmn hI' hJ h'.symm) (le_of_mul_eq hmn hI hJ' h')
      subst hII
      have hI0 : I ≠ 0 := by
        rw [Ideal.zero_eq_bot, ne_eq, ← Ideal.absNorm_eq_zero_iff, hI]
        omega
      have hJJ : J = J' := mul_left_cancel₀ hI0 h'
      subst hJJ
      rfl
    · rintro ⟨A, hA⟩
      obtain ⟨hprod, hI, hJ⟩ := sup_parts hmn hm hn hA
      exact ⟨⟨⟨_, hI⟩, ⟨_, hJ⟩⟩, Subtype.ext hprod⟩
  unfold cnt
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective Φ hΦ)).symm

end PI.ClassNumImQ.ZetaNonvanishing₂
