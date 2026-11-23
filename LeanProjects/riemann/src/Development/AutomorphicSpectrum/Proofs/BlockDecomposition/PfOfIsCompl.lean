import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRingHomPowPrimePow

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem pf_of_isCompl : ∀ (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B] (T : Type) [CommRing T]
    (π : B) (g : B →+* T), IsCompl π g → Pf p B → Pf p T := by
  intro p _ B _ T _ π g hC hB
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hT : (p : T) = 0 := by rw [← map_natCast g p, hB.char, map_zero]
  obtain ⟨FB, hFB⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p B hB.char 1
  obtain ⟨FT, hFT⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p T hT 1
  have subB : ∀ x y : B, (x - y) ^ p = x ^ p - y ^ p := fun x y => by
    have h := map_sub FB x y
    simpa only [hFB, pow_one] using h
  have subT : ∀ x y : T, (x - y) ^ p = x ^ p - y ^ p := fun x y => by
    have h := map_sub FT x y
    simpa only [hFT, pow_one] using h
  have surj' : ∀ (M : ℕ) (y : T), ∃ x, g π ^ M ∣ y - g x := fun M y => by
    obtain ⟨x, hx⟩ := hC.surj M y
    exact ⟨x, Ideal.mem_span_singleton.1 hx⟩
  have inj' : ∀ (M : ℕ) (x : B), g π ^ M ∣ g x → π ^ M ∣ x := fun M x h =>
    Ideal.mem_span_singleton.1 (hC.inj M x (Ideal.mem_span_singleton.2 h))
  have root : ∀ (M : ℕ) (b : B), π ^ (p * M) ∣ b ^ p → π ^ M ∣ b := by
    rintro M b ⟨c, hc⟩
    obtain ⟨d, hd⟩ := hB.bij.2 c
    have hd' : d ^ p = c := hd
    refine ⟨d, hB.bij.1 (show b ^ p = (π ^ M * d) ^ p from ?_)⟩
    rw [hc, mul_pow, ← pow_mul, mul_comm M p, hd']
  have haus : ∀ x : T, (∀ n : ℕ, g π ^ n ∣ x) → x = 0 := by
    intro x hx
    refine hC.compl.toIsHausdorff.haus x fun n => ?_
    rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    exact hx n
  have dvdp : ∀ (n : ℕ) (x : T), g π ^ n ∣ x → g π ^ n ∣ x ^ p := fun n x h =>
    h.trans (dvd_pow_self x hp0.ne')
  refine ⟨hT, ?_, ?_⟩
  · intro z w hzw
    have hzw' : z ^ p = w ^ p := hzw
    rw [← sub_eq_zero]
    have h0 : (z - w) ^ p = 0 := by rw [subT, hzw', sub_self]
    apply haus
    intro M
    obtain ⟨b, hb⟩ := surj' (p * M) (z - w)
    have h1 : g π ^ (p * M) ∣ g (b ^ p) := by
      have h2 : (z - w - g b) ^ p = (z - w) ^ p - g b ^ p := subT _ _
      rw [h0, zero_sub] at h2
      have h3 : g π ^ (p * M) ∣ (z - w - g b) ^ p := dvdp _ _ hb
      rw [h2, dvd_neg] at h3
      rwa [map_pow]
    have h4 : π ^ M ∣ b := root M b (inj' _ _ h1)
    have h5 : g π ^ M ∣ g b := by
      rw [← map_pow]
      exact map_dvd g h4
    have h6 : g π ^ M ∣ z - w - g b := (pow_dvd_pow _ (Nat.le_mul_of_pos_left M hp0)).trans hb
    have h7 := dvd_add h6 h5
    rwa [sub_add_cancel] at h7
  · intro y
    choose b hb using fun M : ℕ => surj' (p * M) y
    choose e he using fun M : ℕ => hB.bij.2 (b M)
    have he' : ∀ M, e M ^ p = b M := he
    have cauchy : ∀ m n : ℕ, m ≤ n → π ^ m ∣ e m - e n := by
      intro m n hmn
      apply root
      rw [subB, he', he']
      apply inj'
      have h1 : g π ^ (p * m) ∣ y - g (b n) :=
        (pow_dvd_pow _ (Nat.mul_le_mul le_rfl hmn)).trans (hb n)
      have h2 := dvd_sub h1 (hb m)
      rw [map_sub]
      convert h2 using 1
      ring
    obtain ⟨L, hL⟩ := hC.compl.toIsPrecomplete.prec (f := fun n => g (e n)) (fun {m n} hmn => by
      beta_reduce
      rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton, ← map_sub, ← map_pow]
      exact map_dvd g (cauchy m n hmn))
    refine ⟨L, ?_⟩
    show L ^ p = y
    rw [← sub_eq_zero]
    apply haus
    intro n
    have hn : g π ^ n ∣ g (e n) - L := by
      have h3 := hL n
      rwa [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton] at h3
    have h1 : g π ^ n ∣ (g (e n) - L) ^ p := dvdp _ _ hn
    rw [subT, ← map_pow g (e n) p, he'] at h1
    have h2 : g π ^ n ∣ y - g (b n) :=
      (pow_dvd_pow _ (Nat.le_mul_of_pos_left n hp0)).trans (hb n)
    have h4 := dvd_add h1 h2
    rw [← dvd_neg]
    convert h4 using 1
    ring

end GlobalTheory.CompanionTheory.PerfectRing
