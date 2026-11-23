import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntIntCast

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open GlobalTheory GlobalTheory.HeckeApprox UpperTheory.Lev
open scoped TensorProduct
universe u

set_option autoImplicit false

namespace UpperTheory.Gal.G3.GSimGlue

variable {G : GDatum}

private theorem mn_symm {n : ℕ} {a b : G.La} (h : MN n a b) : MN n b a := by
  obtain ⟨c, hc⟩ := h
  exact ⟨-c, by rw [hc, smul_neg]; abel⟩

private theorem mn_trans {n : ℕ} {a b c : G.La} (h : MN n a b) (h' : MN n b c) : MN n a c := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨d, hd⟩ := h'
  exact ⟨d + c, by rw [hc, hd, smul_add]; abel⟩

private theorem mn_osmul {n : ℕ} {a b : G.La} (c : G.O) (h : MN n a b) : MN n (c • a) (c • b) := by
  obtain ⟨z, hz⟩ := h
  exact ⟨c • z, by rw [hz, smul_add, smul_comm]⟩

private theorem mn_of_dvd {n m : ℕ} {a b : G.La} (hd : n ∣ m) (h : MN m a b) : MN n a b := by
  obtain ⟨k, rfl⟩ := hd
  obtain ⟨c, hc⟩ := h
  exact ⟨k • c, by rw [hc, mul_smul]⟩

private theorem mn_map (f : G.La →+ G.La) {n : ℕ} {a b : G.La} (h : MN n a b) : MN n (f a) (f b) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨f c, by rw [hc, map_add, map_nsmul]⟩

private theorem mn_glue {a b : ℕ} {x y : G.La} (hab : a.Coprime b) (h : MN a x y) (h' : MN b x y) :
    MN (a * b) x y := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨d, hd⟩ := h'
  have hx : a • c = b • d := add_left_cancel (hc.symm.trans hd)
  have hx' : (a : ℤ) • c = (b : ℤ) • d := by simpa only [natCast_zsmul] using hx
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hab
  refine ⟨u • d + v • c, ?_⟩
  rw [hc, ← natCast_zsmul, ← natCast_zsmul]
  congr 1
  have e1 : (a : ℤ) • c = (u * a + v * b) • ((a : ℤ) • c) := by rw [huv, one_smul]
  rw [e1, add_smul, mul_smul, mul_smul]
  nth_rewrite 1 [hx']
  push_cast
  simp only [smul_add, smul_smul]
  congr 1 <;> congr 1 <;> ring

private theorem mn_form {n : ℕ} {a b c d : G.La} (h : MN n a b) (h' : MN n c d) :
    (n : ℤ) ∣ G.EF a c - G.EF b d := by
  obtain ⟨x, rfl⟩ := h
  obtain ⟨y, rfl⟩ := h'
  refine ⟨G.EF x d + G.EF b y + n * G.EF x y, ?_⟩
  simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
  ring

private structure Sys (G : GDatum) (p : ℕ) (h : ℕ → G.La →+ G.La) (w : ℕ → ℤ) : Prop where
  lin : ∀ a : ℕ, 0 < a → a.Coprime p → ∀ (c : G.O) x, MN a (h a (c • x)) (c • h a x)
  tower : ∀ a b : ℕ, 0 < a → 0 < b → (a * b).Coprime p → ∀ x, MN a (h (a * b) x) (h a x)
  wtower : ∀ a b : ℕ, 0 < a → 0 < b → (a * b).Coprime p → (a : ℤ) ∣ w (a * b) - w a
  cop : ∀ a : ℕ, 0 < a → a.Coprime p → IsCoprime (w a) (a : ℤ)
  isom : ∀ a : ℕ, 0 < a → a.Coprime p → ∀ x y, (a : ℤ) ∣ G.EF (h a x) (h a y) - w a * G.EF x y
  inj : ∀ a : ℕ, 0 < a → a.Coprime p → ∀ x, MN a (h a x) 0 → MN a x 0
  surj : ∀ a : ℕ, 0 < a → a.Coprime p → ∀ y, ∃ x, MN a (h a x) y

private theorem exists_idem {a q : ℕ} (h : a.Coprime q) : ∃ e : ℤ, (a : ℤ) ∣ e - 1 ∧ (q : ℤ) ∣ e := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr h
  exact ⟨v * q, ⟨-u, by linarith⟩, dvd_mul_left _ _⟩

private theorem mn_comb_a {a : ℕ} {e : ℤ} (he : (a : ℤ) ∣ e - 1) (y x : G.La) :
    MN a (e • y + (1 - e) • x) y := by
  obtain ⟨k, hk⟩ := he
  obtain rfl : e = 1 + a * k := by linarith
  refine ⟨k • (y - x), ?_⟩
  rw [← natCast_zsmul]
  module

private theorem mn_comb_q {q : ℕ} {e : ℤ} (he : (q : ℤ) ∣ e) (y x : G.La) :
    MN q (e • y + (1 - e) • x) x := by
  obtain ⟨k, rfl⟩ := he
  refine ⟨k • (y - x), ?_⟩
  rw [← natCast_zsmul]
  module

private theorem exists_parts {p : ℕ} (hp : p.Prime) : ∃ A Q : ℕ → ℕ,
    (∀ n, 0 < n → A n * Q n = n ∧ 0 < A n ∧ (A n).Coprime p ∧ (A n).Coprime (Q n)) ∧
    (∀ n m, 0 < n → 0 < m → A n ∣ A (n * m) ∧ Q n ∣ Q (n * m)) ∧
    ∀ n, 0 < n → n.Coprime p → A n = n := by
  refine ⟨fun n => n / p ^ n.factorization p, fun n => p ^ n.factorization p, fun n hn => ?_, fun n m hn hm => ?_,
    fun n hn hnp => ?_⟩
  · have c : (n / p ^ n.factorization p).Coprime p := (Nat.coprime_ordCompl hp hn.ne').symm
    exact ⟨by rw [mul_comm]; exact Nat.ordProj_mul_ordCompl_eq_self n p, Nat.ordCompl_pos p hn.ne', c,
      Nat.Coprime.pow_right _ c⟩
  · exact ⟨Nat.ordCompl_dvd_ordCompl_of_dvd (dvd_mul_right n m) p,
      Nat.ordProj_dvd_ordProj_of_dvd (Nat.mul_pos hn hm).ne' (dvd_mul_right n m) p⟩
  · have h0 : n.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd fun h =>
      hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hnp.symm h)
    simp [h0]

private theorem glue {p : ℕ} (hp : p.Prime) {h : ℕ → G.La →+ G.La} {w : ℕ → ℤ} (H : Sys G p h w) :
    ∃ g : GSim G, ∀ n, 0 < n → n.Coprime p → ∀ x, MN n (g.f n x) (h n x) := by
  obtain ⟨A, Q, hAQ, hdv, hAid⟩ := exists_parts hp
  have hE : ∀ n, 0 < n → ∃ e : ℤ, (A n : ℤ) ∣ e - 1 ∧ (Q n : ℤ) ∣ e :=
    fun n hn => exists_idem (hAQ n hn).2.2.2
  choose! E hE1 hE2 using hE
  have gl : ∀ n, 0 < n → ∀ u v : G.La, MN (A n) u v → MN (Q n) u v → MN n u v := by
    intro n hn u v h1 h2
    have := mn_glue (hAQ n hn).2.2.2 h1 h2
    rwa [(hAQ n hn).1] at this
  have gli : ∀ n, 0 < n → ∀ z : ℤ, (A n : ℤ) ∣ z → (Q n : ℤ) ∣ z → (n : ℤ) ∣ z := by
    intro n hn z h1 h2
    have := IsCoprime.mul_dvd (Nat.isCoprime_iff_coprime.mpr (hAQ n hn).2.2.2) h1 h2
    rwa [← Nat.cast_mul, (hAQ n hn).1] at this
  have fa : ∀ n, 0 < n → ∀ x, MN (A n) (E n • h (A n) x + (1 - E n) • x) (h (A n) x) :=
    fun n hn x => mn_comb_a (hE1 n hn) _ _
  have fq : ∀ n, 0 < n → ∀ x, MN (Q n) (E n • h (A n) x + (1 - E n) • x) x :=
    fun n hn x => mn_comb_q (hE2 n hn) _ _
  have νa : ∀ n, 0 < n → (A n : ℤ) ∣ (E n * w (A n) + (1 - E n)) - w (A n) := by
    intro n hn
    have e : (E n * w (A n) + (1 - E n)) - w (A n) = (E n - 1) * (w (A n) - 1) := by ring
    rw [e]
    exact dvd_mul_of_dvd_left (hE1 n hn) _
  have νq : ∀ n, 0 < n → (Q n : ℤ) ∣ (E n * w (A n) + (1 - E n)) - 1 := by
    intro n hn
    have e : (E n * w (A n) + (1 - E n)) - 1 = E n * (w (A n) - 1) := by ring
    rw [e]
    exact dvd_mul_of_dvd_left (hE2 n hn) _
  refine ⟨⟨fun n x => E n • h (A n) x + (1 - E n) • x, fun n => E n * w (A n) + (1 - E n), ?_, ?_, ?_⟩, ?_⟩
  · intro n hn
    obtain ⟨hmul, hApos, hAp, hAQc⟩ := hAQ n hn
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x y
      refine ⟨0, ?_⟩
      simp only [map_add, smul_add, smul_zero, add_zero]
      abel
    · intro c x
      refine gl n hn _ _ ?_ ?_
      · exact mn_trans (fa n hn _) (mn_trans (H.lin _ hApos hAp c x) (mn_symm (mn_osmul c (fa n hn x))))
      · exact mn_trans (fq n hn _) (mn_symm (mn_osmul c (fq n hn x)))
    · intro x hx
      refine gl n hn _ _ ?_ ?_
      · have h1 : MN (A n) (E n • h (A n) x + (1 - E n) • x) 0 := mn_of_dvd ⟨Q n, hmul.symm⟩ hx
        exact H.inj _ hApos hAp x (mn_trans (mn_symm (fa n hn x)) h1)
      · have h1 : MN (Q n) (E n • h (A n) x + (1 - E n) • x) 0 :=
          mn_of_dvd ⟨A n, by rw [mul_comm]; exact hmul.symm⟩ hx
        exact mn_trans (mn_symm (fq n hn x)) h1
    · intro y
      obtain ⟨x0, hx0⟩ := H.surj _ hApos hAp y
      refine ⟨E n • x0 + (1 - E n) • y, gl n hn _ _ ?_ ?_⟩
      · exact mn_trans (fa n hn _) (mn_trans (mn_map (h (A n)) (mn_comb_a (hE1 n hn) x0 y)) hx0)
      · exact mn_trans (fq n hn _) (mn_comb_q (hE2 n hn) x0 y)
    · have hc : ((n : ℕ) : ℤ) = (A n : ℤ) * (Q n : ℤ) := by rw [← Nat.cast_mul, hmul]
      rw [hc]
      refine IsCoprime.mul_right ?_ ?_
      · obtain ⟨k, hk⟩ := νa n hn
        have e : E n * w (A n) + (1 - E n) = w (A n) + (A n : ℤ) * k := by linarith
        rw [e]
        exact (H.cop _ hApos hAp).add_mul_left_left k
      · obtain ⟨k, hk⟩ := νq n hn
        have e : E n * w (A n) + (1 - E n) = 1 + (Q n : ℤ) * k := by linarith
        rw [e]
        exact isCoprime_one_left.add_mul_left_left k
    · intro x y
      beta_reduce
      refine gli n hn _ ?_ ?_
      · have d1 := mn_form (fa n hn x) (fa n hn y)
        have d2 := H.isom _ hApos hAp x y
        have d3 := νa n hn
        have e : 2 * G.EF (E n • h (A n) x + (1 - E n) • x) (E n • h (A n) y + (1 - E n) • y)
            - (E n * w (A n) + (1 - E n)) * (2 * G.EF x y)
            = 2 * (G.EF (E n • h (A n) x + (1 - E n) • x) (E n • h (A n) y + (1 - E n) • y)
                - G.EF (h (A n) x) (h (A n) y))
              + 2 * (G.EF (h (A n) x) (h (A n) y) - w (A n) * G.EF x y)
              - ((E n * w (A n) + (1 - E n)) - w (A n)) * (2 * G.EF x y) := by ring
        rw [e]
        exact dvd_sub (dvd_add (dvd_mul_of_dvd_right d1 _) (dvd_mul_of_dvd_right d2 _))
          (dvd_mul_of_dvd_left d3 _)
      · have d1 := mn_form (fq n hn x) (fq n hn y)
        have d3 := νq n hn
        have e : 2 * G.EF (E n • h (A n) x + (1 - E n) • x) (E n • h (A n) y + (1 - E n) • y)
            - (E n * w (A n) + (1 - E n)) * (2 * G.EF x y)
            = 2 * (G.EF (E n • h (A n) x + (1 - E n) • x) (E n • h (A n) y + (1 - E n) • y) - G.EF x y)
              - ((E n * w (A n) + (1 - E n)) - 1) * (2 * G.EF x y) := by ring
        rw [e]
        exact dvd_sub (dvd_mul_of_dvd_right d1 _) (dvd_mul_of_dvd_left d3 _)
  · intro n m hn hm x
    have hN : 0 < n * m := Nat.mul_pos hn hm
    obtain ⟨hdA, hdQ⟩ := hdv n m hn hm
    refine gl n hn _ _ ?_ ?_
    · obtain ⟨b, hb⟩ := hdA
      have hApos := (hAQ n hn).2.1
      have hANpos := (hAQ _ hN).2.1
      have hbpos : 0 < b := by
        rcases Nat.eq_zero_or_pos b with h0 | h0
        · rw [h0, mul_zero] at hb
          omega
        · exact h0
      have hcop : (A n * b).Coprime p := by
        rw [← hb]
        exact (hAQ _ hN).2.2.1
      have ht := H.tower (A n) b hApos hbpos hcop x
      rw [← hb] at ht
      exact mn_trans (mn_of_dvd ⟨b, hb⟩ (fa _ hN x)) (mn_trans ht (mn_symm (fa n hn x)))
    · exact mn_trans (mn_of_dvd hdQ (fq _ hN x)) (mn_symm (fq n hn x))
  · intro n m hn hm
    beta_reduce
    have hN : 0 < n * m := Nat.mul_pos hn hm
    obtain ⟨hdA, hdQ⟩ := hdv n m hn hm
    refine gli n hn _ ?_ ?_
    · obtain ⟨b, hb⟩ := hdA
      have hApos := (hAQ n hn).2.1
      have hbpos : 0 < b := by
        rcases Nat.eq_zero_or_pos b with h0 | h0
        · have := (hAQ _ hN).2.1
          rw [hb, h0, mul_zero] at this
          omega
        · exact h0
      have hcop : (A n * b).Coprime p := by
        rw [← hb]
        exact (hAQ _ hN).2.2.1
      have ht := H.wtower (A n) b hApos hbpos hcop
      rw [← hb] at ht
      have d1 : (A n : ℤ) ∣ (E (n * m) * w (A (n * m)) + (1 - E (n * m))) - w (A (n * m)) :=
        dvd_trans (Int.natCast_dvd_natCast.mpr ⟨b, hb⟩) (νa _ hN)
      have e : (E (n * m) * w (A (n * m)) + (1 - E (n * m))) - (E n * w (A n) + (1 - E n))
          = ((E (n * m) * w (A (n * m)) + (1 - E (n * m))) - w (A (n * m)))
            + (w (A (n * m)) - w (A n)) - ((E n * w (A n) + (1 - E n)) - w (A n)) := by ring
      rw [e]
      exact dvd_sub (dvd_add d1 ht) (νa n hn)
    · have d1 : (Q n : ℤ) ∣ (E (n * m) * w (A (n * m)) + (1 - E (n * m))) - 1 :=
        dvd_trans (Int.natCast_dvd_natCast.mpr hdQ) (νq _ hN)
      have e : (E (n * m) * w (A (n * m)) + (1 - E (n * m))) - (E n * w (A n) + (1 - E n))
          = ((E (n * m) * w (A (n * m)) + (1 - E (n * m))) - 1) - ((E n * w (A n) + (1 - E n)) - 1) := by ring
      rw [e]
      exact dvd_sub d1 (νq n hn)
  · intro n hn hc x
    show MN n (E n • h (A n) x + (1 - E n) • x) (h n x)
    have := fa n hn x
    rw [hAid n hn hc] at this ⊢
    exact this

end UpperTheory.Gal.G3.GSimGlue

private theorem UpperTheory.Gal.G3.GSimGlue.sys_of {p : ℕ} [Fact p.Prime] (hMB : MultBasic) (D : Datum p) (G : HTGroup p)
    (L : Link D G) (u : G.GAf) (hu : u ∈ L.KN 1) :
    ∃ (h : ℕ → D.La →+ D.La) (w : ℕ → ℤ),
      (∀ a : ℕ, 0 < a → a.Coprime p → ∀ (c : D.O) (x : D.La), ∃ z, h a (c • x) = c • h a x + a • z) ∧
      (∀ a b : ℕ, 0 < a → 0 < b → (a * b).Coprime p → ∀ x, ∃ z, h (a * b) x = h a x + a • z) ∧
      (∀ a b : ℕ, 0 < a → 0 < b → (a * b).Coprime p → (a : ℤ) ∣ w (a * b) - w a) ∧
      (∀ a : ℕ, 0 < a → a.Coprime p → IsCoprime (w a) (a : ℤ)) ∧
      (∀ a : ℕ, 0 < a → a.Coprime p → ∀ x y, (a : ℤ) ∣ D.EF (h a x) (h a y) - w a * D.EF x y) ∧
      (∀ a : ℕ, 0 < a → a.Coprime p → ∀ x, (∃ c, h a x = 0 + a • c) → ∃ c, x = 0 + a • c) ∧
      (∀ a : ℕ, 0 < a → a.Coprime p → ∀ y, ∃ x z, h a x = y + a • z) ∧
      ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ v ∈ LaHat D, L.actG u (inAf D x) = inAf D (h n x) + n • v := by
  have hmem : ∀ v ∈ LaHat D, L.actG u v ∈ LaHat D := fun v hv => actG_mem_laHat L hu hv
  have huinv : u⁻¹ ∈ L.KN 1 := inv_mem hu
  have hmem' : ∀ v ∈ LaHat D, L.actG u⁻¹ v ∈ LaHat D := fun v hv => actG_mem_laHat L huinv hv
  have hinv : ∀ v, L.actG u⁻¹ (L.actG u v) = v := by
    intro v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hinv' : ∀ v, L.actG u (L.actG u⁻¹ v) = v := by
    intro v
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨h, hh⟩ := T.lattice_endomorphism_integral_approximation p D (L.actG u) hmem
  obtain ⟨t, t', ht, ht', htt, hmu⟩ := (hMB p).2.2 D G L u hu
  simp only [Nat.cast_one, _root_.one_mul] at hmu
  obtain ⟨w, hwt, hwc⟩ := T.integral_adele_unit_congruence_sequence p (mul u) t' (hmu ▸ ht) ht' (by rw [hmu]; exact htt)
  have div : ∀ a : ℕ, 0 < a → a.Coprime p → ∀ (x : D.La), ∀ v ∈ LaHat D, inAf D x = a • v → ∃ z, x = a • z :=
    fun a ha hc x v hv e => LatDiv.eq_nsmul_of_inAf_eq_nsmul p D x a ha hc v hv e
  refine ⟨h, w, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hh⟩
  · intro a ha hc c x
    obtain ⟨v, hv, e1⟩ := hh a ha hc (c • x)
    obtain ⟨v', hv', e2⟩ := hh a ha hc x
    have e3 : L.actG u (inAf D (c • x)) = inAf D (c • h a x) + a • actAf D c v' := by
      rw [← actAf_inAf, actG_actAf, e2, map_add, map_nsmul, actAf_inAf]
    rw [e1] at e3
    obtain ⟨z, hz⟩ := div a ha hc (h a (c • x) - c • h a x) (actAf D c v' - v)
      (sub_mem (actAf_mem_laHat D c hv') hv) (by
        rw [inAf_sub, nsmul_sub, sub_eq_sub_iff_add_eq_add, e3, add_comm])
    exact ⟨z, sub_eq_iff_eq_add'.mp hz⟩
  · intro a b ha hb hc x
    have hca : a.Coprime p := (Nat.coprime_mul_iff_left.mp hc).1
    obtain ⟨v, hv, e1⟩ := hh (a * b) (Nat.mul_pos ha hb) hc x
    obtain ⟨v', hv', e2⟩ := hh a ha hca x
    obtain ⟨z, hz⟩ := div a ha hca (h (a * b) x - h a x) (v' - b • v)
      (sub_mem hv' (AddSubgroup.nsmul_mem _ hv b)) (by
        rw [inAf_sub, nsmul_sub, smul_smul, sub_eq_sub_iff_add_eq_add, ← e1, e2, add_comm])
    exact ⟨z, sub_eq_iff_eq_add'.mp hz⟩
  · exact fun a b ha hb hc => hwt a b ha hb hc
  · exact fun a ha hc => (hwc a ha hc).1
  · intro a ha hc x y
    obtain ⟨v, hv, e1⟩ := hh a ha hc x
    obtain ⟨v', hv', e2⟩ := hh a ha hc y
    obtain ⟨β, hβ, hmuw⟩ := (hwc a ha hc).2
    have hf := T.harrisTaylor_action_form_eq_similitude_mul p D G L u (inAf D x) (inAf D y)
    change fAf D (L.actG u (inAf D x)) (L.actG u (inAf D y)) = mul u * fAf D (inAf D x) (inAf D y) at hf
    rw [e1, e2, form_inAf, hmuw] at hf
    simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, form_inAf, nsmul_eq_mul] at hf
    refine IntDvdAdele.dvd_of_eq_mul_int p a ha hc _
      (β * ((D.EF x y : ℤ) : AfP p) - (fAf D (inAf D (h a x)) v' + fAf D v (inAf D (h a y)) + (a : AfP p) * fAf D v v'))
      ?_ ?_
    · exact isInt_sub (isInt_mul hβ (isInt_intCast _))
        (isInt_add (isInt_add (formInt_laHat p D _ _ (inAf_mem D _) hv') (formInt_laHat p D _ _ hv (inAf_mem D _)))
          (isInt_mul (isInt_natCast a) (formInt_laHat p D _ _ hv hv')))
    · push_cast
      linear_combination hf
  · rintro a ha hc x ⟨c, hxc⟩
    obtain ⟨v, hv, e1⟩ := hh a ha hc x
    rw [hxc, zero_add, inAf_nsmul, ← nsmul_add] at e1
    have e2 := congrArg (L.actG u⁻¹) e1
    rw [hinv, map_nsmul] at e2
    obtain ⟨z, hz⟩ := div a ha hc x _ (hmem' _ (add_mem (inAf_mem D c) hv)) e2
    exact ⟨z, by rw [zero_add]; exact hz⟩
  · intro a ha hc y
    obtain ⟨x, w', hw', e1⟩ := exists_inAf_add_nsmul_of_mem_laHat p D a ha hc _ (hmem' _ (inAf_mem D y))
    obtain ⟨v, hv, e2⟩ := hh a ha hc x
    have e3 : L.actG u (inAf D x) = inAf D y - a • L.actG u w' := by
      rw [eq_sub_iff_add_eq, ← map_nsmul, ← map_add, ← e1, hinv']
    rw [e2] at e3
    obtain ⟨z, hz⟩ := div a ha hc (h a x - y) (-(L.actG u w') - v)
      (sub_mem (neg_mem (hmem _ hw')) hv) (by
        rw [inAf_sub, nsmul_sub, smul_neg, sub_eq_sub_iff_add_eq_add, e3, sub_eq_neg_add])
    exact ⟨x, z, sub_eq_iff_eq_add'.mp hz⟩

theorem UpperTheory.Gal.G3.pGSimOf :
    MultBasic → GSimOf := by
  intro hMB p _ D G L u hu
  obtain ⟨h, w, hlin, htow, hwt, hcop, hisom, hinj, hsurj, hK⟩ := GSimGlue.sys_of hMB D G L u hu
  have hp : p.Prime := Fact.out
  have S : GSimGlue.Sys D.toG p h w :=
    { lin := hlin, tower := htow, wtower := hwt, cop := hcop, isom := hisom, inj := hinj,
      surj := fun a ha hc y => by
        obtain ⟨x, z, hz⟩ := hsurj a ha hc y
        exact ⟨x, z, hz⟩ }
  obtain ⟨g, hg⟩ := GSimGlue.glue hp S
  refine ⟨g, fun n hn hc x => ?_⟩
  obtain ⟨v, hv, e⟩ := hK n hn hc x
  obtain ⟨c, hc'⟩ := hg n hn hc x
  refine ⟨v - inAf D c, sub_mem hv (inAf_mem D c), ?_⟩
  have e2 : inAf D (g.f n x) = inAf D (h n x) + n • inAf D c := by
    rw [hc']
    exact (inAf_add D _ _).trans (congrArg _ (inAf_nsmul D n c))
  rw [e, e2, nsmul_sub]
  abel
