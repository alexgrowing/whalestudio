import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSympLevel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FullLevel

open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq]
  exact IsCMField.complexConj_apply_apply E _

theorem exists_twist (l : Level H) (L : ℤ) (hL : (l.A : ℤ) ∣ L - 1) :
    ∃ u w c : 𝓞 E, c ∈ l.Mb ∧ u = 1 + (l.A : 𝓞 E) * c ∧
      H.bar u * u = (L : 𝓞 E) + (l.M' : 𝓞 E) * w := by
  obtain ⟨q, hq⟩ := hL
  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [l.coprime]; trivial
  obtain ⟨n, hn, m, hm, hnm⟩ := Submodule.mem_sup.1 h1
  have hbn : H.bar n ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mem_map_of_mem _ hn
  have hbm : H.bar m ∈ l.Mb := by
    obtain ⟨m0, hm0, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ H.bar.surjective).1 hm
    simpa [bar_bar] using hm0
  have hbar1 : H.bar n + H.bar m = 1 := by rw [← map_add, hnm, map_one]
  have hxN : H.bar n - m ∈ l.Mb := by
    have e : H.bar n - m = n - H.bar m := by linear_combination hbar1 - hnm
    rw [e]; exact sub_mem hn hbm
  have hxN' : H.bar n - m ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := sub_mem hbn hm
  have hx : H.bar n - m ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    have e : H.bar n - m = n * (H.bar n - m) + (H.bar n - m) * m := by
      linear_combination -(H.bar n - m) * hnm
    rw [e]
    exact add_mem (Ideal.mul_mem_mul hn hxN') (Ideal.mul_mem_mul hxN hm)
  have hnn : n * H.bar n ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mul_mem_mul hn hbn
  rw [l.prod] at hx hnn
  obtain ⟨y1, hy1⟩ := Ideal.mem_span_singleton'.1 hx
  obtain ⟨y2, hy2⟩ := Ideal.mem_span_singleton'.1 hnn
  have hg : ((l.M : ℕ) : 𝓞 E) * l.A = (l.M' : 𝓞 E) * (Nat.gcd l.M l.A : ℕ) := by
    have := Nat.gcd_mul_lcm l.M l.A
    unfold Level.M'
    exact_mod_cast (by rw [mul_comm (Nat.lcm _ _), this] : l.M * l.A = Nat.lcm l.M l.A * Nat.gcd l.M l.A)
  have hq' : (L : 𝓞 E) - 1 = (l.A : 𝓞 E) * q := by exact_mod_cast hq
  refine ⟨1 + ((L : 𝓞 E) - 1) * n, (Nat.gcd l.M l.A : 𝓞 E) * q * (y1 + ((L : 𝓞 E) - 1) * y2),
    (q : 𝓞 E) * n, Ideal.mul_mem_left _ _ hn, ?_, ?_⟩
  · rw [hq']; ring
  · have hb : H.bar (1 + ((L : 𝓞 E) - 1) * n) = 1 + ((L : 𝓞 E) - 1) * H.bar n := by
      simp [map_add, map_mul, map_sub, map_one, map_intCast]
    rw [hb]
    linear_combination ((L : 𝓞 E) - 1) * hnm - ((L : 𝓞 E) - 1) * hy1 - ((L : 𝓞 E) - 1) ^ 2 * hy2
      + (l.M : 𝓞 E) * (y1 + ((L : 𝓞 E) - 1) * y2) * hq' + (q : 𝓞 E) * (y1 + ((L : 𝓞 E) - 1) * y2) * hg

theorem smul_mem_M (l : Level H) {D : Datum H} {c : 𝓞 E} (hc : c ∈ l.Mb) {a : D.La}
    (ha : a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)) :
    ∃ y : D.La, c • a = l.M • y := by
  refine Submodule.smul_induction_on ha ?_ ?_
  · intro r hr t _
    have : c * r ∈ Ideal.span {((l.M : ℕ) : 𝓞 E)} := l.prod ▸ Ideal.mul_mem_mul hc hr
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨s • t, by rw [← mul_smul, ← hs, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]⟩
  · rintro x y ⟨x', hx'⟩ ⟨y', hy'⟩
    exact ⟨x' + y', by rw [smul_add, hx', hy', smul_add]⟩

theorem exists_sympLevel_of_tate : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} (l : Level H) {k : Type} [Field k]
    {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e)
    {z : kˣ}, IsPrimitiveRoot z l.M' → z ^ (l.M' / l.A) = I.ζ l.A →
    ∃ ev : D.La → Q, IsSympLevel D act e l.M' z ev ∧ Induces l (I.ev l.A) (I.ev l.M) ev := by
  intro E _ _ _ H D l k _ Q _ act e I z hz hzA
  have hM' := M'_pos l
  haveI : NeZero l.M' := ⟨hM'.ne'⟩
  have hζ := I.ζ_prim l.M' hM'
  obtain ⟨L, -, hcop, hL⟩ := (hζ.isPrimitiveRoot_iff').1 hz
  obtain ⟨d, hd⟩ := A_dvd_M' l
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hd; omega)
  have hdiv : l.M' / l.A = d := by rw [hd, Nat.mul_div_cancel_left _ l.A_pos]
  have hζA : I.ζ l.M' ^ d = I.ζ l.A := by
    have := I.ζ_pow l.A d l.A_pos hd0; rwa [← hd] at this
  have hAL : (l.A : ℤ) ∣ (L : ℤ) - 1 := by
    have e1 : I.ζ l.M' ^ (L * d) = I.ζ l.M' ^ d := by
      rw [pow_mul, hL, ← hdiv, hzA, hdiv, hζA]
    have h2 : I.ζ l.M' ^ (((L : ℤ) - 1) * d) = 1 := by
      rw [sub_mul, one_mul, zpow_sub, show ((L : ℤ) * d) = ((L * d : ℕ) : ℤ) by push_cast; ring,
        zpow_natCast, zpow_natCast, e1, mul_inv_cancel]
    have h3 := (hζ.zpow_eq_one_iff_dvd _).1 h2
    rw [hd] at h3; push_cast at h3
    exact (mul_dvd_mul_iff_right (by exact_mod_cast hd0.ne')).1 h3
  obtain ⟨a', b', hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  obtain ⟨u, w, c, hc, hu, hw⟩ := exists_twist l L hAL
  set v : 𝓞 E := (a' : 𝓞 E) * H.bar u with hv
  have hvu : v * u = 1 + (l.M' : 𝓞 E) * ((a' : 𝓞 E) * w - b') := by
    have hab' : (a' : 𝓞 E) * (L : ℤ) + (b' : 𝓞 E) * ((l.M' : ℕ) : ℤ) = 1 := by exact_mod_cast hab
    push_cast at hab'
    rw [hv, mul_assoc, hw]
    push_cast
    linear_combination hab'
  have key : ∀ a : D.La, v • u • a = a + l.M' • (((a' : 𝓞 E) * w - b') • a) := by
    intro a; rw [← mul_smul, hvu, add_smul, one_smul, mul_smul, Nat.cast_smul_eq_nsmul]
  have key' : ∀ a : D.La, u • v • a = a + l.M' • (((a' : 𝓞 E) * w - b') • a) := by
    intro a; rw [smul_comm]; exact key a
  have hcong : ∀ a b : D.La, I.ev l.M' (a + l.M' • b) = I.ev l.M' a := by
    intro a b; rw [I.add, (I.ker _ hM' _).2 ⟨b, rfl⟩, mul_one]
  have hEF : ∀ a b : D.La, D.EF (u • a) (u • b) = L * D.EF a b + l.M' * D.EF a (w • b) := by
    intro a b
    rw [D.adj, ← mul_smul, hw, add_smul, mul_smul, Nat.cast_smul_eq_nsmul]
    simp only [Int.cast_natCast, Nat.cast_smul_eq_nsmul, map_add, map_zsmul, map_nsmul, smul_eq_mul, nsmul_eq_mul]
  refine ⟨fun a => I.ev l.M' (u • a), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro a b; simp only [smul_add, I.add]
  · intro c a; try simp only
    rw [smul_comm, I.lin]
  · intro a; try simp only
    rw [I.ker _ hM']
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨v • b - ((a' : 𝓞 E) * w - b') • a, ?_⟩
      have h := congrArg (v • ·) hb
      change v • u • a = v • (l.M' • b) at h
      rw [key, smul_comm v l.M' b] at h
      rw [smul_sub, ← h]; abel
    · rintro ⟨b, rfl⟩; exact ⟨u • b, smul_comm _ _ _⟩
  · intro x; rw [I.onto _ hM']
    constructor
    · rintro ⟨a0, rfl⟩; exact ⟨v • a0, by simp only [key', hcong]⟩
    · rintro ⟨a, rfl⟩; exact ⟨u • a, rfl⟩
  · intro a b
    have h := I.isom _ hM' (u • a) (u • b)
    convert h using 1
    rw [hEF, zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hL, hζ.pow_eq_one, one_zpow, mul_one]
  · intro a
    have htow : I.ev l.M' (u • a) ^ d = I.ev l.A (u • a) := by
      have := I.tower l.A d l.A_pos hd0 (u • a); rwa [← hd] at this
    try simp only
    rw [hdiv, htow, hu, add_smul, one_smul, mul_smul, Nat.cast_smul_eq_nsmul, I.add,
      (I.ker _ l.A_pos _).2 ⟨_, rfl⟩, mul_one]
  · intro a ha
    obtain ⟨dM, hdM⟩ := M_dvd_M' l
    have hMp : 0 < l.M := by have := l.three_le; omega
    have hdM0 : 0 < dM := Nat.pos_of_ne_zero (by rintro rfl; simp at hdM; omega)
    have hdivM : l.M' / l.M = dM := by rw [hdM, Nat.mul_div_cancel_left _ hMp]
    have htow : I.ev l.M' (u • a) ^ dM = I.ev l.M (u • a) := by
      have := I.tower l.M dM hMp hdM0 (u • a); rwa [← hdM] at this
    obtain ⟨y, hy⟩ := smul_mem_M l hc ha
    try simp only
    rw [hdivM, htow, hu, add_smul, one_smul, mul_smul, hy, Nat.cast_smul_eq_nsmul, smul_comm, I.add,
      (I.ker _ hMp _).2 ⟨_, rfl⟩, mul_one]

end GlobalTheory.FullLevel
