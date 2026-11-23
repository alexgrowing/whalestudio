import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SmulFinsum

set_option linter.style.haveILetI false

noncomputable section

namespace Formalism.IndefR.Fin.Four

variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]

private theorem chi_nsmul_left_eq_pow {χ : W → W → ℂ} (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
    (hχ0 : ∀ t y, χ t y ≠ 0) (s y : W) (n : ℕ) : χ (n • s) y = χ s y ^ n := by
  induction n with
  | zero =>
    rw [zero_smul, pow_zero]
    have h := hχl 0 0 y
    rw [add_zero] at h
    exact mul_left_cancel₀ (hχ0 0 y) (h.symm.trans (mul_one _).symm)
  | succ n ih => rw [succ_nsmul, hχl, ih, pow_succ]

private theorem chi_nsmul_right_eq_pow {χ : W → W → ℂ} (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y')
    (hχ0 : ∀ t y, χ t y ≠ 0) (s y : W) (n : ℕ) : χ s (n • y) = χ s y ^ n := by
  induction n with
  | zero =>
    rw [zero_smul, pow_zero]
    have h := hχr s 0 0
    rw [add_zero] at h
    exact mul_left_cancel₀ (hχ0 s 0) (h.symm.trans (mul_one _).symm)
  | succ n ih => rw [succ_nsmul, hχr, ih, pow_succ]

theorem mk_out_sub (S : AddSubgroup W) (a : W) : ∃ l ∈ S, (QuotientAddGroup.mk a : W ⧸ S).out = a + l := by
  have h := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' (QuotientAddGroup.mk a : W ⧸ S))
  refine ⟨(QuotientAddGroup.mk a : W ⧸ S).out - a, ?_, by abel⟩
  have h2 := S.neg_mem h
  have h3 : -(-(QuotientAddGroup.mk a : W ⧸ S).out + a) = (QuotientAddGroup.mk a : W ⧸ S).out - a := by abel
  rw [h3] at h2
  exact h2

theorem finite_out_smul (H : AddSubgroup W) {k : ℕ} [Finite (Qt (k * k) H)] (htf : ∀ t : W, k • t = 0 → t = 0) :
    {q : W ⧸ smulSub k H | k • q.out ∈ H}.Finite := by
  refine Set.finite_coe_iff.mp (Finite.of_injective
    (fun q : {q : W ⧸ smulSub k H | k • q.out ∈ H} =>
      (QuotientAddGroup.mk (⟨k • q.1.out, q.2⟩ : H) : Qt (k * k) H)) ?_)
  rintro ⟨q₁, h₁⟩ ⟨q₂, h₂⟩ he
  have he' := QuotientAddGroup.eq.mp he
  rw [AddSubgroup.mem_addSubgroupOf] at he'
  have hm : k • (-q₁.out + q₂.out) ∈ smulSub (k * k) H := by
    convert he' using 1
    simp [smul_add, smul_neg]
  obtain ⟨h, hH, hh⟩ := AddSubgroup.mem_map.mp hm
  have key : -q₁.out + q₂.out = k • h := by
    have h0 : k • (-q₁.out + q₂.out - k • h) = 0 := by
      rw [smul_sub, smul_smul]
      exact sub_eq_zero.mpr hh.symm
    exact sub_eq_zero.mp (htf _ h0)
  have e1 := QuotientAddGroup.out_eq' q₁
  have e2 := QuotientAddGroup.out_eq' q₂
  refine Subtype.ext (e1.symm.trans (Eq.trans ?_ e2))
  exact QuotientAddGroup.eq.mpr (by rw [key]; exact AddSubgroup.mem_map_of_mem _ hH)

section Uniq

variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W} {f₀ : V}

def Gk (L Y : AddSubgroup W) (k : ℕ) : AddSubgroup (QY L Y) :=
  (Y ⊓ L.comap (nsmulAddMonoidHom k)).map (QuotientAddGroup.mk' (L ⊓ Y))

def Pk (ρ : W → Module.End ℂ V) (L Y : AddSubgroup W) (f₀ : V) (k : ℕ) : V :=
  (Nat.card (Gk L Y k) : ℂ)⁻¹ • ∑ᶠ g : Gk L Y k, ρ ((g : QY L Y).out) f₀

open Classical in

def indk (L X : AddSubgroup W) (k : ℕ) (t : W) : ℂ := if t ∈ smulSub k (L ⊓ X) then 1 else 0

theorem Gk_out {k : ℕ} (g : Gk L Y k) : (g : QY L Y).out ∈ Y ∧ k • (g : QY L Y).out ∈ L := by
  obtain ⟨g, hg⟩ := g
  obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.mp hg
  rw [AddSubgroup.mem_inf, AddSubgroup.mem_comap] at hy
  obtain ⟨l, hl, he⟩ := mk_out_sub (L ⊓ Y) y
  change (QuotientAddGroup.mk y : W ⧸ (L ⊓ Y)).out ∈ Y ∧ k • (QuotientAddGroup.mk y : W ⧸ (L ⊓ Y)).out ∈ L
  rw [he]
  rw [AddSubgroup.mem_inf] at hl
  refine ⟨Y.add_mem hy.1 hl.2, ?_⟩
  rw [smul_add]
  exact L.add_mem hy.2 (nsmul_mem hl.1 k)

theorem Gk_finite (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y))) (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)
    {k : ℕ} (hk : 0 < k) : Finite (Gk L Y k) := by
  haveI := hfinY k hk
  refine Finite.of_injective (fun g : Gk L Y k =>
    (QuotientAddGroup.mk (⟨k • (g : QY L Y).out,
      AddSubgroup.mem_inf.mpr ⟨(Gk_out g).2, nsmul_mem (Gk_out g).1 k⟩⟩ : ↥(L ⊓ Y)) : Qt k (L ⊓ Y))) ?_
  intro g₁ g₂ he
  have he' := QuotientAddGroup.eq.mp he
  rw [AddSubgroup.mem_addSubgroupOf] at he'
  have hm : k • (-(g₁ : QY L Y).out + (g₂ : QY L Y).out) ∈ smulSub k (L ⊓ Y) := by
    convert he' using 1
    simp [smul_add, smul_neg]
  obtain ⟨m, hmm, hkm⟩ := AddSubgroup.mem_map.mp hm
  have key : -(g₁ : QY L Y).out + (g₂ : QY L Y).out = m := by
    have h0 : k • (-(g₁ : QY L Y).out + (g₂ : QY L Y).out - m) = 0 := by
      rw [smul_sub]
      exact sub_eq_zero.mpr hkm.symm
    exact sub_eq_zero.mp (htf k hk _ h0)
  apply Subtype.ext
  have e1 := QuotientAddGroup.out_eq' (g₁ : QY L Y)
  have e2 := QuotientAddGroup.out_eq' (g₂ : QY L Y)
  refine e1.symm.trans (Eq.trans ?_ e2)
  exact QuotientAddGroup.eq.mpr (by rw [key]; exact hmm)

end Uniq

section Uniq2

variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W} {f₀ : V}
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
  (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1)
  (hdX : ∀ x ∈ X, (∀ y ∈ L ⊓ Y, χ x y = 1) → x ∈ L)
  (hdivX : ∀ k : ℕ, 0 < k → ∀ s ∈ X, ∃ t ∈ X, k • t = s)
  (hdivY : ∀ k : ℕ, 0 < k → ∀ s ∈ Y, ∃ t ∈ Y, k • t = s)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X))) (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y)))
  (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)

include hχr hLL in
theorem chi_out_add {k : ℕ} {t : W} (ht : t ∈ L ⊓ X) (g g' : Gk L Y k) :
    χ t ((g + g' : Gk L Y k) : QY L Y).out = χ t (g : QY L Y).out * χ t (g' : QY L Y).out := by
  have hsum : ((g + g' : Gk L Y k) : QY L Y) =
      QuotientAddGroup.mk ((g : QY L Y).out + (g' : QY L Y).out) := by
    rw [AddSubgroup.coe_add, QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']
  obtain ⟨l, hl, he⟩ := mk_out_sub (L ⊓ Y) ((g : QY L Y).out + (g' : QY L Y).out)
  rw [hsum, he, hχr, hχr, hLL t ht l hl, mul_one]

include hχl hχr hχ0 hLL hdX hdivX hdivY hfinY htf in
open Classical in
theorem chi_sum {k : ℕ} (hk : 0 < k) {t : W} (ht : t ∈ L ⊓ X) :
    ∑ᶠ g : Gk L Y k, χ t (g : QY L Y).out =
      if t ∈ smulSub k (L ⊓ X) then (Nat.card (Gk L Y k) : ℂ) else 0 := by
  haveI : Finite (Gk L Y k) := Gk_finite hfinY htf hk
  letI : Fintype (Gk L Y k) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  split_ifs with hts
  · have h1 : ∀ g : Gk L Y k, χ t (g : QY L Y).out = 1 := by
      intro g
      obtain ⟨s, hs, hst⟩ := AddSubgroup.mem_map.mp hts
      have hst' : t = k • s := hst.symm
      obtain ⟨hgY, hgL⟩ := Gk_out g
      rw [hst', chi_nsmul_left_eq_pow hχl hχ0, ← chi_nsmul_right_eq_pow hχr hχ0]
      exact hLL s hs _ (AddSubgroup.mem_inf.mpr ⟨hgL, nsmul_mem hgY k⟩)
    rw [Finset.sum_congr rfl (fun g _ => h1 g), Finset.sum_const, Finset.card_univ,
      Nat.card_eq_fintype_card, nsmul_eq_mul, mul_one]
  · have hne : ∃ g : Gk L Y k, χ t (g : QY L Y).out ≠ 1 := by
      by_contra hall
      push_neg at hall
      apply hts
      have htX : t ∈ X := (AddSubgroup.mem_inf.mp ht).2
      obtain ⟨s, hsX, hks⟩ := hdivX k hk t htX
      have hsL : s ∈ L := by
        apply hdX s hsX
        intro y hy
        obtain ⟨y', hy'Y, hky'⟩ := hdivY k hk y (AddSubgroup.mem_inf.mp hy).2
        have hmem : (QuotientAddGroup.mk y' : QY L Y) ∈ Gk L Y k := by
          refine AddSubgroup.mem_map.mpr ⟨y', AddSubgroup.mem_inf.mpr ⟨hy'Y, ?_⟩, rfl⟩
          show k • y' ∈ L
          rw [hky']
          exact (AddSubgroup.mem_inf.mp hy).1
        have h1 := hall ⟨_, hmem⟩
        obtain ⟨l, hl, he⟩ := mk_out_sub (L ⊓ Y) y'
        have h2 : χ t (QuotientAddGroup.mk y' : QY L Y).out = χ t y' := by
          rw [he, hχr, hLL t ht l hl, mul_one]
        rw [← hky', chi_nsmul_right_eq_pow hχr hχ0, ← chi_nsmul_left_eq_pow hχl hχ0, hks, ← h2]
        exact h1
      exact AddSubgroup.mem_map.mpr ⟨s, AddSubgroup.mem_inf.mpr ⟨hsL, hsX⟩, hks⟩
    obtain ⟨g₀, hg₀⟩ := hne
    have hS : ∑ g : Gk L Y k, χ t (g : QY L Y).out =
        χ t (g₀ : QY L Y).out * ∑ g : Gk L Y k, χ t (g : QY L Y).out := by
      rw [Finset.mul_sum]
      symm
      refine Fintype.sum_equiv (Equiv.addLeft g₀) _ _ (fun g => ?_)
      exact (chi_out_add hχr hLL ht g₀ g).symm
    have h3 : (1 - χ t (g₀ : QY L Y).out) * ∑ g : Gk L Y k, χ t (g : QY L Y).out = 0 := by
      rw [sub_mul, one_mul, ← hS, sub_self]
    exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm hg₀))

include hχl hχr hχ0 hLL hdX hdivX hdivY hfinY htf in
open Classical in
theorem indk_eq {k : ℕ} (hk : 0 < k) (t : W) :
    indk L X k t = (Nat.card (Gk L Y k) : ℂ)⁻¹ * ∑ᶠ g : Gk L Y k,
      χ t (g : QY L Y).out * (if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) := by
  haveI : Finite (Gk L Y k) := Gk_finite hfinY htf hk
  have hcard : (Nat.card (Gk L Y k) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  unfold indk
  by_cases htLX : t ∈ L ∧ t ∈ X
  · rw [if_pos htLX]
    simp only [mul_one]
    rw [chi_sum hχl hχr hχ0 hLL hdX hdivX hdivY hfinY htf hk (AddSubgroup.mem_inf.mpr htLX)]
    split_ifs
    · exact (inv_mul_cancel₀ hcard).symm
    · simp
  · have hnot : t ∉ smulSub k (L ⊓ X) := by
      intro hm
      obtain ⟨s, hs, hst⟩ := AddSubgroup.mem_map.mp hm
      apply htLX
      rw [← hst]
      exact AddSubgroup.mem_inf.mp (nsmul_mem hs k)
    rw [if_neg hnot, if_neg htLX]
    simp

open Classical in
theorem isSB_indk {k : ℕ} (hk : 0 < k) : IsSB L X (indk L X k) := by
  have hmem : ∀ t, indk L X k t ≠ 0 → t ∈ L ⊓ X := by
    intro t ht
    unfold indk at ht
    split_ifs at ht with h
    · obtain ⟨s, hs, rfl⟩ := AddSubgroup.mem_map.mp h
      exact nsmul_mem hs k
    · exact absurd rfl ht
  refine ⟨fun t ht => (AddSubgroup.mem_inf.mp (hmem t ht)).2, k, hk, ?_,
    fun t ht => nsmul_mem (AddSubgroup.mem_inf.mp (hmem t ht)).1 k⟩
  intro u hu t
  have hku : k • u ∈ smulSub k (L ⊓ X) := AddSubgroup.mem_map_of_mem _ hu
  have hiff : t + k • u ∈ smulSub k (L ⊓ X) ↔ t ∈ smulSub k (L ⊓ X) :=
    (smulSub k (L ⊓ X)).add_mem_cancel_right hku
  unfold indk
  by_cases h : t ∈ smulSub k (L ⊓ X)
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (mt hiff.mp h), if_neg h]

include hχl hχr hχ0 hLL hdX hdivX hdivY hfinY htf in
open Classical in
theorem T_indk (T : (W → ℂ) →ₗ[ℂ] V)
    (hmo : ∀ Φ, IsSB L X Φ → ∀ y ∈ Y, T (fun t => χ t y * Φ t) = ρ y (T Φ))
    (hva : T (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) = f₀) {k : ℕ} (hk : 0 < k) :
    T (indk L X k) = Pk ρ L Y f₀ k := by
  haveI : Finite (Gk L Y k) := Gk_finite hfinY htf hk
  letI : Fintype (Gk L Y k) := Fintype.ofFinite _
  have h1 : IsSB L X (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) := by
    refine ⟨fun t ht => ?_, 1, one_pos, fun u hu t => ?_, fun t ht => ?_⟩
    · by_contra h
      exact ht (if_neg (fun h' => h h'.2))
    · have hu' := AddSubgroup.mem_inf.mp hu
      have hiff : (t + u ∈ L ∧ t + u ∈ X) ↔ (t ∈ L ∧ t ∈ X) :=
        and_congr (L.add_mem_cancel_right hu'.1) (X.add_mem_cancel_right hu'.2)
      show (if t + 1 • u ∈ L ∧ t + 1 • u ∈ X then (1 : ℂ) else 0) = if t ∈ L ∧ t ∈ X then 1 else 0
      rw [one_smul]
      by_cases h : t ∈ L ∧ t ∈ X
      · rw [if_pos (hiff.mpr h), if_pos h]
      · rw [if_neg (mt hiff.mp h), if_neg h]
    · rw [one_smul]
      by_contra h
      exact ht (if_neg (fun h' => h h'.1))
  have hfun : indk L X k = ∑ g : Gk L Y k, ((Nat.card (Gk L Y k) : ℂ)⁻¹ •
      (fun t => χ t (g : QY L Y).out * (if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0))) := by
    funext t
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [indk_eq hχl hχr hχ0 hLL hdX hdivX hdivY hfinY htf hk t, finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [hfun, map_sum]
  simp only [map_smul]
  unfold Pk
  rw [finsum_eq_sum_of_fintype, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  congr 1
  have h2 := hmo _ h1 _ (Gk_out g).1
  rw [h2, hva]

end Uniq2

section Uniq3

variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W} {f₀ : V}
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
  (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1)
  (hdX : ∀ x ∈ X, (∀ y ∈ L ⊓ Y, χ x y = 1) → x ∈ L)
  (hdivX : ∀ k : ℕ, 0 < k → ∀ s ∈ X, ∃ t ∈ X, k • t = s)
  (hdivY : ∀ k : ℕ, 0 < k → ∀ s ∈ Y, ∃ t ∈ Y, k • t = s)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X))) (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y)))
  (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)

include hχl hχr hχ0 hLL hdX hdivX hdivY hfinX hfinY htf in
open Classical in

theorem T_formula (T : (W → ℂ) →ₗ[ℂ] V)
    (htr : ∀ Φ, IsSB L X Φ → ∀ x ∈ X, T (fun t => Φ (t + x)) = ρ x (T Φ))
    (hmo : ∀ Φ, IsSB L X Φ → ∀ y ∈ Y, T (fun t => χ t y * Φ t) = ρ y (T Φ))
    (hva : T (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) = f₀)
    {Φ : W → ℂ} {k : ℕ} (hk : 0 < k) (hs : ∀ t, Φ t ≠ 0 → t ∈ X)
    (hi : ∀ u ∈ L ⊓ X, ∀ t, Φ (t + k • u) = Φ t) (hl : ∀ t, Φ t ≠ 0 → k • t ∈ L) :
    T Φ = ∑ᶠ q : W ⧸ smulSub k (L ⊓ X), Φ q.out • ρ (-q.out) (Pk ρ L Y f₀ k) := by
  haveI := hfinX (k * k) (Nat.mul_pos hk hk)
  have hfin : {q : W ⧸ smulSub k (L ⊓ X) | Φ q.out ≠ 0}.Finite := by
    refine (finite_out_smul (L ⊓ X) (htf k hk)).subset ?_
    intro q hq
    exact AddSubgroup.mem_inf.mpr ⟨hl _ hq, nsmul_mem (hs _ hq) k⟩
  have hinv : ∀ t, Φ ((QuotientAddGroup.mk t : W ⧸ smulSub k (L ⊓ X)).out) = Φ t := by
    intro t
    obtain ⟨l, hl', he⟩ := mk_out_sub (smulSub k (L ⊓ X)) t
    obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.mp hl'
    rw [he]
    exact hi u hu t
  have hone : ∀ t, indk L X k (t + -(QuotientAddGroup.mk t : W ⧸ smulSub k (L ⊓ X)).out) = 1 := by
    intro t
    obtain ⟨l, hl', he⟩ := mk_out_sub (smulSub k (L ⊓ X)) t
    rw [he]
    unfold indk
    apply if_pos
    have h3 : t + -(t + l) = -l := by abel
    rw [h3]
    exact neg_mem hl'
  have hzero : ∀ t (q : W ⧸ smulSub k (L ⊓ X)), q ≠ QuotientAddGroup.mk t →
      indk L X k (t + -q.out) = 0 := by
    intro t q hq
    unfold indk
    apply if_neg
    intro hm
    apply hq
    rw [← QuotientAddGroup.out_eq' q]
    apply QuotientAddGroup.eq.mpr
    rw [add_comm]
    exact hm
  have hdec : Φ = ∑ q ∈ hfin.toFinset, Φ q.out • (fun t => indk L X k (t + -q.out)) := by
    funext t
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (QuotientAddGroup.mk t)]
    · rw [hone, mul_one, hinv]
    · intro q _ hq
      rw [hzero t q hq, mul_zero]
    · intro hn
      rw [hone, mul_one, hinv]
      by_contra h0
      apply hn
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, hinv]
      exact h0
  have hX : ∀ q ∈ hfin.toFinset, -q.out ∈ X := by
    intro q hq
    exact neg_mem (hs _ (hfin.mem_toFinset.mp hq))
  have hsub : (Function.support fun q : W ⧸ smulSub k (L ⊓ X) =>
      Φ q.out • ρ (-q.out) (Pk ρ L Y f₀ k)) ⊆ ↑hfin.toFinset := by
    intro q hq
    rw [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h0
    apply hq
    simp only [h0, zero_smul]
  rw [finsum_eq_sum_of_support_subset _ hsub]
  conv_lhs => rw [hdec]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  rw [map_smul, htr _ (isSB_indk hk) _ (hX q hq),
    T_indk hχl hχr hχ0 hLL hdX hdivX hdivY hfinY htf T hmo hva hk]

include hχl hχr hχ0 hLL hdX hdivX hdivY hfinX hfinY htf in
open Classical in

theorem model_unique (T T' : (W → ℂ) →ₗ[ℂ] V)
    (htr : ∀ Φ, IsSB L X Φ → ∀ x ∈ X, T (fun t => Φ (t + x)) = ρ x (T Φ))
    (hmo : ∀ Φ, IsSB L X Φ → ∀ y ∈ Y, T (fun t => χ t y * Φ t) = ρ y (T Φ))
    (hva : T (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) = f₀)
    (htr' : ∀ Φ, IsSB L X Φ → ∀ x ∈ X, T' (fun t => Φ (t + x)) = ρ x (T' Φ))
    (hmo' : ∀ Φ, IsSB L X Φ → ∀ y ∈ Y, T' (fun t => χ t y * Φ t) = ρ y (T' Φ))
    (hva' : T' (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) = f₀)
    {Φ : W → ℂ} (hΦ : IsSB L X Φ) : T' Φ = T Φ := by
  obtain ⟨hs, k, hk, hi, hl⟩ := hΦ
  rw [T_formula hχl hχr hχ0 hLL hdX hdivX hdivY hfinX hfinY htf T' htr' hmo' hva' hk hs hi hl,
    T_formula hχl hχr hχ0 hLL hdX hdivX hdivY hfinX hfinY htf T htr hmo hva hk hs hi hl]

include hχl hχr hχ0 hLL hdX hdivX hdivY hfinX hfinY htf in
open Classical in

theorem model_mem_span (T : (W → ℂ) →ₗ[ℂ] V)
    (htr : ∀ Φ, IsSB L X Φ → ∀ x ∈ X, T (fun t => Φ (t + x)) = ρ x (T Φ))
    (hmo : ∀ Φ, IsSB L X Φ → ∀ y ∈ Y, T (fun t => χ t y * Φ t) = ρ y (T Φ))
    (hva : T (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) = f₀)
    {Φ : W → ℂ} (hΦ : IsSB L X Φ) :
    T Φ ∈ Submodule.span ℂ {v | ∃ a ∈ X, ∃ y ∈ Y, v = ρ a (ρ y f₀)} := by
  obtain ⟨hs, k, hk, hi, hl⟩ := hΦ
  haveI : Finite (Gk L Y k) := Gk_finite hfinY htf hk
  letI : Fintype (Gk L Y k) := Fintype.ofFinite _
  rw [T_formula hχl hχr hχ0 hLL hdX hdivX hdivY hfinX hfinY htf T htr hmo hva hk hs hi hl]
  refine finsum_induction (fun v => v ∈ Submodule.span ℂ {v | ∃ a ∈ X, ∃ y ∈ Y, v = ρ a (ρ y f₀)})
    (Submodule.zero_mem _) (fun _ _ => Submodule.add_mem _) (fun q => ?_)
  show Φ q.out • ρ (-q.out) (Pk ρ L Y f₀ k) ∈ _
  by_cases h0 : Φ q.out = 0
  · rw [h0, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    unfold Pk
    rw [map_smul, finsum_eq_sum_of_fintype, map_sum]
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro g _
    exact Submodule.subset_span ⟨-q.out, neg_mem (hs _ h0), (g : QY L Y).out, (Gk_out g).1, rfl⟩

end Uniq3

end Formalism.IndefR.Fin.Four

end
