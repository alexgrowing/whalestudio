import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorTeichmullerIsAdicCompleteOfPerfectStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerDistinguishedRegularSequenceStatement

open scoped NNReal

namespace GlobalTheory

theorem wittVector_isUnit_of_isUnit_coeff_zero (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O]
    [CharP O l] [PerfectRing O l] (c : WittVector l O) (hc : IsUnit (c.coeff 0)) : IsUnit c := by
  obtain ⟨u, hu⟩ := hc
  set d := WittVector.teichmuller l (↑u⁻¹ : O) * c with hd
  have h0 : (d - 1).coeff 0 = 0 := by
    have : (d - 1) + 1 = d := sub_add_cancel d 1
    have h2 := congrArg (fun t => t.coeff 0) this
    simp only [WittVector.add_coeff_zero, WittVector.one_coeff_zero, hd,
      WittVector.mul_coeff_zero, WittVector.teichmuller_coeff_zero, ← hu, Units.inv_mul] at h2
    linear_combination h2
  rw [← WittVector.mem_span_p_iff_coeff_zero_eq_zero] at h0
  have hj := IsAdicComplete.le_jacobson_bot (Ideal.span {((l : ℕ) : WittVector l O)}) h0
  have hd1 : IsUnit d := by
    have := (Ideal.mem_jacobson_bot.mp hj) 1
    simpa using this
  exact isUnit_of_mul_isUnit_right hd1

theorem wittVector_natCast_mul_coeff_zero (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O]
    [CharP O l] [PerfectRing O l] (a : WittVector l O) :
    (((l : ℕ) : WittVector l O) * a).coeff 0 = 0 := by
  rw [← WittVector.mem_span_p_iff_coeff_zero_eq_zero]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem wittVector_eq_teichmuller_add (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O]
    [CharP O l] [PerfectRing O l] (a : WittVector l O) :
    ∃ a₁ : WittVector l O, a = WittVector.teichmuller l (a.coeff 0) + ((l : ℕ) : WittVector l O) * a₁ := by
  have h0 : (a - WittVector.teichmuller l (a.coeff 0)).coeff 0 = 0 := by
    have : (a - WittVector.teichmuller l (a.coeff 0)) + WittVector.teichmuller l (a.coeff 0) = a :=
      sub_add_cancel _ _
    have h2 := congrArg (fun t => t.coeff 0) this
    simp only [WittVector.add_coeff_zero, WittVector.teichmuller_coeff_zero] at h2
    linear_combination h2
  rw [← WittVector.mem_span_p_iff_coeff_zero_eq_zero, Ideal.mem_span_singleton] at h0
  obtain ⟨a₁, ha₁⟩ := h0
  exact ⟨a₁, by rw [← ha₁]; ring⟩

section Distinguished

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [CharP O l] [PerfectRing O l]
  (x : O) (e : ℕ) (w E' : WittVector l O)

theorem teichmuller_pow_not_mem_span (hx : x ≠ 0) (hxu : ¬ IsUnit x) (he : 0 < e) (hw : IsUnit w)
    (hE : E' = WittVector.teichmuller l x ^ e + ((l : ℕ) : WittVector l O) * w) (N : ℕ) :
    WittVector.teichmuller l x ^ N ∉ Ideal.span {E'} := by
  intro h
  rw [Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  have hT : WittVector.teichmuller l x ≠ 0 := by
    intro h0; apply hx; rw [← WittVector.teichmuller_coeff_zero l x, h0]; simp
  obtain ⟨d, rfl⟩ := (GlobalTheory.T.teichmuller_distinguished_regular_sequence l O x e w E' hx he hw hE N c).1 ⟨1, by rw [← hc]; ring⟩
  have h1 : E' * d = 1 := by
    apply mul_left_cancel₀ (pow_ne_zero N hT)
    linear_combination -hc
  have hu : IsUnit E' := IsUnit.of_mul_eq_one d h1
  have hc0 : IsUnit (E'.coeff 0) := by
    have := hu.map (WittVector.constantCoeff (p := l) (R := O))
    simpa [WittVector.constantCoeff] using this
  rw [hE, WittVector.add_coeff_zero, wittVector_natCast_mul_coeff_zero, add_zero, ← map_pow,
    WittVector.teichmuller_coeff_zero] at hc0
  exact hxu ((isUnit_pow_iff he.ne').mp hc0)

end Distinguished

section Distinguished2

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l]
  [PerfectRing O l] (x : O) (e : ℕ) (w E' : WittVector l O)

theorem teichmuller_distinguished_normal_form_step (hw : IsUnit w)
    (hE : E' = WittVector.teichmuller l x ^ e + ((l : ℕ) : WittVector l O) * w) (a : WittVector l O) :
    (∃ a' : WittVector l O, a - WittVector.teichmuller l x ^ e * a' ∈ Ideal.span {E'}) ∨
    ∃ y : O, y ∣ x ^ e ∧ ∃ u : WittVector l O, IsUnit u ∧
      a - WittVector.teichmuller l y * u ∈ Ideal.span {E'} := by
  obtain ⟨v, hv⟩ := hw.exists_right_inv
  obtain ⟨a₁, ha⟩ := wittVector_eq_teichmuller_add l O a
  set a₀ := a.coeff 0
  have hL : ((l : ℕ) : WittVector l O) = E' * v - WittVector.teichmuller l x ^ e * v := by
    rw [hE]; linear_combination (-(((l : ℕ) : WittVector l O))) * hv
  have hmem : E' * (v * a₁) ∈ Ideal.span {E'} :=
    Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  obtain ⟨c, hc | hc⟩ := ValuationRing.cond a₀ (x ^ e)
  ·
    by_cases hcu : IsUnit c
    · left
      obtain ⟨c', hc'⟩ := hcu.exists_right_inv
      have ha₀ : a₀ = x ^ e * c' := by rw [← hc, mul_assoc, hc', mul_one]
      refine ⟨WittVector.teichmuller l c' - v * a₁, ?_⟩
      convert hmem using 1
      rw [ha, ha₀, map_mul, map_pow, hL]; ring
    · right
      refine ⟨a₀, ⟨c, hc.symm⟩, 1 - WittVector.teichmuller l c * (v * a₁), ?_, ?_⟩
      · apply wittVector_isUnit_of_isUnit_coeff_zero
        have h2 : (1 - WittVector.teichmuller l c * (v * a₁)).coeff 0 =
            1 - c * (v * a₁).coeff 0 := by
          have : (1 - WittVector.teichmuller l c * (v * a₁)) +
              WittVector.teichmuller l c * (v * a₁) = 1 := sub_add_cancel _ _
          have h3 := congrArg (fun t => t.coeff 0) this
          simp only [WittVector.add_coeff_zero, WittVector.one_coeff_zero, WittVector.mul_coeff_zero,
            WittVector.teichmuller_coeff_zero] at h3
          rw [WittVector.mul_coeff_zero]
          linear_combination h3
        rw [h2]
        rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (c * (v * a₁).coeff 0) with h | h
        · exact absurd (isUnit_of_mul_isUnit_left h) hcu
        · exact h
      · convert hmem using 1
        rw [ha, hL, ← map_pow, ← hc, map_mul]; ring
  ·
    left
    refine ⟨WittVector.teichmuller l c - v * a₁, ?_⟩
    convert hmem using 1
    rw [ha, ← hc, map_mul, map_pow, hL]; ring

theorem teichmuller_distinguished_normal_form_iter (hw : IsUnit w)
    (hE : E' = WittVector.teichmuller l x ^ e + ((l : ℕ) : WittVector l O) * w) (n : ℕ) :
    ∀ a : WittVector l O,
    (∃ a' : WittVector l O, a - WittVector.teichmuller l x ^ (e * n) * a' ∈ Ideal.span {E'}) ∨
    ∃ y : O, y ∣ x ^ (e * n) ∧ ∃ u : WittVector l O, IsUnit u ∧
      a - WittVector.teichmuller l y * u ∈ Ideal.span {E'} := by
  induction n with
  | zero => intro a; left; exact ⟨a, by simp⟩
  | succ n ih =>
    intro a
    rcases ih a with ⟨a', ha'⟩ | ⟨y, hy, u, hu, hya⟩
    · rcases teichmuller_distinguished_normal_form_step l O x e w E' hw hE a' with ⟨a'', ha''⟩ | ⟨y, hy, u, hu, hya⟩
      · left
        refine ⟨a'', ?_⟩
        have := Ideal.add_mem _ ha' (Ideal.mul_mem_left _ (WittVector.teichmuller l x ^ (e * n)) ha'')
        convert this using 1
        rw [Nat.mul_succ, pow_add]; ring
      · right
        refine ⟨x ^ (e * n) * y, ?_, u, hu, ?_⟩
        · rw [Nat.mul_succ, pow_add]; exact mul_dvd_mul_left _ hy
        · have := Ideal.add_mem _ ha' (Ideal.mul_mem_left _ (WittVector.teichmuller l x ^ (e * n)) hya)
          convert this using 1
          rw [map_mul, map_pow]; ring
    · right
      exact ⟨y, hy.trans (pow_dvd_pow _ (Nat.mul_le_mul_left e n.le_succ)), u, hu, hya⟩

end Distinguished2

section Distinguished3

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [CharP O l]
  [PerfectRing O l] (x : O) (e : ℕ) (w E' : WittVector l O)

theorem mem_span_singleton_pow_smul_top_iff_dvd {R : Type} [CommRing R] (t a : R) (m : ℕ) :
    a ∈ (Ideal.span {t} ^ m • ⊤ : Submodule R R) ↔ t ^ m ∣ a := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem teichmuller_distinguished_span_closed (hx : x ≠ 0) (he : 0 < e) (hw : IsUnit w)
    (hE : E' = WittVector.teichmuller l x ^ e + ((l : ℕ) : WittVector l O) * w)
    (hc : IsAdicComplete (Ideal.span {x}) O) (a : WittVector l O)
    (h : ∀ k : ℕ, ∃ c : WittVector l O, a - WittVector.teichmuller l x ^ k * c ∈ Ideal.span {E'}) :
    a ∈ Ideal.span {E'} := by
  set T := WittVector.teichmuller l x with hTdef
  have hcT := (GlobalTheory.T.wittVector_teichmuller_isAdicComplete_of_perfect l O x hx hc).1
  have hreg := GlobalTheory.T.teichmuller_distinguished_regular_sequence l O x e w E' hx he hw hE
  choose c hc' using h
  have hb : ∀ k, ∃ b : WittVector l O, a = E' * b + T ^ k * c k := by
    intro k
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (hc' k)
    exact ⟨b, by rw [← hb]; ring⟩
  choose b hb using hb
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → b m ≡ b n [SMOD (Ideal.span {T} ^ m • ⊤ : Submodule (WittVector l O) (WittVector l O))] := by
    intro m n hmn
    rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_dvd]
    apply (hreg m _).1
    refine ⟨c n * T ^ (n - m) - c m, ?_⟩
    have h1 := (hb m).symm.trans (hb n)
    have h2 : T ^ n = T ^ m * T ^ (n - m) := by rw [← pow_add, Nat.add_sub_cancel' hmn]
    rw [h2] at h1
    linear_combination h1
  obtain ⟨L, hL⟩ := hcT.toIsPrecomplete.prec hcauchy
  have hzero : a - E' * L = 0 := by
    apply hcT.toIsHausdorff.haus
    intro n
    rw [SModEq.sub_mem, sub_zero, mem_span_singleton_pow_smul_top_iff_dvd]
    have hn := hL n
    rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_dvd] at hn
    obtain ⟨d, hd⟩ := hn
    refine ⟨E' * d + c n, ?_⟩
    rw [hb n]
    linear_combination E' * hd
  rw [Ideal.mem_span_singleton]
  exact ⟨L, by linear_combination hzero⟩

end Distinguished3

theorem teichmuller_distinguished_span_isPrime : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (x : O), x ≠ 0 → ¬ IsUnit x → IsAdicComplete (Ideal.span {x}) O → ∀ (e : ℕ) (w E' : WittVector l O), 0 < e → IsUnit w → E' = WittVector.teichmuller l x ^ e + ((l : ℕ) : WittVector l O) * w → (Ideal.span {E'}).IsPrime ∧ ((l : ℕ) : WittVector l O) ∉ Ideal.span {E'} := by
  intro l _ O _ _ _ _ _ x hx hxu hc e w E' he hw hE
  have hnot := teichmuller_pow_not_mem_span l O x e w E' hx hxu he hw hE

  have hform : ∀ a : WittVector l O, a ∉ Ideal.span {E'} → ∃ (y : O) (N : ℕ), y ∣ x ^ N ∧
      ∃ u : WittVector l O, IsUnit u ∧ a - WittVector.teichmuller l y * u ∈ Ideal.span {E'} := by
    intro a ha
    have : ¬ ∀ k : ℕ, ∃ c : WittVector l O,
        a - WittVector.teichmuller l x ^ k * c ∈ Ideal.span {E'} :=
      fun h => ha (teichmuller_distinguished_span_closed l O x e w E' hx he hw hE hc a h)
    push_neg at this
    obtain ⟨k, hk⟩ := this
    rcases teichmuller_distinguished_normal_form_iter l O x e w E' hw hE k a with ⟨a', ha'⟩ | ⟨y, hy, u, hu, hya⟩
    · exfalso
      apply hk (WittVector.teichmuller l x ^ (e * k - k) * a')
      convert ha' using 2
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' (Nat.le_mul_of_pos_left k he)]
    · exact ⟨y, e * k, hy, u, hu, hya⟩
  have hI : Ideal.span {E'} ≠ ⊤ := by
    intro h
    exact hnot 0 (by rw [h]; exact Submodule.mem_top)
  refine ⟨(Ideal.isPrime_iff).mpr ⟨hI, ?_⟩, ?_⟩
  · intro a b hab
    by_contra hne
    push_neg at hne
    obtain ⟨y, N, hy, u, hu, hya⟩ := hform a hne.1
    obtain ⟨y', N', hy', u', hu', hyb⟩ := hform b hne.2
    obtain ⟨s, hs⟩ := mul_dvd_mul hy hy'
    have h1 : WittVector.teichmuller l (y * y') * (u * u') ∈ Ideal.span {E'} := by
      have := Ideal.sub_mem _ hab (Ideal.add_mem _ (Ideal.mul_mem_right b _ hya)
        (Ideal.mul_mem_left _ (WittVector.teichmuller l y * u) hyb))
      convert this using 1
      rw [map_mul]; ring
    obtain ⟨v, hv⟩ := (hu.mul hu').exists_right_inv
    have h2 : WittVector.teichmuller l (y * y') ∈ Ideal.span {E'} := by
      have := Ideal.mul_mem_right v _ h1
      rwa [mul_assoc, hv, mul_one] at this
    apply hnot (N + N')
    have := Ideal.mul_mem_right (WittVector.teichmuller l s) _ h2
    rw [← map_mul, ← hs, map_mul, map_pow, map_pow, ← pow_add] at this
    exact this
  · intro hl
    apply hnot e
    have : E' - ((l : ℕ) : WittVector l O) * w ∈ Ideal.span {E'} :=
      Ideal.sub_mem _ (Ideal.mem_span_singleton_self _) (Ideal.mul_mem_right _ _ hl)
    convert this using 1
    rw [hE]; ring

end GlobalTheory
