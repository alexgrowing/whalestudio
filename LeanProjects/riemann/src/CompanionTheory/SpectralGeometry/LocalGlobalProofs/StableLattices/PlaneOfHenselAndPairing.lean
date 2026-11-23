import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich

open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.HermPlane

section Lat

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {V : Type} [AddCommGroup V] [Module L V]

theorem exists_uniformiser [ProperSpace L] :
    ∃ p : L, p ≠ 0 ∧ ‖p‖ < 1 ∧ ∀ a : L, ‖a‖ < 1 → ‖a‖ ≤ ‖p‖ := by
  obtain ⟨a, ha0, ha1⟩ := NormedField.exists_norm_lt_one L
  have hK : IsCompact (Metric.ball (0 : L) 1) :=
    (isCompact_closedBall (0 : L) 1).of_isClosed_subset
      (IsUltrametricDist.isClopen_ball (0 : L) 1).isClosed Metric.ball_subset_closedBall
  have hne : (Metric.ball (0 : L) 1).Nonempty := ⟨0, by simp⟩
  obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn hne (continuous_norm.continuousOn)
  have hle : ∀ b : L, ‖b‖ < 1 → ‖b‖ ≤ ‖p‖ := fun b hb => hmax (by simpa using hb)
  have hp1 : ‖p‖ < 1 := by simpa using hp
  refine ⟨p, ?_, hp1, hle⟩
  intro h0
  have := hle a ha1
  rw [h0, norm_zero] at this
  linarith

theorem lat_smul {Λ : AddSubgroup V} (hΛ : IsLat L Λ) {a : L} (ha : ‖a‖ ≤ 1) {x : V} (hx : x ∈ Λ) :
    a • x ∈ Λ := by
  obtain ⟨m, b, hb⟩ := hΛ
  rw [hb] at hx ⊢
  intro i
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) (hx i)

theorem lat_commens {Λ M : AddSubgroup V} (hΛ : IsLat L Λ) (hM : IsLat L M) {p : L} (hp0 : p ≠ 0)
    (hp1 : ‖p‖ < 1) : ∃ r : ℕ, ∀ x ∈ M, p ^ r • x ∈ Λ := by
  obtain ⟨m, b, hb⟩ := hΛ
  obtain ⟨m', b', hb'⟩ := hM
  set C : ℝ := ∑ i, ∑ j, ‖b.repr (b' j) i‖ + 1 with hC
  have hC0 : 0 < C := by
    have : 0 ≤ ∑ i, ∑ j, ‖b.repr (b' j) i‖ :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hC0) hp1
  refine ⟨r, fun x hx => ?_⟩
  rw [hb]
  intro i
  have hx' := (hb' x).1 hx
  have hexp : b.coord i x = ∑ j, b'.repr x j * b.coord i (b' j) := by
    conv_lhs => rw [← b'.sum_repr x]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
  have hbound : ‖b.repr x i‖ ≤ C := by
    have h1 : ‖b.repr x i‖ ≤ ∑ j, ‖b.repr (b' j) i‖ := by
      have : b.repr x i = ∑ j, b'.repr x j * b.repr (b' j) i := by simpa using hexp
      rw [this]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hx' j)
    have h2 : ∑ j, ‖b.repr (b' j) i‖ ≤ ∑ i, ∑ j, ‖b.repr (b' j) i‖ :=
      Finset.single_le_sum (f := fun i => ∑ j, ‖b.repr (b' j) i‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    linarith
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul, norm_pow]
  calc ‖p‖ ^ r * ‖b.repr x i‖ ≤ C⁻¹ * C :=
        mul_le_mul hr.le hbound (norm_nonneg _) (inv_pos.mpr hC0).le
    _ = 1 := inv_mul_cancel₀ hC0.ne'

theorem lat_primitive {Λ : AddSubgroup V} (hΛ : IsLat L Λ) {p : L} (hp0 : p ≠ 0) (hp1 : ‖p‖ < 1)
    {v : V} (hv : v ≠ 0) : ∃ a : L, a ≠ 0 ∧ a • v ∈ Λ ∧ p⁻¹ • a • v ∉ Λ := by
  obtain ⟨m, b, hb⟩ := id hΛ
  have hex : ∃ i, b.repr v i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv (b.repr.map_eq_zero_iff.1 (Finsupp.ext hcon))
  obtain ⟨i, hi⟩ := hex
  set C : ℝ := ∑ j, ‖b.repr v j‖ + 1 with hC
  have hC0 : 0 < C := by
    have : 0 ≤ ∑ j, ‖b.repr v j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hC0) hp1
  have hk0 : p ^ k ≠ 0 := pow_ne_zero _ hp0
  have hstart : p ^ k • v ∈ Λ := by
    rw [hb]
    intro j
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul, norm_pow]
    have h1 : ‖b.repr v j‖ ≤ C := by
      have : ‖b.repr v j‖ ≤ ∑ j, ‖b.repr v j‖ :=
        Finset.single_le_sum (f := fun j => ‖b.repr v j‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)
      linarith
    calc ‖p‖ ^ k * ‖b.repr v j‖ ≤ C⁻¹ * C := mul_le_mul hk.le h1 (norm_nonneg _) (inv_pos.mpr hC0).le
      _ = 1 := inv_mul_cancel₀ hC0.ne'
  have hpinv : 1 < ‖p⁻¹‖ := by
    rw [norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.2 hp0)).2 hp1
  have hnot : ∃ n : ℕ, (p⁻¹) ^ n • p ^ k • v ∉ Λ := by
    have hc : 0 < ‖p ^ k * b.repr v i‖ := norm_pos_iff.2 (mul_ne_zero hk0 hi)
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖p ^ k * b.repr v i‖)⁻¹ hpinv
    refine ⟨n, fun hmem => ?_⟩
    have := (hb _).1 hmem i
    rw [map_smul, map_smul, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul,
      norm_mul, norm_pow] at this
    have h2 : 1 < ‖p⁻¹‖ ^ n * ‖p ^ k * b.repr v i‖ := by
      have := mul_lt_mul_of_pos_right hn hc
      rwa [inv_mul_cancel₀ hc.ne'] at this
    linarith
  classical
  have hfind := Nat.find_spec hnot
  have hne : Nat.find hnot ≠ 0 := by
    intro h0
    rw [h0] at hfind
    simp at hfind
    exact hfind hstart
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have hmem : (p⁻¹) ^ n • p ^ k • v ∈ Λ := by
    have := Nat.find_min hnot (m := n) (by omega)
    simpa using this
  refine ⟨(p⁻¹) ^ n * p ^ k, mul_ne_zero (pow_ne_zero _ (inv_ne_zero hp0)) hk0, ?_, ?_⟩
  · rwa [mul_smul]
  · rw [hn] at hfind
    intro hcon
    apply hfind
    rw [mul_smul, smul_smul p⁻¹] at hcon
    rwa [Nat.succ_eq_add_one, pow_succ']

end Lat

section Form

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {V : Type} [AddCommGroup V] [Module L V]

theorem herm_add_left {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (x y z : V) :
    h (x + y) z = h x z + h y z := by
  rw [hh.2.2.1 z (x + y), hh.1, map_add, ← hh.2.2.1, ← hh.2.2.1]

theorem herm_smul_left {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (a : L) (x y : V) :
    h (a • x) y = s a * h x y := by
  rw [hh.2.2.1 y (a • x), hh.2.1, map_mul, ← hh.2.2.1]

theorem herm_expand {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (a c : L) (x y : V) :
    h (c • x + a • y) (c • x + a • y) =
      s c * (c * h x x) + s c * (a * h x y) + s a * (c * h y x) + s a * (a * h y y) := by
  rw [herm_add_left hh, hh.1, hh.1, herm_smul_left hh, herm_smul_left hh, hh.2.1, hh.2.1,
    herm_smul_left hh, herm_smul_left hh, hh.2.1, hh.2.1]
  ring

theorem one_le_norm_delta {s : L →+* L} (hs : IsInv s) {δ : L} (hδ : IsDelta s δ) : 1 ≤ ‖δ‖ := by
  have := (hδ.2.1 1).1 (fun x hx => by
    rw [one_mul]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx ?_)
    rw [hs.2.1]
    exact hx)
  simpa using this

theorem isotropic_lift [CompleteSpace L] (hH : StHensel) {s : L →+* L} (hs : IsInv s) {δ : L}
    (hδ : IsDelta s δ) {h : V → V → L} (hh : IsHerm s h) {x y : V} {N : L} (hN0 : N ≠ 0)
    (hN1 : ‖N‖ < 1) (hNs : s N = N) (hqx : ‖h x x‖ ≤ ‖N‖) (hqy : ‖h y y‖ ≤ 1) (hxy : h x y = δ) :
    ∃ a : L, ‖a‖ ≤ ‖N‖ ∧ h (x + a • y) (x + a • y) = 0 := by
  obtain ⟨hinv, hnorm, -⟩ := id hs
  obtain ⟨-, -, c0, hc0, hc⟩ := hδ
  have hfx : s (h x x) = h x x := (hh.2.2.1 x x).symm
  have hfy : s (h y y) = h y y := (hh.2.2.1 y y).symm
  have hc' : c0 * δ + s c0 * s δ = 1 := by simpa [map_mul] using hc
  have hNpos : 0 < ‖N‖ := norm_pos_iff.2 hN0
  obtain ⟨u, hu, hu1, huq⟩ := hH L s hs (N * (c0 * s c0 * h y y)) (h x x / N)
    (by simp only [map_mul, hNs, hinv, hfy]; ring)
    (by rw [map_div₀, hfx, hNs])
    (by
      rw [norm_mul, norm_mul, norm_mul, hnorm]
      have : ‖c0‖ * ‖c0‖ * ‖h y y‖ ≤ 1 :=
        mul_le_one₀ (mul_le_one₀ hc0 (norm_nonneg _) hc0) (norm_nonneg _) hqy
      calc ‖N‖ * (‖c0‖ * ‖c0‖ * ‖h y y‖) ≤ ‖N‖ * 1 := by gcongr
        _ < 1 := by simpa using hN1)
    (by rw [norm_div]; exact div_le_one_of_le₀ hqx hNpos.le)
  have hd : h x x = N * (h x x / N) := by field_simp
  refine ⟨N * c0 * u, ?_, ?_⟩
  · rw [norm_mul, norm_mul]
    calc ‖N‖ * ‖c0‖ * ‖u‖ ≤ ‖N‖ * 1 * 1 := by gcongr
      _ = ‖N‖ := by ring
  · have hexp := herm_expand hh (N * c0 * u) 1 x y
    rw [one_smul] at hexp
    rw [hexp, hxy, hh.2.2.1 x y, hxy]
    simp only [map_one, map_mul, hNs, hu, one_mul]
    linear_combination hd + N * huq + N * u * hc'

theorem hyperbolic_partner {s : L →+* L} (hs : IsInv s) {δ : L} (hδ : IsDelta s δ) {h : V → V → L}
    (hh : IsHerm s h) {e y : V} (he : h e e = 0) (hqy : ‖h y y‖ ≤ 1) (hey : ‖h e y‖ = ‖δ‖) :
    ∃ b t : L, ‖b‖ = 1 ∧ ‖t‖ ≤ 1 ∧ h (b • y + t • e) (b • y + t • e) = 0 ∧
      h e (b • y + t • e) = δ := by
  obtain ⟨hinv, hnorm, -⟩ := id hs
  obtain ⟨hδ0, -, c0, hc0, hc⟩ := hδ
  have hc' : c0 * δ + s c0 * s δ = 1 := by simpa [map_mul] using hc
  have hw0 : h e y ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hey
    exact hδ0 (norm_eq_zero.1 hey.symm)
  have hb : ‖δ / h e y‖ = 1 := by
    rw [norm_div, hey]
    exact div_self (norm_ne_zero_iff.2 hδ0)
  set b : L := δ / h e y with hbdef
  set y' : V := b • y with hy'
  have hfix : s (h y' y') = h y' y' := (hh.2.2.1 y' y').symm
  have hq' : ‖h y' y'‖ ≤ 1 := by
    rw [hy', herm_smul_left hh, hh.2.1, norm_mul, norm_mul, hnorm, hb]
    simpa using hqy
  have hey' : h e y' = δ := by
    rw [hy', hh.2.1, hbdef]
    field_simp
  have hy'e : h y' e = s δ := by rw [hh.2.2.1 e y', hey']
  refine ⟨b, -(h y' y' * s c0), hb, ?_, ?_, ?_⟩
  · rw [norm_neg, norm_mul, hnorm]
    exact mul_le_one₀ hq' (norm_nonneg _) hc0
  · have hexp := herm_expand hh (-(h y' y' * s c0)) 1 y' e
    rw [one_smul] at hexp
    rw [← hy', hexp, hey', hy'e, he]
    simp only [map_one, map_mul, map_neg, hfix, hinv, one_mul]
    linear_combination (-(h y' y')) * hc'
  · rw [← hy', hh.1, hey', hh.2.1, he]
    simp

end Form

section Pair

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L] [CharZero L]
  {V : Type} [AddCommGroup V] [Module L V] [FiniteDimensional L V]

theorem exists_pair (hH : StHensel) (hP : StPairing) {s : L →+* L} (hs : IsInv s) {δ : L}
    (hδ : IsDelta s δ) {h : V → V → L} (hh : IsHerm s h) (hiso : ∃ x, x ≠ 0 ∧ h x x = 0)
    {Λ M : AddSubgroup V} (hΛ : IsMax h Λ) (hM : IsMax h M) {p : L} (hp0 : p ≠ 0) (hp1 : ‖p‖ < 1)
    (hpm : ∀ a : L, ‖a‖ < 1 → ‖a‖ ≤ ‖p‖) {r : ℕ} (hr : ∀ x ∈ M, p ^ r • x ∈ Λ)
    (hmin : ∀ k < r, ∃ z ∈ M, p ^ k • z ∉ Λ) (hrM : ∀ y ∈ Λ, p ^ r • y ∈ M) :
    ∃ e y : V, e ∈ Λ ∧ y ∈ Λ ∧ h e e = 0 ∧ ‖h e y‖ = ‖δ‖ ∧ (p ^ r)⁻¹ • e ∈ M := by
  obtain ⟨-, hpair⟩ := hP L s hs δ hδ V h hh Λ hΛ
  obtain ⟨hinv, hnorm, -⟩ := id hs
  rcases r with _ | n
  · obtain ⟨v, hv, hq⟩ := hiso
    obtain ⟨a, ha0, haΛ, hprim⟩ := lat_primitive hΛ.1 hp0 hp1 hv
    have hqa : h (a • v) (a • v) = 0 := by rw [herm_smul_left hh, hh.2.1, hq]; simp
    obtain ⟨y, hy, hxy⟩ := hpair p hp1 hpm (a • v) haΛ hprim (by rw [hqa, norm_zero]; positivity)
    refine ⟨a • v, y, haΛ, hy, hqa, by rw [hxy], ?_⟩
    simpa using hrM _ haΛ
  · obtain ⟨z, hz, hzΛ⟩ := hmin n (Nat.lt_succ_self n)
    have hP0 : p ^ (n + 1) ≠ 0 := pow_ne_zero _ hp0
    have hPle : ‖p ^ (n + 1)‖ ≤ ‖p‖ := by
      rw [norm_pow, pow_succ]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hp1.le)
    have hP1 : ‖p ^ (n + 1)‖ < 1 := hPle.trans_lt hp1
    generalize hPdef : p ^ (n + 1) = P at *
    have hPpos : 0 < ‖P‖ := norm_pos_iff.2 hP0
    have hxΛ : P • z ∈ Λ := hr z hz
    have hprim : p⁻¹ • P • z ∉ Λ := by
      intro hcon
      apply hzΛ
      have hpn : p⁻¹ * P = p ^ n := by
        rw [← hPdef, pow_succ']
        field_simp
      rwa [smul_smul, hpn] at hcon
    have hqz := hM.2.1 z hz
    have hnx : ‖h (P • z) (P • z)‖ ≤ ‖P‖ * ‖P‖ := by
      rw [herm_smul_left hh, hh.2.1, norm_mul, norm_mul, hnorm]
      calc ‖P‖ * (‖P‖ * ‖h z z‖) ≤ ‖P‖ * (‖P‖ * 1) := by gcongr
        _ = ‖P‖ * ‖P‖ := by ring
    obtain ⟨y, hy, hxy⟩ := hpair p hp1 hpm (P • z) hxΛ hprim (by
      refine hnx.trans ?_
      rw [pow_two]
      exact mul_le_mul hPle hPle (norm_nonneg _) (norm_nonneg _))
    have hN : ‖P * s P‖ = ‖P‖ * ‖P‖ := by rw [norm_mul, hnorm]
    have hN1 : ‖P * s P‖ < 1 := by
      rw [hN]
      exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hP1 hP1.le
    have hqy := hΛ.2.1 y hy
    obtain ⟨a, ha, haq⟩ := isotropic_lift hH hs hδ hh
      (mul_ne_zero hP0 ((map_ne_zero s).2 hP0)) hN1
      (by rw [map_mul, hinv, mul_comm]) (by rw [hN]; exact hnx) hqy hxy
    have ha1 : ‖a‖ ≤ 1 := ha.trans hN1.le
    have haN : ‖a‖ < 1 := ha.trans_lt hN1
    refine ⟨P • z + a • y, y, add_mem hxΛ (lat_smul hΛ.1 ha1 hy), hy, haq, ?_, ?_⟩
    · rw [herm_add_left hh, hxy, herm_smul_left hh]
      have h1 := one_le_norm_delta hs hδ
      have h2 : ‖s a * h y y‖ < ‖δ‖ := by
        rw [norm_mul, hnorm]
        calc ‖a‖ * ‖h y y‖ ≤ ‖a‖ * 1 := by gcongr
          _ < 1 := by simpa using haN
          _ ≤ ‖δ‖ := h1
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h2.ne']
      exact max_eq_left h2.le
    · have heq : P⁻¹ • (P • z + a • y) = z + (P⁻¹ * a * P⁻¹) • (P • y) := by
        rw [smul_add, smul_smul, smul_smul, smul_smul (P⁻¹ * a * P⁻¹), inv_mul_cancel₀ hP0, one_smul,
          mul_assoc (P⁻¹ * a), inv_mul_cancel₀ hP0, mul_one]
      rw [heq]
      refine add_mem hz (lat_smul hM.1 ?_ (hrM y hy))
      rw [norm_mul, norm_mul, norm_inv]
      have : ‖a‖ ≤ ‖P‖ * ‖P‖ := hN ▸ ha
      field_simp
      rw [pow_two]
      exact this

theorem plane_of_pair {s : L →+* L} (hs : IsInv s) {δ : L} (hδ : IsDelta s δ) {h : V → V → L}
    (hh : IsHerm s h) {Λ M : AddSubgroup V} (hΛ : IsMax h Λ) (hM : IsMax h M) {p : L} (hp0 : p ≠ 0)
    (hp1 : ‖p‖ < 1) {r : ℕ} (hrM : ∀ y ∈ Λ, p ^ r • y ∈ M) {e y : V} (heΛ : e ∈ Λ) (hyΛ : y ∈ Λ)
    (he : h e e = 0) (hey : ‖h e y‖ = ‖δ‖) (heM : (p ^ r)⁻¹ • e ∈ M) :
    ∃ (e f : V) (u : L), u ≠ 0 ∧ h e e = 0 ∧ h f f = 0 ∧ h e f = δ ∧
      e ∈ Λ ∧ f ∈ Λ ∧ u • e ∈ M ∧ (s u)⁻¹ • f ∈ M := by
  obtain ⟨b, t, hb, ht, hf, hef⟩ := hyperbolic_partner hs hδ hh he (hΛ.2.1 y hyΛ) hey
  have hP0 : p ^ r ≠ 0 := pow_ne_zero _ hp0
  have hP1 : ‖p ^ r‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hp1.le
  have hPpos : 0 < ‖p ^ r‖ := norm_pos_iff.2 hP0
  have hyM := hrM y hyΛ
  generalize p ^ r = P at *
  refine ⟨e, b • y + t • e, P⁻¹, inv_ne_zero hP0, he, hf, hef, heΛ,
    add_mem (lat_smul hΛ.1 hb.le hyΛ) (lat_smul hΛ.1 ht heΛ), heM, ?_⟩
  rw [map_inv₀, inv_inv, smul_add]
  have hsP : ‖s P‖ = ‖P‖ := hs.2.1 P
  have h1 : s P • b • y = (s P * b * P⁻¹) • P • y := by
    rw [smul_smul, smul_smul, mul_assoc (s P * b), inv_mul_cancel₀ hP0, mul_one]
  have h2 : s P • t • e = (s P * t * P) • P⁻¹ • e := by
    rw [smul_smul, smul_smul, mul_assoc (s P * t), mul_inv_cancel₀ hP0, mul_one]
  rw [h1, h2]
  refine add_mem (lat_smul hM.1 ?_ hyM) (lat_smul hM.1 ?_ heM)
  · rw [norm_mul, norm_mul, norm_inv, hsP, hb, mul_one, mul_inv_cancel₀ hPpos.ne']
  · rw [norm_mul, norm_mul, hsP]
    exact mul_le_one₀ (mul_le_one₀ hP1 (norm_nonneg _) ht) (norm_nonneg _) hP1

end Pair

theorem stPlane_of_hensel_pairing : StHensel → StPairing → StPlane := by
  intro hH hP L _ _ _ _ s hs δ hδ V _ _ _ h hh hiso Λ M hΛ hM
  obtain ⟨p, hp0, hp1, hpm⟩ := exists_uniformiser (L := L)
  have key : ∀ Λ M : AddSubgroup V, IsMax h Λ → IsMax h M → ∀ r : ℕ, (∀ x ∈ M, p ^ r • x ∈ Λ) →
      (∀ k < r, ∃ z ∈ M, p ^ k • z ∉ Λ) → (∀ y ∈ Λ, p ^ r • y ∈ M) →
      ∃ (e f : V) (u : L), u ≠ 0 ∧ h e e = 0 ∧ h f f = 0 ∧ h e f = δ ∧
        e ∈ Λ ∧ f ∈ Λ ∧ u • e ∈ M ∧ (s u)⁻¹ • f ∈ M := by
    intro Λ M hΛ hM r hr hmin hrM
    obtain ⟨e, y, heΛ, hyΛ, he, hey, heM⟩ :=
      exists_pair hH hP hs hδ hh hiso hΛ hM hp0 hp1 hpm hr hmin hrM
    exact plane_of_pair hs hδ hh hΛ hM hp0 hp1 hrM heΛ hyΛ he hey heM
  classical
  have c1 := lat_commens hΛ.1 hM.1 hp0 hp1
  have c2 := lat_commens hM.1 hΛ.1 hp0 hp1
  have hmin1 : ∀ k < Nat.find c1, ∃ z ∈ M, p ^ k • z ∉ Λ := fun k hk => by
    have := Nat.find_min c1 hk
    push_neg at this
    exact this
  have hmin2 : ∀ k < Nat.find c2, ∃ z ∈ Λ, p ^ k • z ∉ M := fun k hk => by
    have := Nat.find_min c2 hk
    push_neg at this
    exact this
  have up : ∀ (A : AddSubgroup V), IsLat L A → ∀ (B : AddSubgroup V) {a b : ℕ}, a ≤ b →
      (∀ y ∈ B, p ^ a • y ∈ A) → ∀ y ∈ B, p ^ b • y ∈ A := by
    intro A hA B a b hab hy y hyB
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [pow_add, mul_comm, mul_smul]
    refine lat_smul hA ?_ (hy y hyB)
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hp1.le
  rcases le_total (Nat.find c2) (Nat.find c1) with hle | hle
  · exact key Λ M hΛ hM _ (Nat.find_spec c1) hmin1 (up M hM.1 Λ hle (Nat.find_spec c2))
  · obtain ⟨e, f, u, hu, he, hf, hef, heM, hfM, heΛ, hfΛ⟩ :=
      key M Λ hM hΛ _ (Nat.find_spec c2) hmin2 (up Λ hΛ.1 M hle (Nat.find_spec c1))
    have hsu : s u ≠ 0 := (map_ne_zero s).2 hu
    refine ⟨u • e, (s u)⁻¹ • f, u⁻¹, inv_ne_zero hu, ?_, ?_, ?_, heΛ, hfΛ, ?_, ?_⟩
    · rw [herm_smul_left hh, hh.2.1, he]; simp
    · rw [herm_smul_left hh, hh.2.1, hf]; simp
    · rw [herm_smul_left hh, hh.2.1, hef, ← mul_assoc, mul_inv_cancel₀ hsu, one_mul]
    · rwa [smul_smul, inv_mul_cancel₀ hu, one_smul]
    · rwa [map_inv₀, inv_inv, smul_smul, mul_inv_cancel₀ hsu, one_smul]

end GlobalTheory.CompanionTheory.HermPlane

end
