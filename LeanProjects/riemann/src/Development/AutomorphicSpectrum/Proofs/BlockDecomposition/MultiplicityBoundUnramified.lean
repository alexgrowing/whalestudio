import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardHermitianMatricesModPow

open PositivityTheory.PfSWUS.Loc

namespace GlobalTheory.CompanionTheory.GunrNuBound

variable {R : Type} [CommRing R]

theorem not_mem_lev_one {ϖ a : R} (h : ¬ ϖ ∣ a) : a ∉ lev ϖ 1 := by
  intro hm
  exact h (by simpa using Ideal.mem_span_singleton.1 hm)

theorem exists_trace_not_dvd {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (h : IsUnrQuad R σ ϖ q ε) {c : R}
    (hc : ¬ ϖ ∣ c) : ∃ t : R, ¬ ϖ ∣ (t * c + σ (t * c)) := by
  by_contra hall
  push_neg at hall
  obtain ⟨u, ⟨d, hd⟩, -⟩ := h.basis
  have h1 : ϖ ∣ 1 * c + σ (1 * c) := hall 1
  have h2 : ϖ ∣ u * c + σ (u * c) := hall u
  have h3 : ϖ ∣ (d : R) * σ c := by
    have e : (d : R) * σ c = u * (1 * c + σ (1 * c)) - (u * c + σ (u * c)) := by
      rw [hd, map_mul, map_mul, map_one]; ring
    rw [e]
    exact dvd_sub (Dvd.dvd.mul_left h1 u) h2
  have h4 : ϖ ∣ σ c := (Units.dvd_mul_left).1 h3
  have h5 : σ ϖ ∣ σ (σ c) := map_dvd σ h4
  rw [h.fix_ϖ, h.inv] at h5
  exact hc h5

def bf (σ : R →+* R) {n : ℕ} (H : Matrix (Fin n) (Fin n) R) (w z : Fin n → R) : R :=
  ∑ i, ∑ l, w i * H i l * σ (z l)

theorem bf_add_left (σ : R →+* R) {n : ℕ} (H : Matrix (Fin n) (Fin n) R) (w w' z : Fin n → R) :
    bf σ H (w + w') z = bf σ H w z + bf σ H w' z := by
  simp [bf, add_mul, Finset.sum_add_distrib]

theorem bf_add_right (σ : R →+* R) {n : ℕ} (H : Matrix (Fin n) (Fin n) R) (w z z' : Fin n → R) :
    bf σ H w (z + z') = bf σ H w z + bf σ H w z' := by
  simp [bf, mul_add, Finset.sum_add_distrib]

theorem bf_single (σ : R →+* R) {n : ℕ} (H : Matrix (Fin n) (Fin n) R) (a b : Fin n) (s t : R) :
    bf σ H (Pi.single a s) (Pi.single b t) = s * H a b * σ t := by
  unfold bf
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro l _ hl; simp [Pi.single_eq_of_ne hl]
  · simp
  · intro i _ hi; simp [Pi.single_eq_of_ne hi]
  · simp

theorem bf_swap {σ : R →+* R} (hinv : ∀ a, σ (σ a) = a) {n : ℕ} {H : Matrix (Fin n) (Fin n) R}
    (hH : cT σ H = H) (w z : Fin n → R) : σ (bf σ H w z) = bf σ H z w := by
  have hab : ∀ a b, σ (H b a) = H a b := fun a b => by
    have := congrFun (congrFun hH a) b
    simpa [cT] using this
  unfold bf
  rw [map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, hinv, hab]
  ring

theorem exists_form_unit {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (h : IsUnrQuad R σ ϖ q ε) {n : ℕ}
    {H : Matrix (Fin n) (Fin n) R} (hH : cT σ H = H) (hnd : ¬ ∀ a b, ϖ ∣ H a b) :
    ∃ w : Fin n → R, IsUnit (bf σ H w w) := by
  have key : ∀ w : Fin n → R, ¬ ϖ ∣ bf σ H w w → IsUnit (bf σ H w w) := fun w hw =>
    h.fixLocal _ (bf_swap h.inv hH w w) (not_mem_lev_one hw)
  by_cases hd : ∃ a, ¬ ϖ ∣ H a a
  · obtain ⟨a, ha⟩ := hd
    refine ⟨Pi.single a 1, key _ ?_⟩
    simpa [bf_single] using ha
  · push_neg at hd hnd
    obtain ⟨a, b, hab⟩ := hnd
    obtain ⟨t, ht⟩ := exists_trace_not_dvd h hab
    refine ⟨Pi.single a t + Pi.single b 1, key _ ?_⟩
    intro hdiv
    apply ht
    have e : bf σ H (Pi.single a t + Pi.single b 1) (Pi.single a t + Pi.single b 1) =
        t * H a a * σ t + t * H a b + σ (t * H a b) + H b b := by
      have e2 : bf σ H (Pi.single b 1) (Pi.single a t) = σ (t * H a b) := by
        rw [← bf_swap h.inv hH, bf_single, map_one, mul_one]
      rw [bf_add_left, bf_add_right, bf_add_right, e2, bf_single, bf_single, bf_single]
      simp only [map_one, mul_one, one_mul]
      ring
    rw [e] at hdiv
    have e3 : t * H a b + σ (t * H a b) =
        (t * H a a * σ t + t * H a b + σ (t * H a b) + H b b) - (t * H a a * σ t + H b b) := by ring
    rw [e3]
    exact dvd_sub hdiv (dvd_add (Dvd.dvd.mul_right (Dvd.dvd.mul_left (hd a) t) _) (hd b))

theorem vecMul_red (ϖ : R) (k : ℕ) {n : ℕ} (x : Fin n → R) (H : Matrix (Fin n) (Fin n) R) :
    Matrix.vecMul (fun i => Ideal.Quotient.mk (lev ϖ k) (x i)) (red ϖ k H) =
      fun l => Ideal.Quotient.mk (lev ϖ k) (∑ i, x i * H i l) := by
  funext l
  simp [Matrix.vecMul, dotProduct, red, map_sum]

theorem nu_lower {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (h : IsUnrQuad R σ ϖ q ε) {n j k : ℕ}
    (hjk : j ≤ k) {H : Matrix (Fin n) (Fin n) R} (hH : cT σ H = H) (hnd : ¬ ∀ a b, ϖ ∣ H a b) :
    q ^ (2 * j) ≤ nuAt ϖ (red ϖ k (ϖ ^ (k - j) • H)) := by
  obtain ⟨w, hw⟩ := exists_form_unit h hH hnd
  have hq : 0 < q := lt_trans Nat.zero_lt_one h.one_lt
  have hfin : Finite (R ⧸ lev ϖ k) :=
    Nat.finite_of_card_ne_zero (by rw [GlobalTheory.T.unramified_quotient_card R σ ϖ q ε h k]; exact (pow_pos hq _).ne')
  set B := red ϖ k (ϖ ^ (k - j) • H) with hB
  let lift : R ⧸ lev ϖ j → R := Function.surjInv Ideal.Quotient.mk_surjective
  have hlift : ∀ c, Ideal.Quotient.mk (lev ϖ j) (lift c) = c := Function.surjInv_eq _
  let f : R ⧸ lev ϖ j → Set.range (fun x : Fin n → R ⧸ lev ϖ k => Matrix.vecMul x B) :=
    fun c => ⟨_, (fun i => Ideal.Quotient.mk (lev ϖ k) (lift c * w i)), rfl⟩
  have hinj : Function.Injective f := by
    intro c₁ c₂ hc
    have hv := congrArg Subtype.val hc
    simp only [f] at hv
    rw [hB, vecMul_red, vecMul_red] at hv
    have hl : ∀ l, ϖ ^ k ∣ ∑ i, (lift c₁ - lift c₂) * w i * (ϖ ^ (k - j) * H i l) := by
      intro l
      have := congrFun hv l
      have h2 := Ideal.Quotient.eq.1 this
      have h3 := Ideal.mem_span_singleton.1 h2
      convert h3 using 1
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Matrix.smul_apply, smul_eq_mul]
      ring
    have hs : ϖ ^ k ∣ ϖ ^ (k - j) * ((lift c₁ - lift c₂) * bf σ H w w) := by
      have e : ϖ ^ (k - j) * ((lift c₁ - lift c₂) * bf σ H w w) =
          ∑ l, (∑ i, (lift c₁ - lift c₂) * w i * (ϖ ^ (k - j) * H i l)) * σ (w l) := by
        unfold bf
        rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [e]
      exact Finset.dvd_sum fun l _ => Dvd.dvd.mul_right (hl l) _
    obtain ⟨e, he⟩ := hs
    have hk : ϖ ^ k = ϖ ^ (k - j) * ϖ ^ j := by rw [← pow_add, Nat.sub_add_cancel hjk]
    have hreg : IsSMulRegular R (ϖ ^ (k - j)) := h.reg.pow _
    have h5 : (lift c₁ - lift c₂) * bf σ H w w = ϖ ^ j * e := by
      apply hreg
      simp only [smul_eq_mul]
      rw [he, hk]; ring
    have h6 : ϖ ^ j ∣ lift c₁ - lift c₂ :=
      (hw.dvd_mul_right).1 ⟨e, h5⟩
    rw [← hlift c₁, ← hlift c₂]
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 h6)
  have := Nat.card_le_card_of_injective f hinj
  rwa [GlobalTheory.T.unramified_quotient_card R σ ϖ q ε h j] at this

def lvl (σ : R →+* R) (ϖ : R) (n k j : ℕ) : Set (Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) :=
  {B | ∃ H : Matrix (Fin n) (Fin n) R, cT σ H = H ∧ B = red ϖ k (ϖ ^ (k - j) • H)}

theorem card_lvl_le {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (h : IsUnrQuad R σ ϖ q ε) {n j k : ℕ}
    (hjk : j ≤ k) (S : Finset (hermMod σ ϖ n k)) (hS : ∀ B ∈ S, B.1 ∈ lvl σ ϖ n k j) :
    S.card ≤ q ^ (j * n ^ 2) := by
  classical
  have hq : 0 < q := lt_trans Nat.zero_lt_one h.one_lt
  have hcard := GlobalTheory.CompanionTheory.UnrDens.card_hermMod R σ ϖ q ε h n j
  have hfin : Finite (hermMod σ ϖ n j) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact (pow_pos hq _).ne')
  have hS' : ∀ B ∈ S, ∃ H : Matrix (Fin n) (Fin n) R,
      cT σ H = H ∧ B.1 = red ϖ k (ϖ ^ (k - j) • H) := hS
  choose! H hH using hS'
  let f : S → hermMod σ ϖ n j := fun B => ⟨red ϖ j (H B.1), H B.1, (hH B.1 B.2).1, rfl⟩
  have hinj : Function.Injective f := by
    intro B₁ B₂ hf
    have hv : red ϖ j (H B₁.1) = red ϖ j (H B₂.1) := congrArg Subtype.val hf
    apply Subtype.ext
    apply Subtype.ext
    rw [(hH B₁.1 B₁.2).2, (hH B₂.1 B₂.2).2]
    ext a b
    have h1 := congrFun (congrFun hv a) b
    simp only [red, Matrix.map_apply] at h1
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h1)
    simp only [red, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    refine Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 ⟨e, ?_⟩)
    have hk : ϖ ^ k = ϖ ^ (k - j) * ϖ ^ j := by rw [← pow_add, Nat.sub_add_cancel hjk]
    rw [hk, ← mul_sub, he]
    ring
  have := Nat.card_le_card_of_injective f hinj
  rw [hcard] at this
  simpa [Nat.card_eq_fintype_card] using this

theorem not_dvd_of_not_lvl {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (h : IsUnrQuad R σ ϖ q ε) {n j k : ℕ}
    (hj : 0 < j) (hjk : j ≤ k) {H : Matrix (Fin n) (Fin n) R} (hH : cT σ H = H)
    {B : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)} (hB : B = red ϖ k (ϖ ^ (k - j) • H))
    (hn : B ∉ lvl σ ϖ n k (j - 1)) : ¬ ∀ a b, ϖ ∣ H a b := by
  intro hd
  choose H' hH' using hd
  apply hn
  have hab : ∀ a b, σ (H b a) = H a b := fun a b => by
    have := congrFun (congrFun hH a) b
    simpa [cT] using this
  refine ⟨Matrix.of H', ?_, ?_⟩
  · ext a b
    show σ (H' b a) = H' a b
    apply h.reg
    simp only [smul_eq_mul]
    have e := hab a b
    rw [hH' b a, map_mul, h.fix_ϖ, hH' a b] at e
    exact e
  · rw [hB]
    congr 1
    ext a b
    have e : k - (j - 1) = (k - j) + 1 := by omega
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    rw [hH' a b, e, pow_succ]
    ring

end GlobalTheory.CompanionTheory.GunrNuBound

open GlobalTheory.CompanionTheory.GunrNuBound in

theorem GlobalTheory.CompanionTheory.GunrNuBound.nuBound : PositivityTheory.SiegelWeilFormula.Gunr.NuBound := by
  classical
  intro R _ σ ϖ q ε h n k r hr hx
  have hq : 0 < q := lt_trans Nat.zero_lt_one h.one_lt
  have hfin : Finite (hermMod σ ϖ n k) :=
    Nat.finite_of_card_ne_zero
      (by rw [GlobalTheory.CompanionTheory.UnrDens.card_hermMod R σ ϖ q ε h n k]; exact (pow_pos hq _).ne')
  haveI := Fintype.ofFinite (hermMod σ ϖ n k)
  rw [tsum_fintype]
  have hq1 : (1 : ℝ) ≤ (q : ℝ) ^ (n ^ 2) := one_le_pow₀ (by exact_mod_cast hq)
  have hr1 : r ≤ 1 := by nlinarith
  have hx0 : 0 ≤ (q : ℝ) ^ (n ^ 2) * r := by positivity
  have hex : ∀ B : hermMod σ ϖ n k, ∃ j, j ≤ k ∧ B.1 ∈ lvl σ ϖ n k j := by
    rintro ⟨_, H, hH, rfl⟩
    exact ⟨k, le_rfl, H, hH, by simp⟩
  let lv : hermMod σ ϖ n k → ℕ := fun B => Nat.find (hex B)
  have hlv_le : ∀ B, lv B ≤ k := fun B => (Nat.find_spec (hex B)).1
  have hlv_mem : ∀ B, B.1 ∈ lvl σ ϖ n k (lv B) := fun B => (Nat.find_spec (hex B)).2
  have hlog : ∀ B : hermMod σ ϖ n k, lv B ≤ Nat.log (q ^ 2) (nuAt ϖ B.1) := by
    intro B
    rcases Nat.eq_zero_or_pos (lv B) with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · obtain ⟨H, hH, hB⟩ := hlv_mem B
      have hn : B.1 ∉ lvl σ ϖ n k (lv B - 1) := fun hmem =>
        Nat.find_min (hex B) (Nat.sub_lt hpos one_pos) ⟨(Nat.sub_le _ _).trans (hlv_le B), hmem⟩
      have hnd := not_dvd_of_not_lvl h hpos (hlv_le B) hH hB hn
      have hlow := nu_lower h (hlv_le B) hH hnd
      rw [← hB] at hlow
      refine Nat.le_log_of_pow_le (Nat.one_lt_pow two_ne_zero h.one_lt) ?_
      rwa [← pow_mul]
  calc ∑ B : hermMod σ ϖ n k, r ^ Nat.log (q ^ 2) (nuAt ϖ B.1)
      ≤ ∑ B : hermMod σ ϖ n k, r ^ lv B :=
        Finset.sum_le_sum fun B _ => pow_le_pow_of_le_one hr hr1 (hlog B)
    _ = ∑ j ∈ Finset.range (k + 1), ∑ B ∈ Finset.univ.filter (fun B => lv B = j), r ^ lv B :=
        (Finset.sum_fiberwise_of_maps_to
          (fun B _ => Finset.mem_range.2 (Nat.lt_succ_of_le (hlv_le B))) _).symm
    _ ≤ ∑ j ∈ Finset.range (k + 1), ((q : ℝ) ^ (n ^ 2) * r) ^ j := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        have hc := card_lvl_le h hjk (Finset.univ.filter fun B => lv B = j) (by
          intro B hB
          have := (Finset.mem_filter.1 hB).2
          rw [← this]
          exact hlv_mem B)
        have e : ∑ B ∈ Finset.univ.filter (fun B => lv B = j), r ^ lv B =
            ((Finset.univ.filter fun B => lv B = j).card : ℝ) * r ^ j := by
          rw [Finset.sum_congr rfl (g := fun _ => r ^ j)
            (fun B hB => by rw [(Finset.mem_filter.1 hB).2]), Finset.sum_const, nsmul_eq_mul]
        rw [e, mul_pow, ← pow_mul, mul_comm (n ^ 2) j]
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hr _)
        exact_mod_cast hc
    _ ≤ ∑' j : ℕ, ((q : ℝ) ^ (n ^ 2) * r) ^ j :=
        (summable_geometric_of_lt_one hx0 hx).sum_le_tsum _ (fun _ _ => pow_nonneg hx0 _)
    _ = 1 / (1 - (q : ℝ) ^ (n ^ 2) * r) := by
        rw [tsum_geometric_of_lt_one hx0 hx, one_div]
