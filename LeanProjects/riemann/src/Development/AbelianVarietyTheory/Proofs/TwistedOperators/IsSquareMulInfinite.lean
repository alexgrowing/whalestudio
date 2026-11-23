import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
import Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticExtNormFormOverAlgebra
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitNormFormAtOddPlace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitMulSqQuadraticDefectStep
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGlobalUniformizerResidueRepresentatives
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSubSqLtOneOfTwoLtOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareMulOfNonsquareUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareOfValuedSubOneLt

open NumberField IsDedekindDomain IsLocalRing
open scoped WithZero

namespace GlobalTheory.QuadSymbol

namespace NormIndex

section Field

variable {K : Type} [Field K]

def Nm (d x : K) : Prop := ∃ a b : K, x = a ^ 2 - d * b ^ 2

theorem Nm.mul {d x y : K} (hx : Nm d x) (hy : Nm d y) : Nm d (x * y) := by
  obtain ⟨a, b, rfl⟩ := hx
  obtain ⟨c, e, rfl⟩ := hy
  exact ⟨a * c + d * b * e, a * e + b * c, by ring⟩

theorem Nm.sq (d c : K) : Nm d (c ^ 2) := ⟨c, 0, by ring⟩

theorem Nm.of_isSquare (d : K) {x : K} (h : IsSquare x) : Nm d x := by
  obtain ⟨r, rfl⟩ := h
  exact ⟨r, 0, by ring⟩

theorem Nm.of_mul {d x n : K} (hn0 : n ≠ 0) (hn : Nm d n) (h : Nm d (x * n)) : Nm d x := by
  have e : x = x * n * n * (n⁻¹) ^ 2 := by field_simp
  rw [e]
  exact (h.mul hn).mul (Nm.sq d _)

theorem Nm.of_isSquare_left (h2 : (2 : K) ≠ 0) {d : K} (hd : d ≠ 0) (h : IsSquare d) (x : K) :
    Nm d x := by
  obtain ⟨r, rfl⟩ := h
  have hr : r ≠ 0 := fun h => hd (by rw [h, mul_zero])
  exact ⟨(x + 1) / 2, (x - 1) / (2 * r), by field_simp; ring⟩

theorem Nm.symm (h2 : (2 : K) ≠ 0) {d x : K} (hx : x ≠ 0) (h : Nm d x) : Nm x d := by
  obtain ⟨a, b, h⟩ := h
  by_cases hb : b = 0
  · exact Nm.of_isSquare_left h2 hx ⟨a, by rw [h, hb]; ring⟩ d
  · exact ⟨a / b, 1 / b, by rw [h]; field_simp; ring⟩

variable (w : Valuation K ℤᵐ⁰)

theorem even_or_odd {x : K} (hx : x ≠ 0) :
    (∃ n : ℤ, w x = WithZero.exp (2 * n)) ∨ ∃ n : ℤ, w x = WithZero.exp (2 * n + 1) := by
  have h := (WithZero.exp_log ((Valuation.ne_zero_iff w).2 hx)).symm
  rcases Int.even_or_odd' (WithZero.log (w x)) with ⟨k, hk | hk⟩
  · exact Or.inl ⟨k, by rw [h, hk]⟩
  · exact Or.inr ⟨k, by rw [h, hk]⟩

theorem ne_zero_of_exp {x : K} {n : ℤ} (h : w x = WithZero.exp n) : x ≠ 0 := by
  rintro rfl
  rw [map_zero] at h
  exact WithZero.exp_ne_zero h.symm

theorem ne_zero_of_one {x : K} (h : w x = 1) : x ≠ 0 := ne_zero_of_exp w (n := 0) h

theorem val_mul_zpow_sq {x π : K} (hπ : w π = WithZero.exp (-1)) {n : ℤ}
    (h : w x = WithZero.exp n) (k : ℤ) : w (x * (π ^ k) ^ 2) = WithZero.exp (n - 2 * k) := by
  rw [map_mul, map_pow, map_zpow₀, hπ, h, ← WithZero.exp_zsmul, ← WithZero.exp_nsmul,
    ← WithZero.exp_add]
  congr 1
  simp; ring

theorem core (h2 : (2 : K) ≠ 0) {π Δ d : K} (hπ : w π = WithZero.exp (-1)) (hΔ : Δ ≠ 0)
    (hd : d ≠ 0) (hA : ∀ (x : K) (n : ℤ), w x = WithZero.exp (2 * n) → Nm Δ x)
    (hB : ∀ (z : K) (n : ℤ), w z = WithZero.exp (2 * n + 1) → Nm z d ∨ Nm z (d * Δ))
    {x y : K} (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hx : ¬ Nm d x) (hy : ¬ Nm d y) : Nm d (x * y) := by
  have K1 : ∀ (z : K) (n : ℤ), w z = WithZero.exp (2 * n + 1) → ¬ Nm d z → Nm (d * Δ) z :=
    fun z n hz hn => ((hB z n hz).resolve_left fun h => hn (h.symm h2 hd)).symm h2
      (mul_ne_zero hd hΔ)
  have K2 : ∀ (z z' : K) (n n' : ℤ), w z = WithZero.exp (2 * n + 1) →
      w z' = WithZero.exp (2 * n' + 1) → ¬ Nm d z → ¬ Nm d z' → Nm d (z * z') := by
    intro z z' n n' hz hz' h h'
    have hzz : w (z * z') = WithZero.exp (2 * (n + n' + 1)) := by
      rw [map_mul, hz, hz', ← WithZero.exp_add]; congr 1; ring
    have h0 := ne_zero_of_exp w hzz
    have h1 := ((K1 z n hz h).mul (K1 z' n' hz' h')).symm h2 h0
    exact (Nm.of_mul hΔ ((hA _ _ hzz).symm h2 h0) h1).symm h2 hd
  by_cases ht : ∃ (t : K) (j : ℤ), w t = WithZero.exp (2 * j + 1) ∧ Nm d t
  · obtain ⟨t, j, ht, htn⟩ := ht
    have H : ∀ z : K, z ≠ 0 → ∃ (m : K) (n : ℤ), m ≠ 0 ∧ Nm d m ∧
        w (z * m) = WithZero.exp (2 * n + 1) := by
      intro z hz
      rcases even_or_odd w hz with ⟨n, hn⟩ | ⟨n, hn⟩
      · refine ⟨t, n + j, ne_zero_of_exp w ht, htn, ?_⟩
        rw [map_mul, hn, ht, ← WithZero.exp_add]; congr 1; ring
      · exact ⟨1, n, one_ne_zero, ⟨1, 0, by ring⟩, by rw [mul_one, hn]⟩
    obtain ⟨m, n, hm0, hm, hn⟩ := H x hx0
    obtain ⟨m', n', hm0', hm', hn'⟩ := H y hy0
    have := K2 _ _ n n' hn hn' (fun h => hx (Nm.of_mul hm0 hm h)) (fun h => hy (Nm.of_mul hm0' hm' h))
    refine Nm.of_mul (mul_ne_zero hm0 hm0') (hm.mul hm') ?_
    rwa [show x * y * (m * m') = x * m * (y * m') by ring]
  · push Not at ht
    have hπ' : w π = WithZero.exp (2 * (-1) + 1) := by rw [hπ]; norm_num
    have H : ∀ z : K, z ≠ 0 → ¬ Nm d z → ∃ n : ℤ, w z = WithZero.exp (2 * n + 1) := by
      intro z hz hzn
      rcases even_or_odd w hz with ⟨n, hn⟩ | h
      · have h1 : w (z * π) = WithZero.exp (2 * (n - 1) + 1) := by
          rw [map_mul, hn, hπ, ← WithZero.exp_add]; congr 1; ring
        have := K2 _ _ _ _ h1 hπ' (ht _ _ h1) (ht _ _ hπ')
        refine absurd (Nm.of_mul (pow_ne_zero 2 (ne_zero_of_exp w hπ)) (Nm.sq d π) ?_) hzn
        rwa [show z * π ^ 2 = z * π * π by ring]
      · exact h
    obtain ⟨n, hn⟩ := H x hx0 hx
    obtain ⟨n', hn'⟩ := H y hy0 hy
    exact K2 _ _ n n' hn hn' hx hy

theorem map_two_le : w 2 ≤ 1 := by
  rw [← one_add_one_eq_two]
  exact w.map_add_le (by simp) (by simp)

theorem map_four : w 4 = w 2 * w 2 := by
  rw [← map_mul]; norm_num

theorem step {π : K} (hπ : w π = WithZero.exp (-1))
    (hres : w 2 < 1 → ∀ x : K, w x ≤ 1 → ∃ y : K, w y ≤ 1 ∧ w (x - y ^ 2) < 1)
    {z : K} {j : ℤ} (hz : w z = WithZero.exp (2 * j + 1)) {u : K} (hu : w u = 1)
    (h4 : w 4 < w (u - 1)) : ∃ m : K, w m = 1 ∧ Nm z m ∧ w (u * m - 1) < w (u - 1) := by
  have hle : w (u - 1) ≤ 1 := w.map_sub_le hu.le (by simp)
  have hw2 : w 2 < 1 := by
    refine lt_of_le_of_ne (map_two_le w) fun h1 => ?_
    rw [map_four, h1, one_mul] at h4
    exact absurd hle (not_le.2 h4)
  have hne : u - 1 ≠ 0 := by
    intro h0; rw [h0] at h4; simp at h4
  rcases even_or_odd w hne with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hk0 : 2 * k ≤ 0 := by
      rw [hk, ← WithZero.exp_zero, WithZero.exp_le_exp] at hle; exact hle
    obtain ⟨c, hc, hlt⟩ := GlobalTheory.QNorm.exists_unit_mul_sq_sub_one_lt K w u π (-k).toNat hπ
      (hres hw2) hu h4 (by rw [hk]; congr 1; omega)
    exact ⟨c ^ 2, by rw [map_pow, hc, one_pow], Nm.sq _ _, hlt⟩
  · have hk0 : 2 * k + 1 ≤ 0 := by
      rw [hk, ← WithZero.exp_zero, WithZero.exp_le_exp] at hle; exact hle
    have hlt1 : w (u - 1) < 1 := by
      rw [hk, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have hs : w (z * (π ^ (j - k)) ^ 2) = w (u - 1) := by
      rw [val_mul_zpow_sq w hπ hz, hk]; congr 1; ring
    set s := π ^ (j - k)
    have hpos : 0 < w (u - 1) := by rw [hk]; exact WithZero.exp_pos
    have hs0 : z * s ^ 2 ≠ 0 := ne_zero_of_exp w (hs.trans hk)
    obtain ⟨y, hy, hy'⟩ := hres hw2 ((u - 1) / (z * s ^ 2)) (by
      rw [map_div₀, hs, div_self hpos.ne'])
    have h1 : w (z * s ^ 2 * y ^ 2) < 1 := by
      rw [map_mul, hs, map_pow]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one₀ zero_le hy)) hlt1
    refine ⟨1 - z * s ^ 2 * y ^ 2, w.map_one_sub_of_lt h1, ⟨1, s * y, by ring⟩, ?_⟩
    have e : u * (1 - z * s ^ 2 * y ^ 2) - 1 = z * s ^ 2 * ((u - 1) / (z * s ^ 2) - y ^ 2) -
        (u - 1) * (z * s ^ 2 * y ^ 2) := by
      rw [mul_sub (z * s ^ 2), mul_div_cancel₀ _ hs0]; ring
    rw [e]
    refine w.map_sub_lt ?_ ?_
    · rw [map_mul, hs]; exact mul_lt_of_lt_one_right hpos hy'
    · rw [map_mul]; exact mul_lt_of_lt_one_right hpos h1

theorem exists_mul_near (h2 : (2 : K) ≠ 0) {π : K} (hπ : w π = WithZero.exp (-1))
    (hres : w 2 < 1 → ∀ x : K, w x ≤ 1 → ∃ y : K, w y ≤ 1 ∧ w (x - y ^ 2) < 1)
    {z : K} {j : ℤ} (hz : w z = WithZero.exp (2 * j + 1)) {d : K} (hd : d ≠ 0) :
    ∃ m : K, Nm z m ∧ w (d * m) = 1 ∧ w (d * m - 1) ≤ w 4 := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have he := (WithZero.exp_log ((Valuation.ne_zero_iff w).2 h4)).symm
  set e := WithZero.log (w 4)
  have H : ∀ (N : ℕ) (u : K), w u = 1 → w (u - 1) ≤ WithZero.exp (e + N) →
      ∃ m : K, Nm z m ∧ w (u * m) = 1 ∧ w (u * m - 1) ≤ w 4 := by
    intro N
    induction N with
    | zero =>
      intro u hu h
      exact ⟨1, ⟨1, 0, by ring⟩, by rwa [mul_one], by simpa [he] using h⟩
    | succ N ih =>
      intro u hu h
      by_cases h5 : w (u - 1) ≤ w 4
      · exact ⟨1, ⟨1, 0, by ring⟩, by rwa [mul_one], by rwa [mul_one]⟩
      obtain ⟨m, hm1, hm, hlt⟩ := step w hπ hres hz hu (not_le.1 h5)
      obtain ⟨m', hm', H⟩ := ih (u * m) (by rw [map_mul, hu, hm1, one_mul]) (by
        by_cases h0 : u * m - 1 = 0
        · rw [h0]; simp
        have hf := (WithZero.exp_log ((Valuation.ne_zero_iff w).2 h0)).symm
        have := hlt.trans_le h
        rw [hf, WithZero.exp_lt_exp] at this
        rw [hf, WithZero.exp_le_exp]
        push_cast at this
        omega)
      exact ⟨m * m', hm.mul hm', by rwa [← mul_assoc]⟩
  obtain ⟨m, hm, hu⟩ : ∃ m : K, Nm z m ∧ w (d * m) = 1 := by
    rcases even_or_odd w hd with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨_, Nm.sq z (π ^ k), by rw [val_mul_zpow_sq w hπ hk]; simp⟩
    · have h1 : w (d * -z) = WithZero.exp (2 * (k + j + 1)) := by
        rw [map_mul, Valuation.map_neg, hk, hz, ← WithZero.exp_add]; congr 1; ring
      exact ⟨_, Nm.mul (x := -z) ⟨0, 1, by ring⟩ (Nm.sq z (π ^ (k + j + 1))), by
        rw [← mul_assoc, val_mul_zpow_sq w hπ h1]; simp⟩
  obtain ⟨m', hm', H'⟩ := H (-e).toNat _ hu (by
    refine (w.map_sub_le hu.le (by simp)).trans ?_
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega)
  exact ⟨m * m', hm.mul hm', by rwa [← mul_assoc]⟩

theorem isSquare_of_near (hsq : ∀ x : K, w (x - 1) < w 4 → IsSquare x) {u s : K} (hs : w s = 1)
    (h : w (u - s ^ 2) < w 4) : IsSquare u := by
  have hs0 := ne_zero_of_one w hs
  have h1 : IsSquare (u / s ^ 2) := by
    refine hsq _ ?_
    rw [div_sub_one (pow_ne_zero 2 hs0), map_div₀, map_pow, hs, one_pow, div_one]; exact h
  rw [← div_mul_cancel₀ u (pow_ne_zero 2 hs0)]
  exact h1.mul (IsSquare.sq _)

theorem nm_unit_of_two_lt (h2 : (2 : K) ≠ 0) (hsq : ∀ x : K, w (x - 1) < w 4 → IsSquare x)
    (hres : ∀ x : K, w x ≤ 1 → ∃ y : K, w y ≤ 1 ∧ w (x - y ^ 2) < 1) {Δ u : K}
    (hΔ : w (Δ - 1) ≤ w 4) (hu : w u = 1) : Nm Δ u := by
  by_cases h1 : Δ = 1
  · exact Nm.of_isSquare_left h2 (h1 ▸ one_ne_zero) (h1 ▸ IsSquare.one) u
  obtain ⟨a, -, ha⟩ := hres u hu.le
  have ha2 : w (a ^ 2) = 1 := by
    rw [show a ^ 2 = u - (u - a ^ 2) by ring,
      Valuation.map_sub_eq_of_lt_left w (by rw [hu]; exact ha), hu]
  rw [map_pow] at ha2
  have ha1 : w a = 1 := (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 ha2
  have hpos : 0 < w (Δ - 1) := zero_lt_iff.2 ((Valuation.ne_zero_iff w).2 (sub_ne_zero.2 h1))
  obtain ⟨c, hc⟩ := isSquare_of_near w hsq (u := a ^ 2 - (Δ - 1) * (u - a ^ 2)) ha1 (by
    rw [sub_sub_cancel_left, Valuation.map_neg, map_mul]
    exact (mul_lt_of_lt_one_right hpos ha).trans_le hΔ)
  exact Nm.of_mul (sub_ne_zero.2 (Ne.symm h1)) ⟨1, 1, by ring⟩ ⟨c, a, by linear_combination hc⟩

end Field

theorem exists_sq_add_of_not {k : Type} [Field k] [Finite k] (h2 : (2 : k) = 0) {a b : k}
    (ha : ∀ x, x ^ 2 + x ≠ a) (hb : ∀ x, x ^ 2 + x ≠ b) : ∃ x, x ^ 2 + x = a + b := by
  let f : k →+ k :=
    { toFun := fun x => x ^ 2 + x
      map_zero' := by simp
      map_add' := fun x y => by linear_combination x * y * h2 }
  have hker : Nat.card f.ker = 2 := by
    have : (f.ker : Set k) = {0, -1} := by
      ext x
      change x ^ 2 + x = 0 ↔ x = 0 ∨ x = -1
      rw [show x ^ 2 + x = x * (x + 1) by ring, mul_eq_zero, add_eq_zero_iff_eq_neg]
    change Nat.card (f.ker : Set k) = 2
    rw [this, Nat.card_coe_set_eq, Set.ncard_pair (by simp)]
  have h1 := f.ker.card_mul_index
  have h3 := f.range.card_mul_index
  rw [hker, AddSubgroup.index_ker] at h1
  have hidx : f.range.index = 2 := by
    have hpos : 0 < Nat.card f.range := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [h3, ← h1, mul_comm]
  have := (AddSubgroup.add_mem_iff_of_index_two hidx (a := a) (b := b)).2
    (iff_of_false (fun ⟨x, hx⟩ => ha x hx) (fun ⟨x, hx⟩ => hb x hx))
  exact this

section Completion

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem isSquare_mul_of_near {x y : v.adicCompletion F} (hx : Valued.v x = 1) (hy : Valued.v y = 1)
    (hx4 : Valued.v (x - 1) ≤ Valued.v (4 : v.adicCompletion F))
    (hy4 : Valued.v (y - 1) ≤ Valued.v (4 : v.adicCompletion F))
    (hx' : ¬ IsSquare x) (hy' : ¬ IsSquare y) : IsSquare (x * y) := by
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  rcases (map_two_le (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).eq_or_lt with h2 | h2
  · exact GlobalTheory.QNorm.isSquare_mul_of_nonsquare_units F v h2 x y hx hy hx' hy'
  haveI := GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  have hres : ∀ z : v.adicCompletionIntegers F,
      residue (v.adicCompletionIntegers F) z = 0 ↔ Valued.v (z : v.adicCompletion F) < 1 := by
    intro z
    rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact ⟨fun h => lt_of_le_of_ne z.2 h, fun h => h.ne⟩
  have h20 : (2 : ResidueField (v.adicCompletionIntegers F)) = 0 := by
    have := (hres 2).2 h2
    rwa [map_ofNat] at this
  have hpos : 0 < Valued.v (4 : v.adicCompletion F) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (by norm_num))
  have key : ∀ r s : v.adicCompletionIntegers F,
      residue _ s ^ 2 + residue _ s = residue _ r → IsSquare (1 + 4 * (r : v.adicCompletion F)) := by
    intro r s h
    have h1 := (hres (r - (s ^ 2 + s))).1 (by rw [map_sub, map_add, map_pow, h, sub_self])
    refine isSquare_of_near Valued.v (GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt F v)
      (s := 1 + 2 * (s : v.adicCompletion F)) (Valuation.map_one_add_of_lt _ ?_) ?_
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' s.2) h2
    · rw [show 1 + 4 * (r : v.adicCompletion F) - (1 + 2 * (s : v.adicCompletion F)) ^ 2 =
        4 * ((r : v.adicCompletion F) - ((s : v.adicCompletion F) ^ 2 + s)) by ring, map_mul]
      exact mul_lt_of_lt_one_right hpos h1
  let r : v.adicCompletionIntegers F := ⟨(x - 1) / 4, by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
    exact div_le_one_of_le₀ hx4 zero_le⟩
  let t : v.adicCompletionIntegers F := ⟨(y - 1) / 4, by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
    exact div_le_one_of_le₀ hy4 zero_le⟩
  have ex : x = 1 + 4 * (r : v.adicCompletion F) := by
    change x = 1 + 4 * ((x - 1) / 4)
    ring
  have ey : y = 1 + 4 * (t : v.adicCompletion F) := by
    change y = 1 + 4 * ((y - 1) / 4)
    ring
  obtain ⟨s, hs⟩ := exists_sq_add_of_not h20 (a := residue _ r) (b := residue _ t)
    (fun s h => by
      obtain ⟨s, rfl⟩ := residue_surjective s
      exact hx' (ex ▸ key r s h))
    (fun s h => by
      obtain ⟨s, rfl⟩ := residue_surjective s
      exact hy' (ey ▸ key t s h))
  obtain ⟨s, rfl⟩ := residue_surjective s
  have := key (r + t + 2 * (2 * r * t)) s (by
    rw [hs, map_add, map_add, map_mul, map_ofNat, h20, zero_mul, add_zero])
  have e : x * y = 1 + 4 * ((r : v.adicCompletion F) + t + 2 * (2 * r * t)) := by
    rw [ex, ey]; ring
  rw [e]
  exact this

theorem nm_mul_adicCompletion {d x y : v.adicCompletion F} (hd : d ≠ 0) (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hx : ¬ Nm d x) (hy : ¬ Nm d y) : Nm d (x * y) := by
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  obtain ⟨⟨π, -, hπ⟩, -⟩ := GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives F v
  have hres := GlobalTheory.QNorm.exists_sub_sq_lt_one_of_two_lt_one F v
  obtain ⟨Δ, hΔ1, hΔ4, hΔ⟩ : ∃ Δ : v.adicCompletion F, Valued.v Δ = 1 ∧
      Valued.v (Δ - 1) ≤ Valued.v (4 : v.adicCompletion F) ∧ ∀ u : v.adicCompletion F,
        Valued.v u = 1 → Valued.v (u - 1) ≤ Valued.v (4 : v.adicCompletion F) →
          IsSquare u ∨ IsSquare (u * Δ) := by
    by_cases h : ∃ Δ : v.adicCompletion F, Valued.v Δ = 1 ∧
      Valued.v (Δ - 1) ≤ Valued.v (4 : v.adicCompletion F) ∧ ¬ IsSquare Δ
    · obtain ⟨Δ, h1, h2, h3⟩ := h
      exact ⟨Δ, h1, h2, fun u hu hu4 => or_iff_not_imp_left.2 fun hu' =>
        isSquare_mul_of_near F v hu h1 hu4 h2 hu' h3⟩
    · push Not at h
      exact ⟨1, by simp, by simp, fun u hu hu4 => Or.inl (h u hu hu4)⟩
  refine core Valued.v two_ne_zero hπ (ne_zero_of_one _ hΔ1) hd (fun z n hz => ?_)
    (fun z n hz => ?_) hx0 hy0 hx hy
  · have hu := val_mul_zpow_sq Valued.v hπ hz n
    rw [sub_self, WithZero.exp_zero] at hu
    refine Nm.of_mul (pow_ne_zero 2 (zpow_ne_zero n (ne_zero_of_exp _ hπ))) (Nm.sq _ _) ?_
    rcases (map_two_le (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).eq_or_lt with h2 | h2
    · obtain ⟨a, -, b, -, h⟩ := GlobalTheory.QNorm.exists_integral_sq_sub_mul_sq_of_unit F v Δ _ h2 hΔ1 hu
      exact ⟨a, b, h⟩
    · exact nm_unit_of_two_lt Valued.v two_ne_zero
        (GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt F v) (hres h2) hΔ4 hu
  · obtain ⟨m, hm, h1, h4⟩ := exists_mul_near Valued.v two_ne_zero hπ hres hz hd
    have hm0 : m ≠ 0 := right_ne_zero_of_mul (ne_zero_of_one _ h1)
    refine (hΔ _ h1 h4).imp (fun h => Nm.of_mul hm0 hm (Nm.of_isSquare _ h))
      fun h => Nm.of_mul hm0 hm (Nm.of_isSquare _ ?_)
    rwa [mul_right_comm]

theorem isSquare_mul_infinite (w : InfinitePlace F) {x y : w.Completion} (hx : ¬ IsSquare x)
    (hy : ¬ IsSquare y) : IsSquare (x * y) := by
  rcases w.isReal_or_isComplex with hw | hw
  · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    have h : ∀ z : w.Completion, IsSquare z ↔ 0 ≤ e z := fun z => by
      rw [← Real.isSquare_iff]
      exact ⟨fun h => h.map e, fun h => by simpa using h.map e.symm⟩
    rw [h] at hx hy ⊢
    rw [map_mul]
    exact mul_nonneg_of_nonpos_of_nonpos (not_le.1 hx).le (not_le.1 hy).le
  · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
    have h : IsSquare (e x) := IsAlgClosed.exists_eq_mul_self (e x)
    exact absurd (by simpa using h.map e.symm) hx

end Completion

theorem eta_mul {K L A : Type} [Field K] [Field L] [Algebra K L] [CommRing A] [Algebra K A]
    (h : ∀ a b : Aˣ, a ∉ normGroup K L A → b ∉ normGroup K L A → a * b ∈ normGroup K L A)
    (a b : Aˣ) : eta K L A (a * b) = eta K L A a * eta K L A b := by
  by_cases ha : a ∈ normGroup K L A <;> by_cases hb : b ∈ normGroup K L A
  · rw [eta_eq_one_iff.2 ha, eta_eq_one_iff.2 hb, eta_eq_one_iff.2 (mul_mem ha hb), one_mul]
  · rw [eta_eq_one_iff.2 ha, eta_eq_neg_one_iff.2 hb, one_mul, eta_eq_neg_one_iff,
      mul_mem_cancel_left ha]
    exact hb
  · rw [eta_eq_one_iff.2 hb, eta_eq_neg_one_iff.2 ha, mul_one, eta_eq_neg_one_iff,
      mul_mem_cancel_right hb]
    exact ha
  · rw [eta_eq_neg_one_iff.2 ha, eta_eq_neg_one_iff.2 hb, eta_eq_one_iff.2 (h a b ha hb)]
    simp

end NormIndex

open NormIndex in

theorem localCharacters : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [Algebra.IsQuadraticExtension K L], LocalCharacters K L := by
  intro K L _ _ _ _ _ _
  have hr := Algebra.IsQuadraticExtension.finrank_eq_two K L
  have hcard : Nat.card (L ≃ₐ[K] L) = 2 := (IsGalois.card_aut_eq_finrank K L).trans hr
  obtain ⟨σ, hσ, hall⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[K] L)).1 hcard
  have hσσ : σ * σ = 1 := by
    by_contra h
    exact hσ (by simpa using hall _ h)
  obtain ⟨δ, e, hδ, h0, -, h1⟩ := GlobalTheory.QuadNormBase.exists_basis K L (σ : L →ₐ[K] L) hr
    (fun x => DFunLike.congr_fun hσσ x) (by
      by_contra h
      push Not at h
      exact hσ (AlgEquiv.ext h))
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  refine ⟨fun v => eta_mul fun a b ha hb => ?_, fun w => eta_mul fun a b ha hb => ?_⟩
  · rw [mem_normGroup_iff_form e h0 h1] at ha hb ⊢
    exact nm_mul_adicCompletion K v ((map_ne_zero _).2 hδ0) a.ne_zero b.ne_zero ha hb
  · rw [mem_normGroup_iff_form e h0 h1] at ha hb ⊢
    exact Nm.of_isSquare _ (isSquare_mul_infinite K w (fun h => ha (Nm.of_isSquare _ h))
      fun h => hb (Nm.of_isSquare _ h))

end GlobalTheory.QuadSymbol
