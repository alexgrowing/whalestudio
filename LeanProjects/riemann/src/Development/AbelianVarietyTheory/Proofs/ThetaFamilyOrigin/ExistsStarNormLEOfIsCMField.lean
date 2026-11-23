import Mathlib
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion

set_option autoImplicit false

open NumberField

namespace GlobalTheory

namespace StarNormBound

variable {E : Type} [Field E] [NumberField E] (σ : E ≃ₐ[ℚ] E)

def normSums : AddSubmonoid E := AddSubmonoid.closure (Set.range fun b : E => σ b * b)

theorem norm_mem (b : E) : σ b * b ∈ normSums σ :=
  AddSubmonoid.subset_closure ⟨b, rfl⟩

theorem norm_mul_mem (t : E) {s : E} (hs : s ∈ normSums σ) : σ t * t * s ∈ normSums σ := by
  induction hs using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    have h : σ t * t * (σ b * b) = σ (t * b) * (t * b) := by rw [map_mul]; ring
    rw [h]
    exact norm_mem σ _
  | zero => rw [mul_zero]; exact (normSums σ).zero_mem
  | add x y _ _ hx hy => rw [mul_add]; exact (normSums σ).add_mem hx hy

theorem rat_mul_mem {q : ℚ} (hq : 0 ≤ q) {s : E} (hs : s ∈ normSums σ) : (q : E) * s ∈ normSums σ := by
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (Rat.num_nonneg.mpr hq)
  have hden : (q.den : ℚ) ≠ 0 := by positivity
  have hq' : q = ((n * q.den : ℕ) : ℚ) * ((q.den : ℚ)⁻¹ * (q.den : ℚ)⁻¹) := by
    have h := Rat.num_div_den q
    rw [hn] at h
    conv_lhs => rw [← h]
    push_cast
    field_simp
  have hE : (q : E) = ((n * q.den : ℕ) : E) * (((q.den : ℚ)⁻¹ : ℚ) * ((q.den : ℚ)⁻¹ : ℚ) : E) := by
    conv_lhs => rw [hq']
    push_cast
    ring
  have key : (q : E) * s = (n * q.den) • (σ (((q.den : ℚ)⁻¹ : ℚ) : E) * (((q.den : ℚ)⁻¹ : ℚ) : E) * s) := by
    rw [nsmul_eq_mul, map_ratCast, hE]
    push_cast
    ring
  rw [key]
  exact AddSubmonoid.nsmul_mem _ (norm_mul_mem σ _ hs) _

theorem rat_mem {q : ℚ} (hq : 0 ≤ q) : (q : E) ∈ normSums σ := by
  have h1 : (1 : E) ∈ normSums σ := by simpa using norm_mem σ 1
  simpa using rat_mul_mem σ hq h1

theorem casimir {ι : Type} [Fintype ι] [DecidableEq ι] (e : Module.Basis ι ℚ E)
    (ho : ∀ i j, i ≠ j → Algebra.trace ℚ E (σ (e i) * e j) = 0)
    (hd : ∀ i, Algebra.trace ℚ E (σ (e i) * e i) ≠ 0) :
    ∑ i, (Algebra.trace ℚ E (σ (e i) * e i))⁻¹ • (σ (e i) * e i) = 1 := by
  set c := ∑ i, (Algebra.trace ℚ E (σ (e i) * e i))⁻¹ • (σ (e i) * e i) with hc
  have htr : ∀ y : E, Algebra.trace ℚ E (c * y) = Algebra.trace ℚ E y := by
    intro y
    rw [Algebra.trace_eq_matrix_trace e y]
    simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul]
    rw [hc, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, map_smul, mul_assoc, mul_comm y (e i)]
    conv_lhs => rw [← e.sum_repr (e i * y)]
    rw [Finset.mul_sum, map_sum, Finset.sum_eq_single i]
    · rw [mul_smul_comm, map_smul, smul_eq_mul, smul_eq_mul]
      field_simp [hd i]
    · intro j _ hj
      rw [mul_smul_comm, map_smul, ho i j (Ne.symm hj), smul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  by_contra hne
  have hne' : c - 1 ≠ 0 := sub_ne_zero.mpr hne
  have h2 : Algebra.trace ℚ E ((c - 1) * (c - 1)⁻¹) = 0 := by
    rw [sub_mul, map_sub, htr, one_mul, sub_self]
  rw [mul_inv_cancel₀ hne'] at h2
  have h3 := Algebra.trace_algebraMap (R := ℚ) (S := E) 1
  rw [map_one] at h3
  rw [h3] at h2
  have h4 : (Module.finrank ℚ E : ℚ) = 0 := by simpa using h2
  exact Module.finrank_pos.ne' (by exact_mod_cast h4)

theorem exists_rat_bound (hσ : ∀ x, σ (σ x) = x) (hp : ∀ x, x ≠ 0 → 0 < Algebra.trace ℚ E (σ x * x))
    (x : E) : ∃ c : ℚ, (c : E) - σ x * x ∈ normSums σ := by
  classical
  have : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
  have hsym : ∀ u v : E, Algebra.trace ℚ E (σ u * v) = Algebra.trace ℚ E (σ v * u) := by
    intro u v
    rw [← Algebra.trace_eq_of_algEquiv σ (σ v * u), map_mul σ, hσ, mul_comm]
  obtain ⟨e, he⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (B := LinearMap.mk₂ ℚ (fun u v : E => Algebra.trace ℚ E (σ u * v))
      (fun a b c => by rw [map_add, add_mul, map_add])
      (fun r a b => by
        rw [show σ (r • a) = r • σ a by rw [Rat.smul_def, Rat.smul_def, map_mul, map_ratCast],
          smul_mul_assoc, map_smul])
      (fun a b c => by rw [mul_add, map_add])
      (fun r a b => by rw [mul_smul_comm, map_smul]))
    (LinearMap.isSymm_def.mpr fun u v => by simp only [LinearMap.mk₂_apply, RingHom.id_apply]; exact hsym u v)
  rw [LinearMap.isOrthoᵢ_def] at he
  simp only [LinearMap.mk₂_apply] at he
  have hd : ∀ i, Algebra.trace ℚ E (σ (e i) * e i) ≠ 0 := fun i => (hp _ (e.ne_zero i)).ne'
  have hcas := casimir σ e he hd
  obtain ⟨d, hd_def⟩ : ∃ d : Fin (Module.finrank ℚ E) → ℚ, ∀ j, d j = Algebra.trace ℚ E (σ (e j) * e j) :=
    ⟨_, fun _ => rfl⟩
  simp_rw [← hd_def] at hcas hd
  have hdpos : ∀ j, 0 < d j := fun j => by rw [hd_def]; exact hp _ (e.ne_zero j)
  have hbasis : ∀ i, ∃ c : ℚ, (c : E) - σ (e i) * e i ∈ normSums σ := by
    intro i
    refine ⟨d i, ?_⟩
    have h1 : ((d i : ℚ) : E) = ∑ j, ((d i / d j : ℚ) : E) * (σ (e j) * e j) := by
      conv_lhs => rw [← mul_one ((d i : ℚ) : E), ← hcas]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Rat.smul_def]
      push_cast
      ring
    have h2 : ((d i : ℚ) : E) - σ (e i) * e i =
        ∑ j ∈ Finset.univ.erase i, ((d i / d j : ℚ) : E) * (σ (e j) * e j) := by
      rw [h1, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), div_self (hd i), Rat.cast_one, one_mul,
        add_sub_cancel_left]
    rw [h2]
    exact AddSubmonoid.sum_mem _ fun j _ =>
      rat_mul_mem σ (div_nonneg (hdpos i).le (hdpos j).le) (norm_mem σ _)
  have hadd : ∀ u v : E, (∃ c : ℚ, (c : E) - σ u * u ∈ normSums σ) →
      (∃ c : ℚ, (c : E) - σ v * v ∈ normSums σ) → ∃ c : ℚ, (c : E) - σ (u + v) * (u + v) ∈ normSums σ := by
    rintro u v ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨2 * a + 2 * b, ?_⟩
    have h : ((2 * a + 2 * b : ℚ) : E) - σ (u + v) * (u + v) =
        ((2 : ℚ) : E) * ((a : E) - σ u * u) + ((2 : ℚ) : E) * ((b : E) - σ v * v) + σ (u - v) * (u - v) := by
      rw [map_add, map_sub]
      push_cast
      ring
    rw [h]
    exact add_mem (add_mem (rat_mul_mem σ (by norm_num) ha) (rat_mul_mem σ (by norm_num) hb)) (norm_mem σ _)
  have hsmul : ∀ (r : ℚ) (u : E), (∃ c : ℚ, (c : E) - σ u * u ∈ normSums σ) →
      ∃ c : ℚ, (c : E) - σ (r • u) * (r • u) ∈ normSums σ := by
    rintro r u ⟨a, ha⟩
    refine ⟨r ^ 2 * a, ?_⟩
    have h : ((r ^ 2 * a : ℚ) : E) - σ (r • u) * (r • u) = ((r ^ 2 : ℚ) : E) * ((a : E) - σ u * u) := by
      rw [Rat.smul_def, map_mul, map_ratCast]
      push_cast
      ring
    rw [h]
    exact rat_mul_mem σ (sq_nonneg r) ha
  have hzero : ∃ c : ℚ, (c : E) - σ 0 * 0 ∈ normSums σ := ⟨0, by simp⟩
  rw [← e.sum_repr x]
  exact Finset.sum_induction _ (fun y => ∃ c : ℚ, (c : E) - σ y * y ∈ normSums σ)
    (fun u v hu hv => hadd u v hu hv) hzero (fun i _ => hsmul _ _ (hbasis i))

theorem exists_integral_sum {s : E} (hs : s ∈ normSums σ) :
    ∃ (m r : ℕ) (b : Fin r → 𝓞 E), 1 ≤ m ∧ (m : E) ^ 2 * s = ∑ i, σ (b i : E) * (b i : E) := by
  induction hs using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {b}
    have hint : IsIntegral ℤ (y • b) := hy b (Finset.mem_singleton_self b)
    refine ⟨y.natAbs, 1, fun _ => ⟨y • b, hint⟩, Int.natAbs_pos.mpr hy0, ?_⟩
    rw [Fin.sum_univ_one]
    show _ = σ (y • b) * (y • b)
    rw [zsmul_eq_mul, map_mul, map_intCast]
    have h : ((y.natAbs : ℕ) : E) ^ 2 = (y : E) ^ 2 := by
      rw [← Int.cast_natCast, ← Int.cast_pow, Int.natAbs_sq, Int.cast_pow]
    rw [h]
    ring
  | zero => exact ⟨1, 0, Fin.elim0, le_rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, r, b, hm, hb⟩ := hx
    obtain ⟨n, r', b', hn, hb'⟩ := hy
    refine ⟨m * n, r + r', Fin.append (fun i => (n : 𝓞 E) * b i) (fun j => (m : 𝓞 E) * b' j),
      Nat.mul_pos hm hn, ?_⟩
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    push_cast
    simp only [map_mul, map_natCast]
    calc ((m : E) * n) ^ 2 * (x + y) = (n : E) ^ 2 * ((m : E) ^ 2 * x) + (m : E) ^ 2 * ((n : E) ^ 2 * y) := by
          ring
      _ = _ := by
        rw [hb, hb', Finset.mul_sum, Finset.mul_sum]
        congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> ring

theorem trace_conj_mul_pos [IsCMField E] (x : E) (hx : x ≠ 0) :
    0 < Algebra.trace ℚ E (IsCMField.complexConj E x * x) := by
  set t := Algebra.trace ℚ E (IsCMField.complexConj E x * x) with ht
  have h := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := IsCMField.complexConj E x * x)
  rw [← ht, eq_ratCast] at h
  have hre := congrArg Complex.re h
  rw [Complex.ratCast_re, Complex.re_sum] at hre
  have hpos : (0 : ℝ) < (t : ℝ) := by
    rw [hre]
    have : Nonempty (E →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
    refine Finset.sum_pos (fun τ _ => ?_) Finset.univ_nonempty
    have hc : τ (IsCMField.complexConj E x) = (starRingEnd ℂ) (τ x) :=
      IsCMField.complexEmbedding_complexConj E (τ : E →+* ℂ) x
    rw [map_mul, hc, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    have hne : τ x ≠ 0 := (map_ne_zero τ).mpr hx
    have h0 := Complex.normSq_pos.mpr hne
    rw [Complex.normSq_apply] at h0
    linarith
  exact_mod_cast hpos

end StarNormBound

open StarNormBound in

theorem exists_starNormLE_of_isCMField : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E]
    [StarRing (NumberField.RingOfIntegers E)],
    (∀ a : NumberField.RingOfIntegers E, ((star a : NumberField.RingOfIntegers E) : E) =
      NumberField.IsCMField.complexConj E (a : E)) →
    ∀ a : NumberField.RingOfIntegers E, ∃ c : ℕ, GlobalTheory.StarNormLE a c := by
  intro E _ _ _ _ hstar a
  have hσ : ∀ x, ((IsCMField.complexConj E).restrictScalars ℚ) (((IsCMField.complexConj E).restrictScalars ℚ) x) = x :=
    fun x => IsCMField.complexConj_apply_apply E x
  have hp : ∀ x, x ≠ 0 → 0 < Algebra.trace ℚ E (((IsCMField.complexConj E).restrictScalars ℚ) x * x) :=
    fun x hx => trace_conj_mul_pos x hx
  obtain ⟨q, hq⟩ := exists_rat_bound ((IsCMField.complexConj E).restrictScalars ℚ) hσ hp (a : E)
  have hc : (((⌈q⌉₊ : ℕ) : ℚ) : E) - ((IsCMField.complexConj E).restrictScalars ℚ) a * a ∈
      normSums ((IsCMField.complexConj E).restrictScalars ℚ) := by
    have h : (((⌈q⌉₊ : ℕ) : ℚ) : E) - ((IsCMField.complexConj E).restrictScalars ℚ) a * a =
        ((((⌈q⌉₊ : ℕ) : ℚ) - q : ℚ) : E) + ((q : E) - ((IsCMField.complexConj E).restrictScalars ℚ) a * a) := by
      push_cast
      ring
    rw [h]
    exact add_mem (rat_mem _ (sub_nonneg.mpr (Nat.le_ceil q))) hq
  obtain ⟨m, r, b, hm, hb⟩ := exists_integral_sum _ hc
  refine ⟨m ^ 2 * ⌈q⌉₊, m, r, b, hm, ?_⟩
  apply RingOfIntegers.ext
  have hconj : ∀ z : E, ((IsCMField.complexConj E).restrictScalars ℚ) z = IsCMField.complexConj E z :=
    fun _ => rfl
  simp only [hconj] at hb
  push_cast at hb ⊢
  simp only [hstar]
  push_cast
  rw [map_mul, map_natCast]
  linear_combination (-1 : E) * hb

end GlobalTheory
