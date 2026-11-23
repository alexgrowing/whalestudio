import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation
open Matrix

noncomputable section

namespace GlobalTheory.DetSelfDual

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem star_mem_one {a : E} (ha : a ∈ (1 : Submodule (𝓞 E) E)) : star a ∈ (1 : Submodule (𝓞 E) E) := by
  obtain ⟨r, rfl⟩ := Submodule.mem_one.1 ha
  exact Submodule.mem_one.2 (star_range r)

theorem carries_iff (N : Submodule (𝓞 E) (Sp E n)) (A : Matrix (Fin n) (Fin n) E) :
    (∀ v ∈ stdLat E n, A.mulVec v ∈ N) ↔ ∀ j, A.col j ∈ N := by
  constructor
  · intro h j
    have := h _ (single_mem_stdLat j 1)
    rwa [map_one, Matrix.mulVec_single_one] at this
  · intro h v hv
    rw [Matrix.mulVec_eq_sum]
    refine N.sum_mem fun j _ => ?_
    obtain ⟨r, hr⟩ := (mem_stdLat v).1 hv j
    have : (MulOpposite.op (v j) • Aᵀ j : Sp E n) = r • A.col j := by
      funext i
      simp [← hr, Algebra.smul_def, Matrix.col, mul_comm]
    rw [this]
    exact N.smul_mem r (h j)

theorem det_mem_detLat {N : Submodule (𝓞 E) (Sp E n)} {A : Matrix (Fin n) (Fin n) E}
    (h : ∀ j, A.col j ∈ N) : A.det ∈ detLat N :=
  Submodule.subset_span ⟨A, (carries_iff N A).2 h, rfl⟩

omit [StarRing E] [NumberField E] in
theorem det_mem_one {A : Matrix (Fin n) (Fin n) E} (h : ∀ i j, A i j ∈ (1 : Submodule (𝓞 E) E)) :
    A.det ∈ (1 : Submodule (𝓞 E) E) := by
  choose B hB using fun i j => Submodule.mem_one.1 (h i j)
  refine Submodule.mem_one.2 ⟨Matrix.det (Matrix.of B), ?_⟩
  rw [RingHom.map_det]
  congr 1
  ext i j
  simpa using hB i j

theorem star_det_mul_det_mem {N : Submodule (𝓞 E) (Sp E n)} (hN : dual (hStd E n) N = N)
    {A B : Matrix (Fin n) (Fin n) E} (hA : ∀ j, A.col j ∈ N) (hB : ∀ j, B.col j ∈ N) :
    star A.det * B.det ∈ (1 : Submodule (𝓞 E) E) := by
  rw [← Matrix.det_conjTranspose, ← Matrix.det_mul]
  refine det_mem_one fun i j => ?_
  have := (mem_dual N (B.col j)).1 (hN.symm ▸ hB j) _ (hA i)
  rw [hStd_apply] at this
  simpa [Matrix.mul_apply, Matrix.col] using this

theorem star_mul_mem {N : Submodule (𝓞 E) (Sp E n)} (hN : dual (hStd E n) N = N)
    {a b : E} (ha : a ∈ detLat N) (hb : b ∈ detLat N) : star a * b ∈ (1 : Submodule (𝓞 E) E) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨A, hA, rfl⟩ := hx
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨B, hB, rfl⟩ := hy
      exact star_det_mul_det_mem hN ((carries_iff N A).1 hA) ((carries_iff N B).1 hB)
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx
  | zero => simp
  | add x y _ _ hx hy => rw [star_add, add_mul]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    obtain ⟨s, hs⟩ := star_range r
    rw [Algebra.smul_def, star_mul', ← hs, mul_assoc, ← Algebra.smul_def]
    exact Submodule.smul_mem _ s hx

omit [StarRing E] in
theorem exists_det_ne_zero {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N) :
    ∃ A : Matrix (Fin n) (Fin n) E, (∀ j, A.col j ∈ N) ∧ A.det ≠ 0 := by
  have h : ∀ j : Fin n, ∃ t : nonZeroDivisors (𝓞 E), t • (Pi.single j 1 : Sp E n) ∈ N := by
    intro j
    have := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E (N : Set (Sp E n))
      (Pi.single j 1) (by rw [hN.span_eq_top]; trivial)
    rwa [Submodule.span_eq] at this
  choose t ht using h
  refine ⟨Matrix.diagonal fun j => algebraMap (𝓞 E) E (t j), fun j => ?_, ?_⟩
  · convert ht j using 1
    funext i
    by_cases hij : i = j
    · subst hij; simp [Matrix.col, Submonoid.smul_def, Algebra.smul_def]
    · simp [Matrix.col, hij]
  · rw [Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
    simp

omit [StarRing E] in
theorem exists_denom (P : HeightOneSpectrum (𝓞 E)) (F : Finset E) (h : ∀ x ∈ F, P.valuation E x ≤ 1) :
    ∃ t : 𝓞 E, t ∉ P.asIdeal ∧ ∀ x ∈ F, t • x ∈ (1 : Submodule (𝓞 E) E) := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top, by simp⟩
  | insert a F _ ih =>
    obtain ⟨t, ht, H⟩ := ih fun x hx => h x (Finset.mem_insert_of_mem hx)
    obtain ⟨s, hs, Hs⟩ := (mem_locP' (P := P) 1 a).1
      ((maxV_one.mem_locP one_ne_zero a).2 (h a (Finset.mem_insert_self _ _)))
    refine ⟨t * s, fun hm => (P.isPrime.mem_or_mem hm).elim ht hs, fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · rw [mul_smul]; exact Submodule.smul_mem _ t Hs
    · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ s (H x hx)

theorem exists_max_det {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) (P : HeightOneSpectrum (𝓞 E)) :
    ∃ B : Matrix (Fin n) (Fin n) E, (∀ j, B.col j ∈ N) ∧ B.det ≠ 0 ∧
      ∀ C : Matrix (Fin n) (Fin n) E, (∀ j, C.col j ∈ N) → P.valuation E C.det ≤ P.valuation E B.det := by
  obtain ⟨A, hA, hA0⟩ := exists_det_ne_zero hN.1
  have hsA : P.valuation E (star A.det) ≠ 0 := by simpa using hA0
  obtain ⟨z, ⟨B, hB, hB0, rfl⟩, hz⟩ := Int.exists_greatest_of_bdd
    (P := fun z => ∃ B : Matrix (Fin n) (Fin n) E, (∀ j, B.col j ∈ N) ∧ B.det ≠ 0 ∧
      WithZero.log (P.valuation E B.det) = z)
    ⟨- WithZero.log (P.valuation E (star A.det)), by
      rintro z ⟨B, hB, hB0, rfl⟩
      have hvB : P.valuation E B.det ≠ 0 := by simpa using hB0
      have h1 := (maxV_one (P := P)).1 _ (star_det_mul_det_mem hN.2 hA hB)
      rw [map_mul] at h1
      have h2 := (WithZero.log_le_log (mul_ne_zero hsA hvB) one_ne_zero).2 h1
      rw [WithZero.log_mul hsA hvB, WithZero.log_one] at h2
      linarith⟩
    ⟨_, A, hA, hA0, rfl⟩
  refine ⟨B, hB, hB0, fun C hC => ?_⟩
  by_cases hC0 : C.det = 0
  · simp [hC0]
  · exact (WithZero.log_le_log (by simpa using hC0) (by simpa using hB0)).1 (hz _ ⟨C, hC, hC0, rfl⟩)

theorem exists_unit_at {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) (P : HeightOneSpectrum (𝓞 E)) :
    ∃ a ∈ detLat N, ∃ b ∈ detLat N, ∃ t : 𝓞 E, t ∉ P.asIdeal ∧ star a * b = algebraMap (𝓞 E) E t := by
  classical
  obtain ⟨B, hB, hB0, hmax⟩ := exists_max_det hN P
  have hvB : P.valuation E B.det ≠ 0 := by simpa using hB0
  have hu : IsUnit B.det := isUnit_iff_ne_zero.2 hB0
  have h1 : ∀ x ∈ N, ∀ i, P.valuation E ((B⁻¹ *ᵥ x) i) ≤ 1 := by
    intro x hx i
    have hc := congrFun (Matrix.det_smul_inv_mulVec_eq_cramer B x hu) i
    rw [Matrix.cramer_apply, Pi.smul_apply, smul_eq_mul] at hc
    have := hmax (B.updateCol i x) (fun j => by
      by_cases hj : j = i
      · subst hj
        convert hx using 1
        funext k; simp [Matrix.col]
      · convert hB j using 1
        funext k; simp [Matrix.col, Matrix.updateCol_ne hj])
    rw [← hc, map_mul] at this
    exact (mul_le_iff_le_one_right (zero_lt_iff.2 hvB)).1 this
  obtain ⟨S, hS⟩ := hN.1.fg
  obtain ⟨t, ht, H⟩ := exists_denom P ((S ×ˢ (Finset.univ : Finset (Fin n))).image fun p => (B⁻¹ *ᵥ p.1) p.2)
    (by
      intro y hy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hy
      exact h1 _ (hS ▸ Submodule.subset_span (Finset.mem_product.1 hp).1) _)
  have h2 : ∀ x ∈ N, ∀ i, t • (B⁻¹ *ᵥ x) i ∈ (1 : Submodule (𝓞 E) E) := by
    intro x hx i
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact H _ (Finset.mem_image.2 ⟨(y, i), Finset.mem_product.2 ⟨hy, Finset.mem_univ _⟩, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add, Pi.add_apply, smul_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      rw [Matrix.mulVec_smul, Pi.smul_apply, smul_comm]; exact Submodule.smul_mem _ r hx
  let A : Matrix (Fin n) (Fin n) E := (algebraMap (𝓞 E) E t • B⁻¹)ᴴ
  have hA : ∀ j, A.col j ∈ N := by
    intro j
    have hd : dual (hStd E n) N = N := hN.2
    rw [← hd, mem_dual]
    intro y hy
    convert star_mem_one (h2 y hy j) using 1
    rw [hStd_apply, Algebra.smul_def, Matrix.mulVec, dotProduct, Finset.mul_sum, star_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [A, Matrix.col, Matrix.transpose_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, star_mul']
    ring
  refine ⟨A.det, det_mem_detLat hA, B.det, det_mem_detLat hB, t ^ n,
    fun h => ht (P.isPrime.mem_of_pow_mem n h), ?_⟩
  rw [← Matrix.det_conjTranspose, Matrix.conjTranspose_conjTranspose, ← Matrix.det_mul, Matrix.smul_mul,
    Matrix.nonsing_inv_mul _ hu, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, map_pow]

theorem detLat_mul_conj (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)
    (N : Submodule (𝓞 E) (Sp E n)) (hN : IsSdLat N) :
    ∃ J : Submodule (𝓞 E) E, (∀ x, x ∈ J ↔ star x ∈ detLat N) ∧ detLat N * J = 1 := by
  let J : Submodule (𝓞 E) E :=
    { carrier := {x | star x ∈ detLat N}
      add_mem' := fun {a b} ha hb => by
        show star (a + b) ∈ detLat N
        rw [star_add]; exact Submodule.add_mem _ ha hb
      zero_mem' := by
        show star (0 : E) ∈ detLat N
        simp
      smul_mem' := fun r x hx => by
        show star (r • x) ∈ detLat N
        obtain ⟨s, hs⟩ := star_range r
        rw [Algebra.smul_def, star_mul', ← hs, ← Algebra.smul_def]
        exact Submodule.smul_mem _ s hx }
  have hJ : ∀ x, x ∈ J ↔ star x ∈ detLat N := fun x => Iff.rfl
  refine ⟨J, hJ, le_antisymm (Submodule.mul_le.2 fun a ha b hb => ?_) ?_⟩
  · have := star_mul_mem hN.2 ((hJ b).1 hb) ha
    rwa [star_star, mul_comm] at this
  · rw [Submodule.one_le]
    by_contra hne
    let I : Ideal (𝓞 E) := (detLat N * J).comap (Algebra.linearMap (𝓞 E) E)
    have hI : I ≠ ⊤ := by
      rw [Ideal.ne_top_iff_one]
      intro h
      apply hne
      simpa [I] using h
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
    obtain ⟨a, ha, b, hb, t, ht, h⟩ := exists_unit_at hN
      ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)⟩
    apply ht
    apply hIM
    show algebraMap (𝓞 E) E t ∈ detLat N * J
    rw [← h, mul_comm (star a) b]
    exact Submodule.mul_mem_mul hb ((hJ _).2 (by rwa [star_star]))

end GlobalTheory.DetSelfDual
