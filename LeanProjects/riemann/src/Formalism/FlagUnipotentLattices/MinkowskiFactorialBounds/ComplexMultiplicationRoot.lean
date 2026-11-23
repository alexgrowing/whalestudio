import Formalism.FlagUnipotentLattices.DetIndexProductHyperbolicInequality
import Formalism.HyperbolicPlaceProducts.ArithmeticCountRevised

open Module NumberField Formalism.HermitianLatticeCounting.LocalIntegralStructure

namespace Formalism.HermitianLatticeCounting.P

theorem integer_group_preservation : Formalism.HermitianLatticeCounting.LocalIntegralStructure.ZZgPreserve := by
  intro E _ _ g a b c d h
  have hI : ∀ y : 𝓞 E, IsInt (y : E) := fun y => by unfold IsInt; exact ⟨y, rfl⟩
  have mem : ∀ x y : E, IsInt x → IsInt y → (∃ w : 𝓞 E, x + y = (g : E) * (w : E)) →
      (x, y) ∈ (ZZ g : Set (E × E)) := by
    intro x y hx hy hw
    simp only [ZZ, Set.mem_setOf_eq]
    exact ⟨hx, hy, hw⟩
  have out : ∀ x y : E, (x, y) ∈ (ZZ g : Set (E × E)) → IsInt x ∧ IsInt y := by
    intro x y hxy
    simp only [ZZ, Set.mem_setOf_eq] at hxy
    exact ⟨hxy.1, hxy.2.1⟩
  have hg : IsInt (g : E) := by simpa using hI (g : 𝓞 E)
  have h0 : IsInt (0 : E) := by simpa using hI 0
  have h1 : IsInt (1 : E) := by simpa using hI 1
  have hm1 : IsInt (-1 : E) := by simpa using hI (-1)
  have p1 := out _ _ (h _ (mem _ _ hg h0 ⟨1, by simp⟩))
  have p2 := out _ _ (h _ (mem _ _ h0 hg ⟨1, by simp⟩))
  have p3 := out _ _ (h _ (mem _ _ h1 hm1 ⟨0, by simp⟩))
  simp only [mul_zero, add_zero, zero_add, mul_one, mul_neg, ← sub_eq_add_neg] at p1 p2 p3
  refine ⟨?_, ?_, ?_, ?_, p3.1, p3.2⟩
  · rw [mul_comm]; exact p1.1
  · rw [mul_comm]; exact p2.1
  · rw [mul_comm]; exact p1.2
  · rw [mul_comm]; exact p2.2

theorem local_congruence_condition : Formalism.HermitianLatticeCounting.LocalIntegralStructure.LocalCongr := by
  intro E _ _ P T T' a b c d hP hT hT' h
  have hT0 : (T : E) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  have hT'0 : (T' : E) ≠ 0 := Nat.cast_ne_zero.mpr hT'.ne'
  have h1P : (1 : 𝓞 E) ∉ P := (Ideal.ne_top_iff_one P).mp hP.ne_top
  have one : ∀ x : E, x = 1 → LocIn P x 1 := by
    intro x hx; unfold LocIn
    exact ⟨1, 1, h1P, by simp [hx]⟩
  have zer : ∀ x : E, x = 0 → LocIn P x 1 := by
    intro x hx; unfold LocIn
    exact ⟨1, 0, h1P, by simp [hx]⟩
  have back : ∀ (x : E) (N : ℕ), (N : E) ≠ 0 → LocIn P (x * (1 / (N : E))) 1 → LocIn P x N := by
    intro x N hN hx
    unfold LocIn at hx ⊢
    obtain ⟨y, z, hy, hyz⟩ := hx
    refine ⟨y, z, hy, ?_⟩
    have e : (y : E) * x = (N : E) * ((y : E) * (x * (1 / (N : E)))) := by
      first
      | field_simp
      | rw [mul_one_div, mul_div_assoc', mul_div_assoc', mul_div_cancel_left₀ _ hN]
    rw [e, hyz]; simp
  obtain ⟨ha, hc⟩ := h (1 / (T : E)) 0 (one _ (by field_simp)) (zer _ (by simp))
  obtain ⟨hb, hd⟩ := h 0 (1 / (T' : E)) (zer _ (by simp)) (one _ (by field_simp))
  simp only [mul_zero, add_zero, zero_add] at ha hc hb hd
  exact ⟨back _ _ hT0 ha, back _ _ hT0 hc, back _ _ hT'0 hb, back _ _ hT'0 hd⟩

theorem complex_multiplication_root : Formalism.HermitianLatticeCounting.LocalIntegralStructure.CMRoot := by
  intro E _ _ q x hc hq hx h
  have hm : ∀ w : InfinitePlace E, w.mult = 2 := fun w =>
    NumberField.InfinitePlace.mult_isComplex ⟨w, hc w⟩
  have hn : Module.finrank ℚ E = 2 * Fintype.card (InfinitePlace E) := by
    rw [← NumberField.InfinitePlace.sum_mult_eq]
    simp only [hm, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  simp only [hm] at h
  rw [hn] at h
  have hP : ∏ w : InfinitePlace E, (x w ^ 2) ^ 2 = (∏ w : InfinitePlace E, x w) ^ 4 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl (fun w _ => by ring)
  have hA : (q ^ ((Fintype.card (InfinitePlace E) : ℝ) / 2)) ^ 4 =
      q ^ (2 * Fintype.card (InfinitePlace E)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have key : (q ^ ((Fintype.card (InfinitePlace E) : ℝ) / 2)) ^ 4 ≤ (∏ w : InfinitePlace E, x w) ^ 4 := by
    rw [hA, ← hP]; exact h
  have h0 : 0 ≤ ∏ w : InfinitePlace E, x w := Finset.prod_nonneg fun w _ => hx w
  have hq0 : 0 ≤ q ^ ((Fintype.card (InfinitePlace E) : ℝ) / 2) := (Real.rpow_pos_of_pos hq _).le
  first
  | exact le_of_pow_le_pow_left₀ (by norm_num) h0 key
  | exact (pow_le_pow_iff_left₀ hq0 h0 (by norm_num)).mp key
  | exact le_of_pow_le_pow_left (by norm_num) h0 key
  | exact (pow_le_pow_iff_left hq0 h0 (by norm_num)).mp key

namespace IntegralityLocalGlobal

variable {E : Type} [Field E] [NumberField E]

lemma isInt_mul {a b : E} (ha : IsInt a) (hb : IsInt b) : IsInt (a * b) := by
  first
  | exact ha.mul hb
  | exact IsIntegral.mul ha hb
  | (obtain ⟨x, hx⟩ := ha; obtain ⟨y, hy⟩ := hb; exact ⟨x * y, by rw [← hx, ← hy]; push_cast; ring⟩)
lemma isInt_add {a b : E} (ha : IsInt a) (hb : IsInt b) : IsInt (a + b) := by
  first
  | exact ha.add hb
  | exact IsIntegral.add ha hb
  | (obtain ⟨x, hx⟩ := ha; obtain ⟨y, hy⟩ := hb; exact ⟨x + y, by rw [← hx, ← hy]; push_cast; ring⟩)
lemma isInt_coe (y : 𝓞 E) : IsInt (y : E) := by
  first
  | exact y.2
  | exact ⟨y, rfl⟩
  | exact NumberField.RingOfIntegers.isIntegral_coe y
lemma isInt_map (σ : E →+* E) {a : E} (ha : IsInt a) : IsInt (σ a) := by
  obtain ⟨x, rfl⟩ := ha
  first
  | exact ⟨⟨σ x, (NumberField.RingOfIntegers.isIntegral_coe x).map σ.toIntAlgHom⟩, rfl⟩
  | exact ⟨⟨σ x, x.2.map σ.toIntAlgHom⟩, rfl⟩
  | exact ⟨NumberField.RingOfIntegers.mapRingHom σ x, rfl⟩

lemma locGlob (x : E) (h : ∀ P : Ideal (𝓞 E), P.IsPrime → ∃ y : 𝓞 E, y ∉ P ∧ IsInt ((y : E) * x)) :
    IsInt x := by
  let I : Ideal (𝓞 E) :=
    { carrier := {y | IsInt ((y : E) * x)}
      add_mem' := fun {a b} ha hb => by
        show IsInt (((a + b : 𝓞 E) : E) * x)
        convert isInt_add ha hb using 1
        push_cast; ring
      zero_mem' := by
        show IsInt (((0 : 𝓞 E) : E) * x)
        convert isInt_coe (0 : 𝓞 E) using 1
        push_cast; ring
      smul_mem' := fun c y hy => by
        show IsInt (((c • y : 𝓞 E) : E) * x)
        convert isInt_mul (isInt_coe c) hy using 1
        rw [smul_eq_mul]; push_cast; ring }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨y, hy, hyx⟩ := h M hM.isPrime
    exact hy (hIM (show y ∈ I from hyx))
  have h1 : (1 : 𝓞 E) ∈ I := by rw [hI]; exact Submodule.mem_top
  have h1' : IsInt (((1 : 𝓞 E) : E) * x) := h1
  convert h1' using 1
  push_cast; ring

lemma divGlob (e : E) (N : ℕ) (hN : 0 < N) (he : IsInt e)
    (h : ∀ P : Ideal (𝓞 E), P.IsPrime → (N : 𝓞 E) ∈ P → LocIn P e N) :
    ∃ β : 𝓞 E, e = (N : E) * (β : E) := by
  have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hx : IsInt (e / (N : E)) := by
    apply locGlob
    intro P hP
    by_cases hNP : (N : 𝓞 E) ∈ P
    · obtain ⟨y, z, hy, hyz⟩ := h P hP hNP
      refine ⟨y, hy, ?_⟩
      convert isInt_coe z using 1
      rw [mul_div_assoc', hyz]
      field_simp
    · refine ⟨(N : 𝓞 E), hNP, ?_⟩
      convert he using 1
      push_cast
      field_simp
  obtain ⟨β, hβ⟩ := hx
  refine ⟨β, ?_⟩
  rw [hβ]
  field_simp

end IntegralityLocalGlobal

open IntegralityLocalGlobal

private theorem exists_not_mem_prime_mul_eq_of_locIn {E : Type} [Field E] [NumberField E] (σ : E →+* E) (M M' g : ℕ) (u e : E)
    (hM : 0 < M) (he : e = (g : E) ^ 2 * ((M' : E) * u * σ u / (M : E)))
    (hu : ∀ P : Ideal (𝓞 E), P.IsPrime → (M : 𝓞 E) ∈ P → LocIn P u M)
    (P : Ideal (𝓞 E)) (hP : P.IsPrime) (hMP : (M : 𝓞 E) ∈ P) :
    ∃ y z : 𝓞 E, y ∉ P ∧ (y : E) * e = (M : E) * (M' : E) * (g : E) ^ 2 * (z : E) := by
  have hM0 : (M : E) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  let f : 𝓞 E →+* 𝓞 E := NumberField.RingOfIntegers.mapRingHom σ
  have hf : ∀ y : 𝓞 E, ((f y : 𝓞 E) : E) = σ (y : E) := fun y => rfl
  have hQ : (P.comap f).IsPrime := by
    haveI := hP
    first
    | exact Ideal.comap_isPrime f P
    | exact Ideal.IsPrime.comap f
    | infer_instance
  have hMQ : (M : 𝓞 E) ∈ P.comap f := by
    rw [Ideal.mem_comap, map_natCast]; exact hMP
  obtain ⟨y1, z1, hy1, h1⟩ := hu P hP hMP
  obtain ⟨y2, z2, hy2, h2⟩ := hu _ hQ hMQ
  have h2' : ((f y2 : 𝓞 E) : E) * σ u = (M : E) * ((f z2 : 𝓞 E) : E) := by
    have h3 := congrArg σ h2
    rw [map_mul, map_mul, map_natCast] at h3
    rw [hf, hf]; exact h3
  have hE : e * (M : E) = (g : E) ^ 2 * ((M' : E) * u * σ u) := by
    rw [he]
    first
    | rw [mul_div_assoc', div_mul_cancel₀ _ hM0]
    | field_simp
  have c1 : ((y1 * f y2 : 𝓞 E) : E) = (y1 : E) * ((f y2 : 𝓞 E) : E) := by
    first | rfl | (push_cast; rfl) | simp
  have c2 : ((z1 * f z2 : 𝓞 E) : E) = (z1 : E) * ((f z2 : 𝓞 E) : E) := by
    first | rfl | (push_cast; rfl) | simp
  refine ⟨y1 * f y2, z1 * f z2, ?_, ?_⟩
  · intro hmem
    rcases hP.mem_or_mem hmem with h | h
    · exact hy1 h
    · exact hy2 (Ideal.mem_comap.mpr h)
  · rw [c1, c2]
    apply mul_right_cancel₀ hM0
    linear_combination ((y1 : E) * ((f y2 : 𝓞 E) : E)) * hE
      + ((g : E) ^ 2 * (M' : E) * (((f y2 : 𝓞 E) : E) * σ u)) * h1
      + ((g : E) ^ 2 * (M' : E) * (M : E) * (z1 : E)) * h2'

theorem s_integrality : Formalism.HermitianLatticeCounting.LocalIntegralStructure.SInt := by
  intro E _ _ σ T T' g s b c hT hT' hs1 hs2 hgb hgc hc hb
  have hT0 : (T : E) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  have hTT : 0 < T * T' := Nat.mul_pos hT hT'
  have e1 : (g : E) ^ 2 * s = (g : E) ^ 2 * ((T' : E) * c * σ c / (T : E)) := by rw [hs1]
  have e2 : (g : E) ^ 2 * s = (g : E) ^ 2 * ((T : E) * b * σ b / (T' : E)) := by rw [hs2]
  have hint : IsInt ((g : E) ^ 2 * s) := by
    apply locGlob
    intro P hP
    by_cases hTP : (T : 𝓞 E) ∈ P
    · obtain ⟨y, z, hy, hyz⟩ := exists_not_mem_prime_mul_eq_of_locIn σ T T' g c _ hT e1 hc P hP hTP
      refine ⟨y, hy, ?_⟩
      rw [hyz]
      convert isInt_coe ((T : 𝓞 E) * (T' : 𝓞 E) * (g : 𝓞 E) ^ 2 * z) using 1
      push_cast; ring
    · refine ⟨(T : 𝓞 E), hTP, ?_⟩
      have hh := isInt_mul (isInt_mul (isInt_coe (T' : 𝓞 E)) hgc) (isInt_map σ hgc)
      convert hh using 1
      rw [hs1, map_mul, map_natCast]
      push_cast
      first
      | (rw [mul_div_assoc', mul_div_assoc', mul_div_cancel_left₀ _ hT0]; ring)
      | (field_simp; ring)
      | field_simp
  have hloc : ∀ P : Ideal (𝓞 E), P.IsPrime → ((T * T' : ℕ) : 𝓞 E) ∈ P →
      LocIn P ((g : E) ^ 2 * s) (T * T') := by
    intro P hP hmem
    rw [Nat.cast_mul] at hmem
    unfold LocIn
    rcases hP.mem_or_mem hmem with h | h
    · obtain ⟨y, z, hy, hyz⟩ := exists_not_mem_prime_mul_eq_of_locIn σ T T' g c _ hT e1 hc P hP h
      refine ⟨y, (g : 𝓞 E) ^ 2 * z, hy, ?_⟩
      rw [hyz]; push_cast; ring
    · obtain ⟨y, z, hy, hyz⟩ := exists_not_mem_prime_mul_eq_of_locIn σ T' T g b _ hT' e2 hb P hP h
      refine ⟨y, (g : 𝓞 E) ^ 2 * z, hy, ?_⟩
      rw [hyz]; push_cast; ring
  obtain ⟨β, hβ⟩ := divGlob _ (T * T') hTT hint hloc
  refine ⟨β, ?_⟩
  rw [hβ]; push_cast; ring

namespace IntegralityLocalGlobal

lemma formEq (a b c d : ℂ) (T T' : ℝ)
    (h : ∀ u v : ℂ, T * ‖a * u + b * v‖ ^ 2 - T' * ‖c * u + d * v‖ ^ 2 = T * ‖u‖ ^ 2 - T' * ‖v‖ ^ 2) :
    T ^ 2 * ‖b‖ ^ 2 = T' ^ 2 * ‖c‖ ^ 2 := by
  have h1 := h 1 0
  have h2 := h 0 1
  have h3 := h 1 1
  have h4 := h 1 Complex.I
  first
  | simp only [← Complex.normSq_eq_norm_sq] at h1 h2 h3 h4 ⊢
  | simp only [Complex.sq_norm] at h1 h2 h3 h4 ⊢
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im, Complex.I_re,
    Complex.I_im] at h1 h2 h3 h4 ⊢
  linear_combination
    (T * (a.re * b.re + a.im * b.im) + T' * (c.re * d.re + c.im * d.im)) / 2 * (h3 - h1 - h2)
    + (T * (a.im * b.re - a.re * b.im) + T' * (c.im * d.re - c.re * d.im)) / 2 * (h4 - h1 - h2)
    - T * (b.re * b.re + b.im * b.im) * h1 - T' * (c.re * c.re + c.im * c.im) * h2

end IntegralityLocalGlobal

theorem theorem_B_statement : Formalism.HermitianLatticeCounting.LocalIntegralStructure.ThmB := by
  intro E _ _ σ hσ hcx T T' g a b c d x hT hT' hg hiso hZZ hloc hx hxw
  have hTpos : 0 < T := by omega
  have hT'pos : 0 < T' := by omega
  have hTr : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hT'r : (0 : ℝ) < T' := by exact_mod_cast hT'pos
  have hgr : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hm : ∀ w : InfinitePlace E, w.mult = 2 := fun w =>
    NumberField.InfinitePlace.mult_isComplex ⟨w, hcx w⟩
  have hn : Module.finrank ℚ E = 2 * Fintype.card (InfinitePlace E) := by
    rw [← NumberField.InfinitePlace.sum_mult_eq]
    simp only [hm, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  have hne : Nonempty (InfinitePlace E) := by
    first
    | infer_instance
    | (apply Fintype.card_pos_iff.mp
       have := Module.finrank_pos (R := ℚ) (M := E)
       omega)
  obtain ⟨w0⟩ := hne
  have hcard : 1 ≤ Fintype.card (InfinitePlace E) := Fintype.card_pos_iff.mpr ⟨w0⟩
  have hnw : ∀ (w : InfinitePlace E) (y : E), w y = ‖w.embedding y‖ := fun w y =>
    (NumberField.InfinitePlace.norm_embedding_eq w y).symm
  have hI : ∀ y : 𝓞 E, IsInt (y : E) := fun y => by unfold IsInt; exact ⟨y, rfl⟩
  have hm1 : IsInt (-1 : E) := by simpa using hI (-1)
  have h1 : IsInt (1 : E) := by simpa using hI 1
  have normge : ∀ β : 𝓞 E, β ≠ 0 → 1 ≤ ∏ w : InfinitePlace E, (w (β : E)) ^ 2 := by
    intro β hβ
    have hp := NumberField.InfinitePlace.prod_eq_abs_norm (β : E)
    simp only [hm] at hp
    rw [hp, ← Algebra.coe_norm_int]
    have hn0 : Algebra.norm ℤ β ≠ 0 := Algebra.norm_ne_zero_iff.mpr hβ
    have h2 : (1 : ℤ) ≤ |Algebra.norm ℤ β| := Int.one_le_abs hn0
    exact_mod_cast h2
  have hwn : ∀ w : InfinitePlace E,
      (T : ℝ) ^ 2 * ‖w.embedding b‖ ^ 2 = (T' : ℝ) ^ 2 * ‖w.embedding c‖ ^ 2 := fun w =>
    formEq _ _ _ _ _ _ (hiso w.embedding)
  have zz := integer_group_preservation E g a b c d hZZ
  have unit1 : ∀ (y : E) (N : ℕ), 3 ≤ N → IsInt (y - 1) →
      (∀ P : Ideal (𝓞 E), P.IsPrime → (N : 𝓞 E) ∈ P → LocIn P (y - 1) N) →
      (∀ w : InfinitePlace E, ‖w.embedding y‖ = 1) → y = 1 := by
    intro y N hN hi hl hy
    obtain ⟨β, hβ⟩ := divGlob (y - 1) N (by omega) hi hl
    by_contra hne
    have hβ0 : β ≠ 0 := by
      rintro rfl
      apply hne
      have h0 : y - 1 = 0 := by rw [hβ]; simp
      exact sub_eq_zero.mp h0
    have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have hb : ∀ w : InfinitePlace E, (w (β : E)) ^ 2 ≤ 4 / 9 := by
      intro w
      have h5 : w.embedding y - 1 = (N : ℂ) * w.embedding (β : E) := by
        rw [← map_one w.embedding, ← map_sub, hβ, map_mul, map_natCast]
      have e1 : (N : ℝ) * ‖w.embedding (β : E)‖ = ‖w.embedding y - 1‖ := by
        rw [h5, norm_mul]
        simp
      have e2 : ‖w.embedding y - 1‖ ≤ 2 := by
        calc ‖w.embedding y - 1‖ ≤ ‖w.embedding y‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by rw [hy w, norm_one]; norm_num
      have e3 : 0 ≤ ‖w.embedding (β : E)‖ := norm_nonneg _
      have e4 : ‖w.embedding (β : E)‖ ≤ 2 / 3 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hNr) e3]
      rw [hnw]
      nlinarith [mul_nonneg e3 (sub_nonneg.mpr e4)]
    have hprod : ∏ w : InfinitePlace E, (w (β : E)) ^ 2 ≤ ∏ _w : InfinitePlace E, (4 / 9 : ℝ) :=
      Finset.prod_le_prod (fun w _ => sq_nonneg _) (fun w _ => hb w)
    rw [Finset.prod_const, Finset.card_univ] at hprod
    have h49 : (4 / 9 : ℝ) ^ Fintype.card (InfinitePlace E) ≤ 4 / 9 :=
      pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith [normge β hβ0]
  by_cases hc0 : c = 0
  · left
    have hb0 : b = 0 := by
      have h := hwn w0
      rw [hc0, map_zero, norm_zero] at h
      have h2 : ‖w0.embedding b‖ ^ 2 = 0 :=
        mul_left_cancel₀ (pow_ne_zero 2 hTr.ne') (by rw [h]; ring)
      have h3 : w0.embedding b = 0 := norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)
      exact (map_eq_zero_iff _ w0.embedding.injective).mp h3
    have ha1 : ∀ w : InfinitePlace E, ‖w.embedding a‖ = 1 := by
      intro w
      have h := hiso w.embedding 1 0
      rw [hb0, hc0] at h
      simp only [map_zero, mul_one, mul_zero, zero_mul, add_zero, zero_add, norm_zero, norm_one] at h
      have h2 : (T : ℝ) * (‖w.embedding a‖ ^ 2 - 1) = 0 := by linear_combination h
      have h3 := (mul_eq_zero.mp h2).resolve_left hTr.ne'
      nlinarith [norm_nonneg (w.embedding a)]
    have hd1 : ∀ w : InfinitePlace E, ‖w.embedding d‖ = 1 := by
      intro w
      have h := hiso w.embedding 0 1
      rw [hb0, hc0] at h
      simp only [map_zero, mul_one, mul_zero, zero_mul, add_zero, zero_add, norm_zero, norm_one] at h
      have h2 : (T' : ℝ) * (‖w.embedding d‖ ^ 2 - 1) = 0 := by linear_combination -h
      have h3 := (mul_eq_zero.mp h2).resolve_left hT'r.ne'
      nlinarith [norm_nonneg (w.embedding d)]
    have ha : a = 1 := unit1 a T hT
      (by convert isInt_add zz.2.2.2.2.1 hm1 using 1; rw [hb0]; ring)
      (fun P hP h => (hloc P hP (Or.inl h)).1) ha1
    have hd : d = 1 := unit1 d T' hT'
      (by convert isInt_mul hm1 (isInt_add zz.2.2.2.2.2 h1) using 1; rw [hc0]; ring)
      (fun P hP h => (hloc P hP (Or.inr h)).2.2.2) hd1
    exact ⟨ha, hb0, hc0, hd⟩
  · right
    obtain ⟨s, hs1⟩ : ∃ s : E, s = (T' : E) * c * σ c / (T : E) := ⟨_, rfl⟩
    have hs2 : s = (T : E) * b * σ b / (T' : E) := by
      rw [hs1]
      apply w0.embedding.injective
      have hconj : ∀ z : E,
          w0.embedding z * w0.embedding (σ z) = ((‖w0.embedding z‖ ^ 2 : ℝ) : ℂ) := by
        intro z
        rw [hσ, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp only [map_div₀, map_mul, map_natCast]
      rw [mul_assoc, mul_assoc, hconj, hconj]
      have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hTpos.ne'
      have hT'c : (T' : ℂ) ≠ 0 := by exact_mod_cast hT'pos.ne'
      rw [div_eq_div_iff hTc hT'c]
      have h' := congrArg (fun r : ℝ => (r : ℂ)) (hwn w0)
      push_cast at h' ⊢
      linear_combination -h'
    obtain ⟨β, hβ⟩ := s_integrality E σ T T' g s b c hTpos hT'pos hs1 hs2 zz.2.1 zz.2.2.1
      (fun P hP h => (hloc P hP (Or.inl h)).2.1) (fun P hP h => (hloc P hP (Or.inr h)).2.2.1)
    have hs0 : s ≠ 0 := by
      rw [hs1]
      have hσc : σ c ≠ 0 := fun h => hc0 (σ.injective (by rw [h, map_zero]))
      have hT0 : (T : E) ≠ 0 := Nat.cast_ne_zero.mpr hTpos.ne'
      have hT'0 : (T' : E) ≠ 0 := Nat.cast_ne_zero.mpr hT'pos.ne'
      exact div_ne_zero (mul_ne_zero (mul_ne_zero hT'0 hc0) hσc) hT0
    have hβ0 : β ≠ 0 := by
      rintro rfl
      have hg0 : (g : E) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have h0 : (g : E) ^ 2 * s = 0 := by rw [hβ]; simp
      exact hs0 ((mul_eq_zero.mp h0).resolve_left (pow_ne_zero 2 hg0))
    set q : ℝ := (T : ℝ) * T' / (g : ℝ) ^ 2 with hq_def
    have hq : 0 < q := div_pos (mul_pos hTr hT'r) (pow_pos hgr 2)
    have key : ∀ w : InfinitePlace E, q ^ 2 * (w (β : E)) ^ 2 ≤ (x w ^ 2) ^ 2 := by
      intro w
      have A : (g : ℝ) ^ 2 * ‖w.embedding s‖ = (T : ℝ) * T' * ‖w.embedding (β : E)‖ := by
        have h := congrArg (fun y => ‖w.embedding y‖) hβ
        simpa [map_mul, map_pow, map_natCast, norm_mul, norm_pow] using h
      have B : ‖w.embedding s‖ = (T' : ℝ) * ‖w.embedding c‖ ^ 2 / T := by
        rw [hs1]
        simp [hσ, norm_div] <;> ring
      have C := hxw w
      rw [hnw w c] at C
      have hs_le : ‖w.embedding s‖ ≤ x w ^ 2 := by rw [B]; exact C
      have hs_eq : ‖w.embedding s‖ = q * ‖w.embedding (β : E)‖ := by
        rw [hq_def, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hgr.ne')]
        linear_combination A
      rw [hnw w, ← mul_pow, ← hs_eq]
      first
      | exact pow_le_pow_left (norm_nonneg _) hs_le 2
      | exact pow_le_pow_left₀ (norm_nonneg _) hs_le 2
      | nlinarith [norm_nonneg (w.embedding s)]
    apply complex_multiplication_root E q x hcx hq hx
    simp only [hm]
    rw [hn, pow_mul]
    have hprod : ∏ w : InfinitePlace E, q ^ 2 * (w (β : E)) ^ 2 ≤
        ∏ w : InfinitePlace E, (x w ^ 2) ^ 2 :=
      Finset.prod_le_prod (fun w _ => by positivity) (fun w _ => key w)
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] at hprod
    have hqn : 0 ≤ (q ^ 2) ^ Fintype.card (InfinitePlace E) := by positivity
    have h3 := mul_le_mul_of_nonneg_left (normge β hβ0) hqn
    rw [mul_one] at h3
    linarith

end Formalism.HermitianLatticeCounting.P
