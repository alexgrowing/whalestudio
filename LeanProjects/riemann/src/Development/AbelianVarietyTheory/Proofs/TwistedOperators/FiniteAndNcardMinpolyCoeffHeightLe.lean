import Mathlib

open NumberField Polynomial

namespace GlobalTheory.MinpolyHeightCount

theorem finite_and_ncard_le_of_fibres {α β : Type*} {S : Set α} {T : Set β} {f : α → β}
    (hT : T.Finite) (hf : Set.MapsTo f S T) (m : ℕ)
    (hfib : ∀ t ∈ T, (S ∩ f ⁻¹' {t}).Finite ∧ (S ∩ f ⁻¹' {t}).ncard ≤ m) :
    S.Finite ∧ S.ncard ≤ m * T.ncard := by
  classical
  have hS : S.Finite := by
    refine (hT.biUnion fun t ht => (hfib t ht).1).subset fun x hx => ?_
    exact Set.mem_biUnion (hf hx) ⟨hx, rfl⟩
  refine ⟨hS, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hS, Set.ncard_eq_toFinset_card _ hT]
  refine Finset.card_le_mul_card_image_of_maps_to (f := f)
    (fun a ha => by simpa using hf (by simpa using ha)) m fun t ht => ?_
  have h := (hfib t (by simpa using ht)).2
  have e : (({a ∈ hS.toFinset | f a = t} : Finset α) : Set α) = S ∩ f ⁻¹' {t} := by
    ext a; simp
  rw [← Set.ncard_coe_finset, e]
  exact h

theorem finite_and_ncard_le_of_eval_eq_zero {L : Type*} [Field L] {S : Set L} {p : L[X]}
    (hp : p ≠ 0) (hS : ∀ x ∈ S, p.eval x = 0) : S.Finite ∧ S.ncard ≤ p.natDegree := by
  classical
  have hsub : S ⊆ (p.roots.toFinset : Set L) := fun x hx => by
    simp [Multiset.mem_toFinset, mem_roots hp, IsRoot.def, hS x hx]
  refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
  calc S.ncard ≤ (p.roots.toFinset : Set L).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = p.roots.toFinset.card := Set.ncard_coe_finset _
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := card_roots' p

theorem finite_and_ncard_le_of_fibres_roots {L β : Type*} [Field L] {S : Set L} {T : Set β}
    {f : L → β} (hT : T.Finite) (hf : Set.MapsTo f S T) (m : ℕ)
    (hfib : ∀ t ∈ T, ∃ p : L[X], p ≠ 0 ∧ p.natDegree ≤ m ∧ ∀ x ∈ S, f x = t → p.eval x = 0) :
    S.Finite ∧ S.ncard ≤ m * T.ncard := by
  refine finite_and_ncard_le_of_fibres hT hf m fun t ht => ?_
  obtain ⟨p, hp, hdeg, hroot⟩ := hfib t ht
  obtain ⟨h1, h2⟩ := finite_and_ncard_le_of_eval_eq_zero (S := S ∩ f ⁻¹' {t}) hp
    fun x hx => hroot x hx.1 hx.2
  exact ⟨h1, h2.trans hdeg⟩

section Integral

variable (K : Type) [Field K] [NumberField K]

theorem natDegree_minpoly_int_le {x : K} (hx : IsIntegral ℤ x) :
    (minpoly ℤ x).natDegree ≤ Module.finrank ℚ K := by
  rw [← (minpoly.monic hx).natDegree_map (algebraMap ℤ ℚ),
    ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hx]
  exact minpoly.natDegree_le x

theorem abs_coeff_minpoly_int_le {x : K} (hx : IsIntegral ℤ x) {R : ℝ}
    (h : ∀ φ : K →+* ℂ, ‖φ x‖ ≤ R) (i : ℕ) :
    (|(minpoly ℤ x).coeff i| : ℝ) ≤ max R 1 ^ Module.finrank ℚ K *
      (Module.finrank ℚ K).choose (Module.finrank ℚ K / 2) := by
  refine Eq.trans_le ?_ (Embeddings.coeff_bdd_of_norm_le h i)
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hx, coeff_map, eq_intCast,
    Int.norm_cast_rat, Int.norm_eq_abs]

theorem finite_and_ncard_integral_le (R : ℝ) :
    {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ R}.Finite ∧
    (({x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ R}.ncard : ℕ) : ℝ) ≤
      Module.finrank ℚ K * (2 * (max R 1 ^ Module.finrank ℚ K *
        (Module.finrank ℚ K).choose (Module.finrank ℚ K / 2)) + 3) ^
          (Module.finrank ℚ K + 1) := by
  classical
  set d := Module.finrank ℚ K with hd
  set M : ℝ := max R 1 ^ d * (d.choose (d / 2) : ℝ) with hM
  set C : ℕ := ⌈M⌉₊ with hC
  set T : Set (Fin (d + 1) → ℤ) :=
    ((Fintype.piFinset fun _ : Fin (d + 1) => Finset.Icc (-(C : ℤ)) C : Finset (Fin (d + 1) → ℤ)) :
      Set (Fin (d + 1) → ℤ)) with hTdef
  set f : K → Fin (d + 1) → ℤ := fun x i => (minpoly ℤ x).coeff i with hfdef
  have hT : T.ncard = (2 * C + 1) ^ (d + 1) := by
    rw [hTdef, Set.ncard_coe_finset, Fintype.card_piFinset, Finset.prod_const, Int.card_Icc,
      Finset.card_univ, Fintype.card_fin]
    congr 1
    omega
  have hmaps : Set.MapsTo f {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ R} T := by
    intro x hx
    rw [hTdef, Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have h1 := abs_coeff_minpoly_int_le K hx.1 hx.2 i
    have h2 : (|(minpoly ℤ x).coeff i| : ℝ) ≤ (C : ℝ) := h1.trans (Nat.le_ceil _)
    have h3 : |(minpoly ℤ x).coeff i| ≤ (C : ℤ) := by exact_mod_cast h2
    exact abs_le.mp h3
  obtain ⟨hfin, hcard⟩ := finite_and_ncard_le_of_fibres_roots (Finset.finite_toSet _) hmaps d
    (by
      intro t _
      by_cases h : ∃ x0 ∈ {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ R}, f x0 = t
      · obtain ⟨x0, hx0, hfx0⟩ := h
        refine ⟨(minpoly ℤ x0).map (algebraMap ℤ K), ((minpoly.monic hx0.1).map _).ne_zero, ?_, ?_⟩
        · rw [(minpoly.monic hx0.1).natDegree_map]
          exact natDegree_minpoly_int_le K hx0.1
        · intro y hy hfy
          have heq : minpoly ℤ y = minpoly ℤ x0 := by
            ext i
            by_cases hi : i < d + 1
            · exact congrFun (hfy.trans hfx0.symm) ⟨i, hi⟩
            · rw [coeff_eq_zero_of_natDegree_lt ((natDegree_minpoly_int_le K hy.1).trans_lt
                (by omega)), coeff_eq_zero_of_natDegree_lt
                ((natDegree_minpoly_int_le K hx0.1).trans_lt (by omega))]
          rw [eval_map_algebraMap, ← heq]
          exact minpoly.aeval ℤ y
      · refine ⟨1, one_ne_zero, by simp, fun x hx hfx => (h ⟨x, hx, hfx⟩).elim⟩)
  refine ⟨hfin, ?_⟩
  have hM0 : 0 ≤ M := by positivity
  have hC' : (C : ℝ) ≤ M + 1 := (Nat.ceil_lt_add_one hM0).le
  rw [hT] at hcard
  calc (({x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ R}.ncard : ℕ) : ℝ)
      ≤ ((d * (2 * C + 1) ^ (d + 1) : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (d : ℝ) * (2 * (C : ℝ) + 1) ^ (d + 1) := by push_cast; ring
    _ ≤ (d : ℝ) * (2 * M + 3) ^ (d + 1) := by
      have h23 : 2 * (C : ℝ) + 1 ≤ 2 * M + 3 := by linarith
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h23 _) (by positivity)

end Integral

section Height

variable {K : Type} [Field K] [NumberField K]

theorem norm_embedding_le_mulHeight₁ (φ : K →+* ℂ) (c : K) : ‖φ c‖ ≤ Height.mulHeight₁ c := by
  classical
  set w := InfinitePlace.mk φ
  have hw : w c = ‖φ c‖ := InfinitePlace.apply φ c
  rw [← hw, NumberField.mulHeight₁_eq]
  have h1 : ∀ v : InfinitePlace K, 1 ≤ max (v c) 1 ^ v.mult :=
    fun v => one_le_pow₀ (le_max_right _ _)
  calc w c ≤ max (w c) 1 := le_max_left _ _
    _ ≤ max (w c) 1 ^ w.mult := le_self_pow₀ (le_max_right _ _) w.mult_ne_zero
    _ ≤ ∏ v : InfinitePlace K, max (v c) 1 ^ v.mult := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
      exact le_mul_of_one_le_right (by positivity) (Finset.one_le_prod fun v _ => h1 v)
    _ ≤ _ := le_mul_of_one_le_right (Finset.prod_nonneg fun v _ => by positivity)
        (one_le_finprod fun _ => le_max_right _ _)

variable (K) in

theorem exists_ncard_mulHeight₁_le : ∃ (C : ℝ) (k : ℕ), ∀ B : ℝ, 1 ≤ B →
    {c : K | Height.mulHeight₁ c ≤ B}.Finite ∧
      (({c : K | Height.mulHeight₁ c ≤ B}.ncard : ℕ) : ℝ) ≤ C * B ^ k := by
  classical
  set d := Module.finrank ℚ K with hd
  refine ⟨d * (2 * (d.choose (d / 2) : ℝ) + 3) ^ (d + 1), 1 + 2 * d * (d + 1), fun B hB => ?_⟩
  refine ⟨finite_setOfPred_mulHeight₁_le K B, ?_⟩
  choose n hn0 hnle hint using fun c : K => exists_nat_le_mulHeight₁ c
  set A := {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ B ^ 2} with hAdef
  obtain ⟨hAfin, hAcard⟩ := finite_and_ncard_integral_le K (B ^ 2)
  set P : Set (ℕ × K) := (↑(Finset.Icc 1 ⌊B⌋₊) : Set ℕ) ×ˢ A with hPdef
  have hP : P.Finite := (Finset.finite_toSet _).prod hAfin
  have hle : {c : K | Height.mulHeight₁ c ≤ B}.ncard ≤ P.ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun c => (n c, (n c : K) * c)) ?_ ?_ hP
    · intro c hc
      have hc' : Height.mulHeight₁ c ≤ B := hc
      refine Set.mk_mem_prod ?_ ⟨hint c, fun φ => ?_⟩
      · rw [Finset.mem_coe, Finset.mem_Icc]
        exact ⟨Nat.one_le_iff_ne_zero.mpr (hn0 c), Nat.le_floor ((hnle c).trans hc')⟩
      · rw [map_mul, norm_mul, map_natCast, Complex.norm_natCast, sq]
        exact mul_le_mul ((hnle c).trans hc') ((norm_embedding_le_mulHeight₁ φ c).trans hc')
          (norm_nonneg _) (by linarith)
    · intro c _ c' _ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [h1] at h2
      exact mul_left_cancel₀ (by exact_mod_cast hn0 c') h2
  have hPcard : P.ncard = ⌊B⌋₊ * A.ncard := by
    rw [hPdef, Set.ncard_prod, Set.ncard_coe_finset, Nat.card_Icc, Nat.add_sub_cancel]
  have hfl : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le (by linarith)
  have hmax : max (B ^ 2) 1 = B ^ 2 := max_eq_left (by nlinarith)
  rw [hmax] at hAcard
  have hX : 1 ≤ B ^ (2 * d) := one_le_pow₀ hB
  have hch : (0 : ℝ) ≤ (d.choose (d / 2) : ℝ) := Nat.cast_nonneg _
  have hstep : 2 * ((B ^ 2) ^ d * (d.choose (d / 2) : ℝ)) + 3 ≤
      (2 * (d.choose (d / 2) : ℝ) + 3) * B ^ (2 * d) := by
    rw [← pow_mul]; nlinarith
  calc (({c : K | Height.mulHeight₁ c ≤ B}.ncard : ℕ) : ℝ) ≤ (P.ncard : ℝ) := by
        exact_mod_cast hle
    _ = (⌊B⌋₊ : ℝ) * (A.ncard : ℝ) := by rw [hPcard]; push_cast; ring
    _ ≤ B * (d * (2 * ((B ^ 2) ^ d * (d.choose (d / 2) : ℝ)) + 3) ^ (d + 1)) :=
        mul_le_mul hfl hAcard (Nat.cast_nonneg _) (by linarith)
    _ ≤ B * (d * ((2 * (d.choose (d / 2) : ℝ) + 3) * B ^ (2 * d)) ^ (d + 1)) := by
        gcongr
    _ = _ := by rw [mul_pow, ← pow_mul, pow_add B 1, pow_one]; ring

end Height

theorem finite_and_ncard_minpoly_height_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E], ∃ (C : ℝ) (k : ℕ), ∀ B : ℝ, 1 ≤ B →
      {x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.Finite ∧
      (({x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.ncard : ℕ) : ℝ) ≤
        C * B ^ k := by
  intro F E _ _ _ _ _
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨C₁, k₁, h₁⟩ := exists_ncard_mulHeight₁_le F
  set m := Module.finrank F E with hm
  refine ⟨m * C₁ ^ (m + 1), k₁ * (m + 1), fun B hB => ?_⟩
  obtain ⟨hSfin, hScard⟩ := h₁ B hB
  set S := {c : F | Height.mulHeight₁ c ≤ B} with hSdef
  set X := {x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B} with hXdef
  set T : Set (Fin (m + 1) → F) :=
    ((Fintype.piFinset fun _ : Fin (m + 1) => hSfin.toFinset : Finset (Fin (m + 1) → F)) :
      Set (Fin (m + 1) → F)) with hTdef
  set f : E → Fin (m + 1) → F := fun x j => (minpoly F x).coeff j with hfdef
  have hT : T.ncard = S.ncard ^ (m + 1) := by
    rw [hTdef, Set.ncard_coe_finset, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Set.ncard_eq_toFinset_card _ hSfin]
  have hmaps : Set.MapsTo f X T := by
    intro x hx
    rw [hTdef, Finset.mem_coe, Fintype.mem_piFinset]
    intro j
    rw [Set.Finite.mem_toFinset]
    exact hx j
  obtain ⟨hXfin, hXcard⟩ := finite_and_ncard_le_of_fibres_roots (Finset.finite_toSet _) hmaps m
    (by
      intro t _
      by_cases h : ∃ x0 ∈ X, f x0 = t
      · obtain ⟨x0, -, hfx0⟩ := h
        have hi0 : IsIntegral F x0 := Algebra.IsIntegral.isIntegral x0
        refine ⟨(minpoly F x0).map (algebraMap F E), ((minpoly.monic hi0).map _).ne_zero, ?_, ?_⟩
        · rw [(minpoly.monic hi0).natDegree_map]; exact minpoly.natDegree_le x0
        · intro y _ hfy
          have heq : minpoly F y = minpoly F x0 := by
            ext i
            by_cases hi : i < m + 1
            · exact congrFun (hfy.trans hfx0.symm) ⟨i, hi⟩
            · rw [coeff_eq_zero_of_natDegree_lt ((minpoly.natDegree_le y).trans_lt (by omega)),
                coeff_eq_zero_of_natDegree_lt ((minpoly.natDegree_le x0).trans_lt (by omega))]
          rw [eval_map_algebraMap, ← heq]
          exact minpoly.aeval F y
      · exact ⟨1, one_ne_zero, by simp, fun x hx hfx => (h ⟨x, hx, hfx⟩).elim⟩)
  refine ⟨hXfin, ?_⟩
  rw [hT] at hXcard
  have h0 : (0 : ℝ) ≤ (S.ncard : ℝ) := Nat.cast_nonneg _
  calc ((X.ncard : ℕ) : ℝ) ≤ ((m * S.ncard ^ (m + 1) : ℕ) : ℝ) := by exact_mod_cast hXcard
    _ = (m : ℝ) * (S.ncard : ℝ) ^ (m + 1) := by push_cast; ring
    _ ≤ (m : ℝ) * (C₁ * B ^ k₁) ^ (m + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hScard _) (Nat.cast_nonneg _)
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

end GlobalTheory.MinpolyHeightCount
