import Mathlib

namespace GlobalTheory.LatticeCovolumeL2

open NumberField Matrix

theorem det_compl {n : Type} [Fintype n] [DecidableEq n] (M Y : Matrix n n ℝ) (h : M * Y = 1) (p : n → Prop)
    [DecidablePred p] :
    (toSquareBlockProp Y (fun k => ¬ p k)).det = (toSquareBlockProp M p).det * Y.det := by
  let Z : Matrix n n ℝ := fun i k => if p k then (1 : Matrix n n ℝ) i k else Y i k
  have hMZ : ∀ i k, (M * Z) i k = if p k then M i k else (1 : Matrix n n ℝ) i k := by
    intro i k
    by_cases hk : p k
    · simp only [hk, if_true]
      rw [Matrix.mul_apply]
      simp [Z, hk, Matrix.one_apply]
    · simp only [hk, if_false]
      rw [← h, Matrix.mul_apply, Matrix.mul_apply]
      simp [Z, hk]
  have hZ : Z.det = (toSquareBlockProp Y (fun k => ¬ p k)).det := by
    rw [Matrix.twoBlockTriangular_det Z p]
    · have h1 : toSquareBlockProp Z p = 1 := by
        ext i j
        change Z i j = _
        simp [Z, j.2, Matrix.one_apply, Subtype.ext_iff]
      have h2 : toSquareBlockProp Z (fun k => ¬ p k) = toSquareBlockProp Y (fun k => ¬ p k) := by
        ext i j
        change Z i j = Y i j
        simp [Z, j.2]
      rw [h1, h2, det_one, one_mul]
    · intro i hi j hj
      have hij : i ≠ j := fun e => hi (e ▸ hj)
      simp [Z, hj, Matrix.one_apply, hij]
  have hMZd : (M * Z).det = (toSquareBlockProp M p).det := by
    rw [← det_transpose, Matrix.twoBlockTriangular_det (M * Z)ᵀ p]
    · have h1 : toSquareBlockProp (M * Z)ᵀ p = (toSquareBlockProp M p)ᵀ := by
        ext i j
        change (M * Z) j i = M j i
        rw [hMZ]
        simp [i.2]
      have h2 : toSquareBlockProp (M * Z)ᵀ (fun k => ¬ p k) = 1 := by
        ext i j
        change (M * Z) j i = if i = j then 1 else 0
        rw [hMZ]
        simp [i.2, Matrix.one_apply, Subtype.ext_iff, eq_comm]
      rw [h1, h2, det_one, mul_one, det_transpose]
    · intro i hi j hj
      have hji : j ≠ i := fun e => hi (e ▸ hj)
      simp [hMZ, hi, hji]
  have hdet : M.det * Y.det = 1 := by rw [← det_mul, h, det_one]
  rw [← hMZd, det_mul, hZ]
  linear_combination (-(toSquareBlockProp Y (fun k => ¬ p k)).det) * hdet

variable {E : Type} [Field E] [NumberField E]

noncomputable def cmEquiv (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) :
    Ψ ⊕ Ψ ≃ (E →+* ℂ) :=
  Equiv.ofBijective (Sum.elim (fun τ => τ.1) (fun τ => ComplexEmbedding.conjugate τ.1)) <| by
    have cc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
      fun τ => star_star τ
    constructor
    · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
      · exact congrArg _ (Subtype.ext h)
      · exact absurd (h ▸ a.2) ((hΨ _).1 b.2)
      · exact absurd (h ▸ b.2) ((hΨ _).1 a.2)
      · have := congrArg ComplexEmbedding.conjugate h
        rw [cc, cc] at this
        exact congrArg _ (Subtype.ext this)
    · intro τ
      by_cases h : τ ∈ Ψ
      · exact ⟨.inl ⟨τ, h⟩, rfl⟩
      · refine ⟨.inr ⟨ComplexEmbedding.conjugate τ, ?_⟩, cc τ⟩
        by_contra h'
        exact h ((hΨ τ).2 h')

theorem det_gram {ι : Type} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = Module.finrank ℚ E)
    (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ)
    (a : ι → E) (s : Ψ → ℝ) (G : Matrix ι ι ℝ)
    (hG : ∀ k l, G k l = ∑ τ : Ψ, (τ.1 (a k) * (starRingEnd ℂ) (τ.1 (a l))).re * s τ) :
    G.det = |((Algebra.discr ℚ a : ℚ) : ℝ)| * (∏ τ, (s τ / 2)) ^ 2 := by
  let κ := Ψ ⊕ Ψ
  let e1 : κ ≃ (E →+* ℂ) := cmEquiv Ψ hΨ
  have hcard : Fintype.card ι = Fintype.card κ := by
    rw [hι, Fintype.card_congr e1, NumberField.Embeddings.card]
  let f : ι ≃ κ := Fintype.equivOfCardEq hcard
  let e2 : ι ≃ (E →ₐ[ℚ] ℂ) := (f.trans e1).trans (RingHom.equivRatAlgHom E ℂ)
  let B : Matrix ι ι ℂ := Algebra.embeddingsMatrixReindex ℚ ℂ a e2
  have hB : ∀ k j, B k j = e1 (f j) (a k) := fun k j => rfl
  let d : κ → ℂ := fun σ => Sum.elim (fun τ => ((s τ : ℂ) / 2)) (fun τ => ((s τ : ℂ) / 2)) σ
  let Dm : Matrix ι ι ℂ := Matrix.diagonal (fun j => d (f j))
  let Cm : Matrix ι ι ℂ := (B.map (starRingEnd ℂ))ᵀ
  have hGm : G.map (fun x : ℝ => (x : ℂ)) = B * Dm * Cm := by
    ext k l
    rw [Matrix.map_apply, hG k l, Matrix.mul_apply]
    simp only [Dm, Cm, Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply, hB]
    rw [Equiv.sum_comp f (fun σ => e1 σ (a k) * d σ * (starRingEnd ℂ) (e1 σ (a l))),
      Fintype.sum_sum_type]
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have he1l : e1 (Sum.inl τ) = τ.1 := rfl
    have he1r : e1 (Sum.inr τ) = ComplexEmbedding.conjugate τ.1 := rfl
    simp only [he1l, he1r, d, Sum.elim_inl, Sum.elim_inr, ComplexEmbedding.conjugate_coe_eq,
      Complex.conj_conj]
    rw [Complex.re_eq_add_conj, map_mul, Complex.conj_conj]
    ring
  have hdisc : algebraMap ℚ ℂ (Algebra.discr ℚ a) = B.det ^ 2 :=
    Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ a e2
  have hdetG : ((G.det : ℝ) : ℂ) = B.det * (starRingEnd ℂ) B.det * (∏ τ, ((s τ : ℂ) / 2)) ^ 2 := by
    have h1 : ((G.det : ℝ) : ℂ) = (G.map (fun x : ℝ => (x : ℂ))).det :=
      RingHom.map_det Complex.ofRealHom G
    have h2 : (B.map (starRingEnd ℂ)).det = (starRingEnd ℂ) B.det := (RingHom.map_det _ B).symm
    rw [h1, hGm, det_mul, det_mul, det_diagonal, det_transpose, h2,
      Equiv.prod_comp f d, Fintype.prod_sum_type]
    simp only [d, Sum.elim_inl, Sum.elim_inr]
    ring
  have hn : ((|((Algebra.discr ℚ a : ℚ) : ℝ)| : ℝ) : ℂ) = B.det * (starRingEnd ℂ) B.det := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← norm_pow, ← hdisc]
    congr 1
    rw [eq_ratCast, Complex.norm_ratCast]
  apply Complex.ofReal_injective
  rw [hdetG, Complex.ofReal_mul, hn, Complex.ofReal_pow, Complex.ofReal_prod]
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat]

theorem discr_le {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ι → E)
    (h : ∀ i, b i ∈ Submodule.span ℤ (Set.range a)) (hb : Algebra.discr ℚ b ≠ 0) :
    Algebra.discr ℚ a ≠ 0 ∧ |Algebra.discr ℚ a| ≤ |Algebra.discr ℚ b| := by
  have hc : ∀ i, ∃ c : ι → ℤ, ∑ j, c j • a j = b i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun (R := ℤ)).1 (h i)
  choose c hc using hc
  let P : Matrix ι ι ℤ := Matrix.of c
  let Pq : Matrix ι ι ℚ := P.map (Int.cast)
  have hb' : Pq.map (algebraMap ℚ E) *ᵥ a = b := by
    funext i
    rw [← hc i]
    simp [Matrix.mulVec, dotProduct, Pq, P, zsmul_eq_mul, map_intCast]
  have hd := Algebra.discr_of_matrix_mulVec a Pq
  rw [hb'] at hd
  have hPq : Pq.det = (P.det : ℚ) := by
    exact (RingHom.map_det (Int.castRingHom ℚ) P).symm
  rw [hPq] at hd
  have hP0 : P.det ≠ 0 := by
    intro h0
    apply hb
    rw [hd, h0]
    simp
  refine ⟨fun h0 => hb (by rw [hd, h0, mul_zero]), ?_⟩
  rw [hd, abs_mul]
  have h1 : (1 : ℚ) ≤ |((P.det : ℤ) : ℚ) ^ 2| := by
    rw [abs_pow]
    have : (1 : ℤ) ≤ |P.det| := Int.one_le_abs hP0
    exact one_le_pow₀ (by exact_mod_cast this)
  nlinarith [abs_nonneg (Algebra.discr ℚ a)]

theorem finrank_int_le {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite ℤ X]
    (h : Module.finrank (𝓞 E) X = 1) : Module.finrank ℤ X ≤ Module.finrank ℚ E := by
  have : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) X
  obtain ⟨x, hx⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := X) (n := 1) h.ge
  have hx0 : ∀ c : 𝓞 E, c • x 0 = 0 → c = 0 := by
    intro c hc
    exact linearIndependent_iff'.1 hx Finset.univ (fun _ => c) (by simpa using hc) 0 (Finset.mem_univ _)
  have key : ∀ y : X, ∃ N : ℤ, N ≠ 0 ∧ ∃ α : 𝓞 E, N • y = α • x 0 := by
    intro y
    have hdep : ¬ LinearIndependent (𝓞 E) ![x 0, y] := by
      intro hli
      have := hli.fintype_card_le_finrank
      rw [h] at this
      simp at this
    rw [LinearIndependent.pair_iff] at hdep
    push Not at hdep
    obtain ⟨s, t, hst, hne⟩ := hdep
    have ht : t ≠ 0 := by
      intro ht0
      rw [ht0, zero_smul, add_zero] at hst
      exact hne (hx0 s hst) ht0
    have hI := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) (I := Ideal.span {t}) ht
      (Ideal.mem_span_singleton_self t) (NumberField.RingOfIntegers.isIntegral t)
    obtain ⟨N, hN, hN0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hN
    obtain ⟨c, hc⟩ := hN
    refine ⟨N, hN0, -(c * s), ?_⟩
    have hty : t • y = -(s • x 0) := eq_neg_of_add_eq_zero_right hst
    rw [← algebraMap_smul (𝓞 E) N y, hc, mul_comm t c, mul_smul, hty]
    simp [smul_neg, mul_smul]
  obtain ⟨yv, hy⟩ := exists_linearIndependent_of_le_finrank (R := ℤ) (M := X) (le_refl (Module.finrank ℤ X))
  choose N hN α hα using fun i => key (yv i)
  let N0 : ℤ := ∏ i, N i
  have hN0 : N0 ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hN i
  let φ : 𝓞 E →ₗ[ℤ] X := (LinearMap.toSpanSingleton (𝓞 E) X (x 0)).restrictScalars ℤ
  let β : Fin (Module.finrank ℤ X) → 𝓞 E := fun i => ((∏ j ∈ Finset.univ.erase i, N j : ℤ) : 𝓞 E) * α i
  have hβ : ∀ i, φ (β i) = N0 • yv i := by
    intro i
    show (((∏ j ∈ Finset.univ.erase i, N j : ℤ) : 𝓞 E) * α i) • x 0 = N0 • yv i
    rw [mul_smul, ← hα i, Int.cast_smul_eq_zsmul, smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have hli : LinearIndependent ℤ (φ ∘ β) := by
    have hfun : φ ∘ β = fun i => N0 • yv i := funext hβ
    rw [hfun]
    rw [linearIndependent_iff'] at hy ⊢
    intro s g hg i hi
    have := hy s (fun j => g j * N0) (by simpa [smul_smul] using hg) i hi
    exact (mul_eq_zero.1 this).resolve_right hN0
  have := (LinearIndependent.of_comp φ hli).fintype_card_le_finrank
  simpa [NumberField.RingOfIntegers.rank] using this

theorem exists_line_basis {La ι V : Type} [AddCommGroup La] [Module (𝓞 E) La] [Fintype ι]
    [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (ψ : La →ₗ[𝓞 E] V) (hψ : Function.Injective ψ) (T : La → Prop) (b : ι → La)
    (hT : ∀ (c : 𝓞 E) v, T v → T (c • v)) (hsat : ∀ (m : ℤ) v, m ≠ 0 → T (m • v) → T v)
    (hb : ∀ v, T v → v ∈ Submodule.span ℤ (Set.range b)) (hι : Fintype.card ι ≤ Module.finrank ℚ E)
    (t : La) (ht : T t) (h0 : ψ t ≠ 0) :
    Fintype.card ι = Module.finrank ℚ E ∧ ∃ a : ι → E, (∀ k, ψ (b k) = a k • ψ t) ∧
      ∀ e : E, e • ψ t ∈ LinearMap.range ψ ↔ e ∈ Submodule.span ℤ (Set.range a) := by
  have hinj : ∀ c : 𝓞 E, c • t = 0 → c = 0 := by
    intro c hc
    have h1 := congrArg ψ hc
    rw [map_smul, map_zero, ← algebraMap_smul E c (ψ t)] at h1
    rcases smul_eq_zero.1 h1 with h2 | h2
    · exact (map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).1 h2
    · exact absurd h2 h0
  let S : Submodule ℤ La := Submodule.span ℤ (Set.range b)
  have hSfin : Module.Finite ℤ S := Module.Finite.span_of_finite ℤ (Set.finite_range b)
  have hS : ∀ {κ : Type} [Fintype κ] (w : κ → La), (∀ i, w i ∈ S) → LinearIndependent ℤ w →
      Fintype.card κ ≤ Fintype.card ι := by
    intro κ _ w hw hli
    let w' : κ → S := fun i => ⟨w i, hw i⟩
    have hli' : LinearIndependent ℤ w' := LinearIndependent.of_comp S.subtype hli
    exact hli'.fintype_card_le_finrank.trans (finrank_range_le_card b)
  obtain ⟨β, hβ⟩ := exists_linearIndependent_of_le_finrank (R := ℤ) (M := 𝓞 E)
    (le_of_eq (NumberField.RingOfIntegers.rank E).symm)
  let φ : 𝓞 E →ₗ[ℤ] La := (LinearMap.toSpanSingleton (𝓞 E) La t).restrictScalars ℤ
  have hφ : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    exact fun c hc => hinj c hc
  have hβt : LinearIndependent ℤ (φ ∘ β) := hβ.map' φ hφ
  have hβS : ∀ j, (φ ∘ β) j ∈ S := fun j => hb _ (hT _ _ ht)
  have hcard : Fintype.card ι = Module.finrank ℚ E := by
    refine le_antisymm hι ?_
    simpa using hS (φ ∘ β) hβS hβt
  have hline : ∀ k, ∃ e : E, ψ (b k) = e • ψ t := by
    intro k
    let w : Option (Fin (Module.finrank ℚ E)) → La := fun o => Option.elim o (b k) (φ ∘ β)
    have hw : ∀ o, w o ∈ S := by
      intro o
      cases o with
      | none => exact Submodule.subset_span ⟨k, rfl⟩
      | some j => exact hβS j
    have hnd : ¬ LinearIndependent ℤ w := by
      intro hli
      have := hS w hw hli
      simp [hcard] at this
    obtain ⟨g, hg, o, ho⟩ := Fintype.not_linearIndependent_iff.1 hnd
    rw [Fintype.sum_option] at hg
    have hgn : g none ≠ 0 := by
      intro hz
      rw [hz, zero_smul, zero_add] at hg
      have := Fintype.linearIndependent_iff.1 hβt (fun j => g (some j)) hg
      cases o with
      | none => exact ho hz
      | some j => exact ho (this j)
    let γ : 𝓞 E := -∑ j, (g (some j) : 𝓞 E) * β j
    have hmb : g none • b k = γ • t := by
      have h1 : g none • b k = -∑ j, g (some j) • φ (β j) := eq_neg_of_add_eq_zero_left hg
      rw [h1]
      simp only [γ, φ, LinearMap.restrictScalars_apply, LinearMap.toSpanSingleton_apply, neg_smul,
        Finset.sum_smul, mul_smul, Int.cast_smul_eq_zsmul]
    refine ⟨((g none : ℤ) : E)⁻¹ * algebraMap (𝓞 E) E γ, ?_⟩
    have h2 := congrArg ψ hmb
    rw [map_zsmul, map_smul, ← algebraMap_smul E γ (ψ t), ← Int.cast_smul_eq_zsmul E] at h2
    have hne : ((g none : ℤ) : E) ≠ 0 := by exact_mod_cast hgn
    rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hne, one_smul]
  choose a ha using hline
  refine ⟨hcard, a, ha, fun e => ⟨?_, ?_⟩⟩
  · rintro ⟨v, hv⟩
    obtain ⟨α, β', hβ'⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
    have hβ0 : β' ≠ 0 := nonZeroDivisors.ne_zero hβ'.1
    have hβE : algebraMap (𝓞 E) E β' ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 hβ0
    have h1 : β' • v = α • t := by
      apply hψ
      rw [map_smul, map_smul, hv, ← algebraMap_smul E β', ← algebraMap_smul E α, smul_smul, ← hβ'.2]
      congr 1
      field_simp
    have hI := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) (I := Ideal.span {β'}) hβ0
      (Ideal.mem_span_singleton_self β') (NumberField.RingOfIntegers.isIntegral β')
    obtain ⟨N, hN, hN0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hN
    obtain ⟨c, hc⟩ := hN
    have hTv : T v := by
      apply hsat N v hN0
      rw [← algebraMap_smul (𝓞 E) N v, hc, mul_comm β' c, mul_smul, h1, smul_smul]
      exact hT _ _ ht
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℤ)).1 (hb v hTv)
    have h2 : e • ψ t = (∑ k, g k • a k) • ψ t := by
      rw [← hv, ← hg, map_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_zsmul, ha k, smul_assoc]
    have h3 : e = ∑ k, g k • a k := smul_left_injective E h0 h2
    rw [h3]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · intro he
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℤ)).1 he
    refine ⟨∑ k, c k • b k, ?_⟩
    rw [map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, ha k, smul_assoc]

end GlobalTheory.LatticeCovolumeL2
