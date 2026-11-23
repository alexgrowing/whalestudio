import Mathlib
import Formalism.UnipotentAdelicQuotients.CyclicNormPrinciple

open NumberField IsDedekindDomain TensorProduct

namespace GlobalTheory.CyclicNormCheck

theorem norm_one_tmul_eq {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
    [Module.Finite F E] (y : E) :
    Algebra.norm K ((1 : K) ⊗ₜ[F] y) = algebraMap F K (Algebra.norm F y) := by
  rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
  congr 1
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem isUnit_of_norm_eq {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
    [Module.Finite F E] {x : F} (hx : x ≠ 0) {y : K ⊗[F] E}
    (h : Algebra.norm K y = algebraMap F K x) : IsUnit y := by
  have h0 : LinearMap.det (LinearMap.mul K (K ⊗[F] E) y) ≠ 0 := by
    have : Algebra.norm K y ≠ 0 := by rw [h]; exact (map_ne_zero _).2 hx
    simpa [Algebra.norm_apply] using this
  have hu : IsUnit (LinearMap.mul K (K ⊗[F] E) y) :=
    (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h0)
  have hs := ((Module.End.isUnit_iff _).1 hu).2
  obtain ⟨z, hz⟩ := hs 1
  exact IsUnit.of_mul_eq_one z (by simpa using hz)

theorem norm_of_root {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
    [Module.Finite F E] {a r : K} (h : r ^ Module.finrank F E = a) :
    ∃ y : K ⊗[F] E, Algebra.norm K y = a :=
  ⟨algebraMap K _ r, by rw [Algebra.norm_algebraMap, Module.finrank_baseChange, h]⟩

theorem norm_complex {F E : Type} [Field F] [Field E] [Algebra F E] [Algebra F ℂ]
    [Module.Finite F E] (a : ℂ) : ∃ y : ℂ ⊗[F] E, Algebra.norm ℂ y = a := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq a (Module.finrank_pos (R := F) (M := E))
  exact norm_of_root hr

theorem norm_real_pos {F E : Type} [Field F] [Field E] [Algebra F E] [Algebra F ℝ]
    [Module.Finite F E] {a : ℝ} (ha : 0 < a) : ∃ y : ℝ ⊗[F] E, Algebra.norm ℝ y = a :=
  norm_of_root (Real.rpow_inv_natCast_pow ha.le (Module.finrank_pos (R := F) (M := E)).ne')

theorem norm_pos_of_not_extends {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero F]
    [Module.Finite F E] (σ : F →+* ℝ) (hσ : ¬ ∃ τ : E →+* ℝ, τ.comp (algebraMap F E) = σ)
    {y : E} (hy : y ≠ 0) : 0 < σ (Algebra.norm F y) := by
  classical
  let : Algebra F ℂ := (Complex.ofRealHom.comp σ).toAlgebra
  have hm : ∀ a : F, algebraMap F ℂ a = (σ a : ℂ) := fun _ => rfl
  let c : (E →ₐ[F] ℂ) → (E →ₐ[F] ℂ) := fun φ =>
    { (starRingEnd ℂ).comp φ.toRingHom with
      commutes' := fun a => by
        change starRingEnd ℂ (φ (algebraMap F E a)) = _
        rw [φ.commutes, hm, Complex.conj_ofReal] }
  have hc : ∀ φ e, c φ e = starRingEnd ℂ (φ e) := fun _ _ => rfl
  have hne : ∀ φ, c φ ≠ φ := by
    intro φ h
    apply hσ
    have hr : ∀ e, ((φ e).re : ℂ) = φ e := fun e =>
      Complex.conj_eq_iff_re.1 (by rw [← hc, h])
    refine ⟨{ toFun := fun e => (φ e).re, map_one' := by simp, map_zero' := by simp,
              map_add' := by simp, map_mul' := fun a b => ?_ }, ?_⟩
    · apply Complex.ofReal_injective
      rw [Complex.ofReal_mul, hr, hr, hr, map_mul]
    · ext a
      change (φ (algebraMap F E a)).re = σ a
      rw [φ.commutes, hm, Complex.ofReal_re]
  have hφ : ∀ φ : E →ₐ[F] ℂ, φ y ≠ 0 := fun φ => (map_ne_zero _).2 hy
  have hn : ∀ φ : E →ₐ[F] ℂ, (‖φ y‖ : ℂ) ≠ 0 := fun φ => by
    exact_mod_cast (norm_ne_zero_iff.2 (hφ φ))
  have h1 : ∏ φ : E →ₐ[F] ℂ, (φ y / (‖φ y‖ : ℂ)) = 1 := by
    refine Finset.prod_involution (fun φ _ => c φ) (fun φ _ => ?_) (fun φ _ _ => hne φ)
      (fun _ _ => Finset.mem_univ _) (fun φ _ => ?_)
    · rw [hc, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have := hn φ
      push_cast
      field_simp
    · ext e; simp [hc]
  rw [Finset.prod_div_distrib, div_eq_one_iff_eq (Finset.prod_ne_zero_iff.2 fun φ _ => hn φ),
    ← Algebra.norm_eq_prod_embeddings F ℂ y, hm] at h1
  have h2 : σ (Algebra.norm F y) = ∏ φ : E →ₐ[F] ℂ, ‖φ y‖ := by exact_mod_cast h1
  rw [h2]
  exact Finset.prod_pos fun φ _ => norm_pos_iff.2 (hφ φ)

theorem local_conditions_of_global (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (x : F) (hx : x ≠ 0) (h : ∃ y : E, Algebra.norm F y = x) :
    (∀ v : HeightOneSpectrum (𝓞 F), ∃ y : TensorProduct F (v.adicCompletion F) E,
        Algebra.norm (v.adicCompletion F) y = algebraMap F (v.adicCompletion F) x) ∧
    (∀ σ : F →+* ℝ, (¬ ∃ τ : E →+* ℝ, τ.comp (algebraMap F E) = σ) → 0 < σ x) := by
  obtain ⟨y, rfl⟩ := h
  refine ⟨fun v => ⟨_, norm_one_tmul_eq y⟩, fun σ hσ => norm_pos_of_not_extends σ hσ ?_⟩
  rintro rfl
  exact hx (Algebra.norm_zero)

theorem exists_norm_neg {F E : Type} [Field F] [Field E] [Algebra F E] [Module.Finite F E] [IsGalois F E]
    (τ : E →+* ℝ) : ∃ y : E, τ (algebraMap F E (Algebra.norm F y)) < 0 := by
  classical
  have : CharZero E := τ.charZero
  have : CharZero F := (τ.comp (algebraMap F E)).charZero
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  have hinj : Function.Injective fun g : E ≃ₐ[F] E => τ (g α) := by
    intro g h e
    have e' : g α = h α := τ.injective e
    have : (g : E →ₐ[F] E) = h := by
      apply (Field.primitive_element_iff_algHom_eq_of_eval' F E (fun x => IsGalois.splits F x) α).1 hα
      exact e'
    ext z
    exact DFunLike.congr_fun this z
  obtain ⟨g0, -, hg0⟩ := Finset.exists_max_image Finset.univ (fun g : E ≃ₐ[F] E => τ (g α))
    ⟨1, Finset.mem_univ _⟩
  have hlt : ∀ g, g ≠ g0 → τ (g α) < τ (g0 α) := fun g hg =>
    lt_of_le_of_ne (hg0 g (Finset.mem_univ _)) fun e => hg (hinj e)
  obtain ⟨b, hb, hb'⟩ : ∃ b < τ (g0 α), ∀ g, g ≠ g0 → τ (g α) ≤ b := by
    by_cases hne : (Finset.univ.erase g0).Nonempty
    · obtain ⟨g1, h1, h2⟩ := Finset.exists_max_image _ (fun g : E ≃ₐ[F] E => τ (g α)) hne
      exact ⟨_, hlt g1 (Finset.ne_of_mem_erase h1), fun g hg => h2 g (by simp [hg])⟩
    · exact ⟨τ (g0 α) - 1, by linarith, fun g hg => absurd ⟨g, by simp [hg]⟩ hne⟩
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hb
  refine ⟨(q : E) - α, ?_⟩
  rw [Algebra.norm_eq_prod_automorphisms, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ g0)]
  apply mul_neg_of_neg_of_pos
  · simp only [map_sub, map_ratCast]; linarith
  · refine Finset.prod_pos fun g hg => ?_
    have := hb' g (Finset.ne_of_mem_erase hg)
    simp only [map_sub, map_ratCast]; linarith

theorem norm_real_of_extends {F E : Type} [Field F] [Field E] [Algebra F E] [Algebra F ℝ]
    [Module.Finite F E] [IsGalois F E] (τ : E →+* ℝ) (hτ : τ.comp (algebraMap F E) = algebraMap F ℝ)
    {a : ℝ} (ha : a ≠ 0) : ∃ y : ℝ ⊗[F] E, Algebra.norm ℝ y = a := by
  rcases ha.lt_or_gt with h | h
  · obtain ⟨y, hy⟩ := exists_norm_neg (F := F) τ
    have hy' : algebraMap F ℝ (Algebra.norm F y) < 0 := by rw [← hτ]; exact hy
    obtain ⟨z, hz⟩ := norm_real_pos (F := F) (E := E) (div_pos_of_neg_of_neg h hy')
    refine ⟨z * (1 ⊗ₜ y), ?_⟩
    rw [map_mul, hz, norm_one_tmul_eq, div_mul_cancel₀ _ hy'.ne]
  · exact norm_real_pos h

theorem local_norm_nonneg {F E : Type} [Field F] [Field E] [Algebra F E] [Algebra F ℝ] [CharZero F]
    [Module.Finite F E] (hσ : ¬ ∃ τ : E →+* ℝ, τ.comp (algebraMap F E) = algebraMap F ℝ)
    (y : ℝ ⊗[F] E) : 0 ≤ Algebra.norm ℝ y := by
  classical
  let b := Module.finBasis F E
  let B := b.baseChange ℝ
  let f : (Fin (Module.finrank F E) → ℝ) → ℝ := fun t => Algebra.norm ℝ (∑ i, t i • B i)
  have hf : Continuous f := by
    have : f = fun t => (∑ i, t i • Algebra.leftMulMatrix B (B i)).det := by
      funext t
      simp only [f]
      rw [Algebra.norm_eq_matrix_det B, map_sum]
      simp only [map_smul]
    rw [this]
    exact Continuous.matrix_det (by fun_prop)
  have hd : DenseRange (Pi.map fun (_ : Fin (Module.finrank F E)) (q : ℚ) => (q : ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  have hall : ∀ t, 0 ≤ f t := by
    intro t
    refine hd.induction_on t (isClosed_le continuous_const hf) fun q => ?_
    have he : (∑ i, Pi.map (fun (_ : Fin (Module.finrank F E)) (q : ℚ) => (q : ℝ)) q i • B i)
        = (1 : ℝ) ⊗ₜ[F] (∑ i, (q i : F) • b i) := by
      rw [TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.tmul_smul, ← algebraMap_smul ℝ (q i : F), map_ratCast]
      simp [B]
    simp only [f]
    rw [he, norm_one_tmul_eq]
    by_cases h0 : (∑ i, (q i : F) • b i) = 0
    · rw [h0, Algebra.norm_zero, map_zero]
    · exact (norm_pos_of_not_extends _ hσ h0).le
  have := hall (B.repr y)
  simpa only [f, B.sum_repr] using this

theorem real_clause_iff {F E : Type} [Field F] [Field E] [Algebra F E] [Algebra F ℝ] [CharZero F]
    [Module.Finite F E] [IsGalois F E] {x : F} (hx : x ≠ 0) :
    ((¬ ∃ τ : E →+* ℝ, τ.comp (algebraMap F E) = algebraMap F ℝ) → 0 < algebraMap F ℝ x) ↔
      ∃ y : ℝ ⊗[F] E, Algebra.norm ℝ y = algebraMap F ℝ x := by
  have hx' : algebraMap F ℝ x ≠ 0 := (map_ne_zero _).2 hx
  constructor
  · intro h
    by_cases hσ : ∃ τ : E →+* ℝ, τ.comp (algebraMap F E) = algebraMap F ℝ
    · obtain ⟨τ, hτ⟩ := hσ
      exact norm_real_of_extends τ hτ hx'
    · exact norm_real_pos (h hσ)
  · rintro ⟨y, hy⟩ hσ
    exact lt_of_le_of_ne (hy ▸ local_norm_nonneg hσ y) hx'.symm

theorem neg_one_not_norm (E : Type) [Field E] [NumberField E] [IsCyclotomicExtension {4} ℚ E] :
    IsGalois ℚ E ∧ IsCyclic (E ≃ₐ[ℚ] E) ∧ Module.finrank ℚ E = 2 ∧ ¬ ∃ y : E, Algebra.norm ℚ y = -1 := by
  have hG : IsGalois ℚ E := IsCyclotomicExtension.isGalois {4} ℚ E
  have hr : Module.finrank ℚ E = 2 := by
    rw [IsCyclotomicExtension.finrank (n := 4) E (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
    decide
  refine ⟨hG, isCyclic_of_prime_card (p := 2) (by rw [IsGalois.card_aut_eq_finrank, hr]), hr, ?_⟩
  rintro ⟨y, hy⟩
  have hσ : ¬ ∃ τ : E →+* ℝ, τ.comp (algebraMap ℚ _) = Rat.castHom ℝ := by
    rintro ⟨τ, -⟩
    have hζ := (IsCyclotomicExtension.zeta_spec 4 ℚ E).map_of_injective τ.injective
    have h2 := (hζ.pow (by norm_num) (show 4 = 2 * 2 by norm_num)).eq_neg_one_of_two_right
    nlinarith [sq_nonneg (τ (IsCyclotomicExtension.zeta 4 ℚ E))]
  have h0 : y ≠ 0 := by
    rintro rfl
    rw [Algebra.norm_zero] at hy
    norm_num at hy
  have := norm_pos_of_not_extends (Rat.castHom ℝ) hσ h0
  rw [hy] at this
  norm_num at this

theorem exists_gaussian_field : ∃ (E : Type) (_ : Field E) (_ : NumberField E),
    IsCyclotomicExtension {4} ℚ E :=
  ⟨CyclotomicField 4 ℚ, inferInstance, inferInstance, CyclotomicField.isCyclotomicExtension 4 ℚ⟩

end GlobalTheory.CyclicNormCheck
