import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsNeZeroNormSqLeMulCovolumeRpow

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW

theorem exists_linearIndependent_of_rat_independent {E U : Type} [Field E] [NumberField E]
    [AddCommGroup U] [Module E U] [Module ℚ U] [IsScalarTower ℚ E U] (S : ℕ → Set U) (N : ℕ)
    (h : ∀ i < N, ∃ u : Fin (Module.finrank ℚ E * i + 1) → U,
      LinearIndependent ℚ u ∧ ∀ k, u k ∈ S i) :
    ∃ w : Fin N → U, LinearIndependent E w ∧ ∀ i : Fin N, w i ∈ S i := by
  induction N with
  | zero => exact ⟨Fin.elim0, linearIndependent_empty_type, fun i => i.elim0⟩
  | succ N ih =>
    obtain ⟨w, hw, hS⟩ := ih fun i hi => h i (by omega)
    obtain ⟨u, hu, huS⟩ := h N (by omega)
    obtain ⟨k, hk⟩ : ∃ k, u k ∉ Submodule.span E (Set.range w) := by
      by_contra! hc
      have : Module.Finite E (Submodule.span E (Set.range w)) :=
        Module.Finite.span_of_finite E (Set.finite_range w)
      have : Module.Finite ℚ (Submodule.span E (Set.range w)) := Module.Finite.trans E _
      have h1 : LinearIndependent ℚ (fun k => (⟨u k, hc k⟩ : Submodule.span E (Set.range w))) :=
        LinearIndependent.of_comp
          ((Submodule.span E (Set.range w)).subtype.restrictScalars ℚ) hu
      have h2 := h1.fintype_card_le_finrank
      rw [← Module.finrank_mul_finrank ℚ E (Submodule.span E (Set.range w)),
        finrank_span_eq_card hw] at h2
      simp at h2
    refine ⟨Fin.snoc w (u k), linearIndependent_finSnoc.2 ⟨hw, hk⟩, fun i => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using huS k
    · simpa using hS j

theorem prod_pow_le_prod_of_mono (l : ℕ → ℝ) (hl : ∀ i, 0 ≤ l i) (d N : ℕ)
    (hm : ∀ i j, i ≤ j → j ≤ d * N → l i ≤ l j) :
    ∏ i ∈ Finset.range N, l (d * i + 1) ^ d ≤ ∏ j ∈ Finset.range (d * N), l (j + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ, mul_add, mul_one, Finset.prod_range_add]
    refine mul_le_mul (ih fun i j hij hj => hm i j hij (by nlinarith)) ?_ (pow_nonneg (hl _) _)
      (Finset.prod_nonneg fun _ _ => hl _)
    calc l (d * N + 1) ^ d = ∏ _j ∈ Finset.range d, l (d * N + 1) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => hl _) fun j hj => hm _ _ (by omega) (by
          have := Finset.mem_range.1 hj
          rw [mul_add]; omega)

theorem IsType.prod_univ {E : Type} [Field E] [NumberField E] [IsCMField E]
    {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) {M : Type} [CommMonoid M] (g : (E →+* ℂ) → M) :
    ∏ σ, g σ = ∏ τ : Ψ, (g τ * g (ComplexEmbedding.conjugate τ.1)) := by
  classical
  rw [Finset.prod_coe_sort Ψ (fun τ => g τ * g (ComplexEmbedding.conjugate τ)),
    Finset.prod_mul_distrib, ← Finset.prod_mul_prod_compl Ψ]
  congr 1
  symm
  refine Finset.prod_bij' (fun τ _ => ComplexEmbedding.conjugate τ)
    (fun τ _ => ComplexEmbedding.conjugate τ) ?_ ?_ ?_ ?_ ?_
  · intro τ hτ; exact Finset.mem_compl.2 ((hΨ τ).1 hτ)
  · intro τ hτ
    by_contra hc
    exact Finset.mem_compl.1 hτ ((hΨ τ).2 hc)
  · intro τ _; exact star_star τ
  · intro τ _; exact star_star τ
  · intro τ _; rfl

theorem IsType.finrank_eq {E : Type} [Field E] [NumberField E] [IsCMField E]
    {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) : Module.finrank ℚ E = 2 * Ψ.card := by
  have h := hΨ.prod_univ (fun _ => Multiplicative.ofAdd (1 : ℕ))
  have h2 := congrArg Multiplicative.toAdd h
  simp only [Finset.prod_const, toAdd_pow, toAdd_mul, toAdd_ofAdd, smul_eq_mul, Finset.card_univ,
    Embeddings.card, Fintype.card_coe] at h2
  omega

theorem exists_linearIndependent_prod_norm_le {E U V ι : Type} [Field E] [NumberField E]
    [AddCommGroup U] [Module E U] [Module ℚ U] [IsScalarTower ℚ E U] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [Fintype ι] [DecidableEq ι] {N : ℕ}
    (hι : Fintype.card ι = Module.finrank ℚ E * N) (φ : U →ₗ[ℤ] V) (u : ι → U)
    (hu : LinearIndependent ℝ fun k => φ (u k)) :
    ∃ w : Fin N → U, LinearIndependent E w ∧ (∀ i, w i ∈ Submodule.span ℤ (Set.range u)) ∧
      ∏ i, ‖φ (w i)‖ ^ Module.finrank ℚ E ≤
        (Fintype.card ι : ℝ) ^ ((Fintype.card ι : ℝ) / 2) * √(gram ℝ fun k => φ (u k)).det := by
  set d := Module.finrank ℚ E with hd
  have hd0 : 0 < d := Module.finrank_pos
  set L := Submodule.span ℤ (Set.range fun k => φ (u k)) with hL
  have : DiscreteTopology L := discreteTopology_span_of_linearIndependent hu
  have huZ : LinearIndependent ℤ fun k => φ (u k) := hu.restrict_scalars' ℤ
  have hr : Module.finrank ℤ L = Fintype.card ι := finrank_span_eq_card huZ
  have hrR : Module.finrank ℝ (Submodule.span ℝ (L : Set V)) = d * N := by
    rw [finrank_span_eq_finrank_int, hr, hι]
  have hLm : L = (Submodule.span ℤ (Set.range u)).map φ := by
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  obtain ⟨w, hw, hS⟩ := exists_linearIndependent_of_rat_independent (E := E)
    (fun i => {t | t ∈ Submodule.span ℤ (Set.range u) ∧ ‖φ t‖ ≤ succMin L (d * i + 1)}) N (by
      intro i hi
      obtain ⟨v, hv, hvL⟩ := exists_linearIndependent_norm_le_succMin (L := L) (i := d * i + 1)
        (by rw [hrR]; nlinarith)
      have : ∀ k, ∃ t ∈ Submodule.span ℤ (Set.range u), φ t = v k := fun k => by
        have := (hvL k).1
        rwa [hLm] at this
      choose t ht htv using this
      refine ⟨t, (LinearIndependent.iff_fractionRing ℤ ℚ).1 (LinearIndependent.of_comp φ ?_),
        fun k => ⟨ht k, ?_⟩⟩
      · have : φ ∘ t = v := funext htv
        rw [this]; exact hv.restrict_scalars' ℤ
      · rw [htv]; exact (hvL k).2)
  refine ⟨w, hw, fun i => (hS i).1, ?_⟩
  have h1 := prod_succMin_le_rpow_mul_spanCovol L
  rw [spanCovol_span huZ, Fin.prod_univ_eq_prod_range (fun i => succMin L (i + 1)), hr] at h1
  refine le_trans ?_ h1
  rw [hι]
  refine le_trans ?_ (prod_pow_le_prod_of_mono (succMin L) (succMin_nonneg L) d N
    fun i j hij hj => succMin_mono hij (by rwa [hrR]))
  rw [← Fin.prod_univ_eq_prod_range (fun i => succMin L (d * i + 1) ^ d)]
  exact Finset.prod_le_prod (fun _ _ => by positivity) fun i _ =>
    pow_le_pow_left₀ (norm_nonneg _) (hS i).2 _

theorem posDef_map_mul_conjTranspose {E m n : Type} [Field E] [Fintype m] [Fintype n]
    {W : Matrix n m E} (hW : LinearIndependent E fun i => W i) (σ : E →+* ℂ) :
    (W.map σ * (W.map σ)ᴴ).PosDef := by
  let _ := σ.toAlgebra
  exact PosDef.mul_conjTranspose_self _
    (vecMul_injective_iff.2 ((linearIndependent_algebraMap_comp_iff (S := ℂ)).2 hW))

noncomputable def rowEmb {E m n : Type} [Field E] [Fintype n] (W : Matrix n m E) :
    (n → E) →ₗ[ℤ] EuclideanSpace ℂ ((E →+* ℂ) × m) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun t => WithLp.toLp 2 fun p => p.1 ((t ᵥ* W) p.2)
      map_zero' := by ext p; simp
      map_add' := fun s t => by ext p; simp [add_vecMul] }

@[simp] theorem rowEmb_apply {E m n : Type} [Field E] [Fintype n] (W : Matrix n m E) (t : n → E)
    (p : (E →+* ℂ) × m) : rowEmb W t p = p.1 ((t ᵥ* W) p.2) := rfl

open Classical in

theorem det_gram_rowEmb {E m : Type} [Field E] [NumberField E] [Fintype m] {N : ℕ}
    (W : Matrix (Fin N) m E) (ω : (E →+* ℂ) → E) :
    (((gram ℝ fun p : Fin N × (E →+* ℂ) => rowEmb W (Pi.single p.1 (ω p.2))).det : ℝ) : ℂ) =
      (normSq (Matrix.of fun k σ : E →+* ℂ => σ (ω k)).det : ℂ) ^ N *
        ∏ σ : E →+* ℂ, (W.map σ * (W.map σ)ᴴ).det := by
  set A : Matrix (E →+* ℂ) (E →+* ℂ) ℂ := Matrix.of fun k σ : E →+* ℂ => σ (ω k) with hA
  set P : Matrix (Fin N × (E →+* ℂ)) (Fin N × (E →+* ℂ)) ℂ :=
    kroneckerMap (· * ·) (1 : Matrix (Fin N) (Fin N) ℂ) A with hP
  have hdP : P.det = A.det ^ N := by simp [hP, det_kronecker]
  have key : (gram ℝ fun p : Fin N × (E →+* ℂ) => rowEmb W (Pi.single p.1 (ω p.2))).map ofRealHom
      = (P * blockDiagonal (fun σ : E →+* ℂ => W.map σ * (W.map σ)ᴴ) * Pᴴ)ᵀ := by
    ext ⟨i, k⟩ ⟨i', k'⟩
    have hR : (P * blockDiagonal (fun σ : E →+* ℂ => W.map σ * (W.map σ)ᴴ) * Pᴴ)ᵀ (i, k) (i', k')
        = ∑ σ : E →+* ℂ, ∑ j, σ (ω k' * W i' j) * conj (σ (ω k * W i j)) := by
      simp only [transpose_apply, mul_apply, Fintype.sum_prod_type, hP, hA, kroneckerMap_apply,
        one_apply, blockDiagonal_apply, conjTranspose_apply, of_apply, map_apply]
      simp [Finset.mul_sum, Finset.sum_mul, apply_ite]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [hR]
    have hreal : conj (∑ σ : E →+* ℂ, ∑ j, σ (ω k' * W i' j) * conj (σ (ω k * W i j))) =
        ∑ σ : E →+* ℂ, ∑ j, σ (ω k' * W i' j) * conj (σ (ω k * W i j)) := by
      rw [map_sum]
      refine Fintype.sum_equiv (Function.Involutive.toPerm _
        (ComplexEmbedding.involutive_conjugate E)) _ _ fun σ => ?_
      simp [map_sum]
    rw [← conj_eq_iff_re.1 hreal]
    simp [gram_apply, PiLp.inner_apply, Fintype.sum_prod_type, Complex.inner, single_vecMul]
  rw [← ofRealHom_eq_coe, RingHom.map_det, RingHom.mapMatrix_apply, key, det_transpose, det_mul,
    det_mul, det_conjTranspose, hdP, det_blockDiagonal, normSq_eq_conj_mul_self]
  simp only [star_pow, RCLike.star_def]
  ring

theorem IsType.prod_det_eq_sq {E m n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype m]
    [Fintype n] [DecidableEq n] {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (W : Matrix n m E) :
    ∏ σ : E →+* ℂ, (W.map σ * (W.map σ)ᴴ).det =
      (((∏ τ : Ψ, (W.map τ.1 * (W.map τ.1)ᴴ).det.re) ^ 2 : ℝ) : ℂ) := by
  rw [hΨ.prod_univ, ← Finset.prod_pow, ofReal_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h1 : W.map (ComplexEmbedding.conjugate τ.1) * (W.map (ComplexEmbedding.conjugate τ.1))ᴴ =
      (W.map τ.1 * (W.map τ.1)ᴴ)ᵀ := by
    ext i j
    simp [mul_apply, mul_comm]
  have h2 : (((W.map τ.1 * (W.map τ.1)ᴴ).det.re : ℝ) : ℂ) = (W.map τ.1 * (W.map τ.1)ᴴ).det :=
    conj_eq_iff_re.1 (by
      rw [← RCLike.star_def, ← det_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose])
  rw [h1, det_transpose, ofReal_pow, h2, sq]

theorem exists_short_independent_rows :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ →
      ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (m : Type) [Fintype m] (W : Matrix (Fin N) m E),
        LinearIndependent E (fun i => W i) → ∃ a : Matrix (Fin N) (Fin N) E, IntM a ∧ a.det ≠ 0 ∧
          ∏ i, (∑ τ : Ψ, ∑ j, ‖τ.1 ((a * W) i j)‖ ^ 2) ^ Ψ.card ≤
            C * ∏ τ : Ψ, (W.map τ.1 * (W.map τ.1)ᴴ).det.re := by
  classical
  intro E _ _ _ Ψ hΨ N
  set ω : (E →+* ℂ) → E := fun k => integralBasis E (equivReindex E k) with hω
  have hωi : ∀ k, IsIntegral ℤ (ω k) := fun k => by
    rw [hω]; simp only [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _
  set A : Matrix (E →+* ℂ) (E →+* ℂ) ℂ := Matrix.of fun k σ : E →+* ℂ => σ (ω k) with hA
  have hA0 : A.det ≠ 0 := by
    have : A = basisMatrix E := by
      ext k σ
      simp only [hA, hω, basisMatrix, of_apply, canonicalEmbedding.latticeBasis_apply,
        canonicalEmbedding.apply_at]
    rw [this]; exact det_of_basisMatrix_non_zero E
  set n : ℕ := Fintype.card (Fin N × (E →+* ℂ)) with hn
  have hc : 0 < (n : ℝ) ^ ((n : ℝ) / 2) := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · positivity
  have hA1 : 0 < ‖A.det‖ := norm_pos_iff.2 hA0
  refine ⟨(n : ℝ) ^ ((n : ℝ) / 2) * ‖A.det‖ ^ N, by positivity, fun m _ W hW => ?_⟩
  have hpos : 0 < ∏ τ : Ψ, (W.map τ.1 * (W.map τ.1)ᴴ).det.re :=
    Finset.prod_pos fun τ _ => (Complex.pos_iff.1 (posDef_map_mul_conjTranspose hW τ.1).det_pos).1
  have hdet : (gram ℝ fun p : Fin N × (E →+* ℂ) => rowEmb W (Pi.single p.1 (ω p.2))).det =
      (‖A.det‖ ^ N * ∏ τ : Ψ, (W.map τ.1 * (W.map τ.1)ᴴ).det.re) ^ 2 := by
    have h := det_gram_rowEmb W ω
    rw [hΨ.prod_det_eq_sq, normSq_eq_norm_sq] at h
    rw [mul_pow, ← pow_mul, mul_comm N, pow_mul]
    exact_mod_cast h
  obtain ⟨a, ha, hai, hle⟩ := exists_linearIndependent_prod_norm_le (E := E) (N := N)
    (by rw [Fintype.card_prod, Fintype.card_fin, Embeddings.card, mul_comm]) (rowEmb W) (fun p : Fin N × (E →+* ℂ) => Pi.single p.1 (ω p.2))
    (det_gram_ne_zero_iff_linearIndependent.1 (by rw [hdet]; positivity))
  refine ⟨Matrix.of a, fun i => ?_, ?_, ?_⟩
  · show ∀ j, IsIntegral ℤ (a i j)
    refine Submodule.span_induction (p := fun t _ => ∀ j, IsIntegral ℤ (t j)) ?_ ?_ ?_ ?_ (hai i)
    · rintro _ ⟨p, rfl⟩ j
      simp only [Pi.single_apply]
      split_ifs
      · exact hωi _
      · exact isIntegral_zero
    · exact fun _ => isIntegral_zero
    · exact fun x y _ _ hx hy j => (hx j).add (hy j)
    · exact fun c x _ hx j => (hx j).smul c
  · exact ((Matrix.isUnit_iff_isUnit_det _).1
      (linearIndependent_rows_iff_isUnit.1 (show LinearIndependent E (Matrix.of a).row from ha))).ne_zero
  · rw [hdet, Real.sqrt_sq (by positivity), ← mul_assoc, hΨ.finrank_eq] at hle
    refine le_trans (Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => ?_) hle
    rw [pow_mul, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    rw [Finset.sum_coe_sort Ψ (fun τ => ∑ j, ‖τ ((Matrix.of a * W) i j)‖ ^ 2)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Ψ)
      (f := fun τ => ∑ j, ‖τ ((Matrix.of a * W) i j)‖ ^ 2) fun _ _ _ => by positivity

end GlobalTheory.SW
