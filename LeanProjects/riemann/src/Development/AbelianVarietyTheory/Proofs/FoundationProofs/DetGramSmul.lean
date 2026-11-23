import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EisValueAtIffEisPoleLE
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneMemEntries
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLinearIndependentOfRatIndependent
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdeleCoverModFieldShrunkCompactStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SkewHermitianAdelicCoverOfAdeleCoverStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactAdelesRationalPointsFiniteEventuallyZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TensorIdeleNormalizedAbsIdeleHalfAtInfinityStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummableRpowOfFibreCardLeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntGeneratorsCardEqOfIsLatticePiStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LinearIndependentVecMulOfSpanRatStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GramDetIndexSublatticeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MatrixInvEntriesBoundedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeAdelicMatrixIntegralTranslateStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCmAdeleSplitComplexFiniteAdelesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TotallyComplexSpanEmbeddingsAndFinrankStatement

noncomputable section

namespace GlobalTheory.Eis.Conv

open Matrix Formalism.UG GlobalTheory.Doubling
open scoped NNReal

section Reduction

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Module

theorem det_gram_smul {V κ : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fintype κ] [DecidableEq κ]
    (a : κ → ℝ) (v : κ → V) : (gram ℝ fun k => a k • v k).det = (∏ k, a k) ^ 2 * (gram ℝ v).det := by
  have : (gram ℝ fun k => a k • v k) = diagonal a * gram ℝ v * diagonal a := by
    ext i j; simp [gram_apply, inner_smul_left, inner_smul_right, mul_diagonal, diagonal_mul]; ring
  rw [this, det_mul, det_mul, det_diagonal]; ring

theorem red_inf (E : Type) [Field E] [NumberField E] (R : Type) [NormedCommRing R] [NormedAlgebra ℝ R]
    [FiniteDimensional ℝ R] (τ : E →+* R) (hτ : Submodule.span ℝ (Set.range τ) = ⊤) (hd : finrank ℝ R = finrank ℚ E)
    (n : ℕ) : ∃ (M : ℕ) (C : ℝ), 0 < M ∧ ∀ (Λ : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E Λ →
      ∀ g : GL (Fin n) R, ∃ (δ : GL (Fin n) E) (l : Fin n → ℤ) (c : GL (Fin n) R), (∀ i, δ.1 i ∈ Λ) ∧
        (∀ x ∈ Λ, ∃ y : Fin n → 𝓞 E, (M : E) • x = (fun i => (y i : E)) ᵥ* δ.1) ∧
        (∀ i j, ‖c.1 i j‖ ≤ C ∧ ‖c⁻¹.1 i j‖ ≤ C) ∧
        δ.1.map τ * g.1 = diagonal (fun i => algebraMap ℝ R (2 ^ l i)) * c.1 := by
  classical
  haveI : Nontrivial R := Module.nontrivial_of_finrank_pos (R := ℝ) (hd ▸ finrank_pos)
  let ε := toEuclidean (E := Fin n → R)
  let κ := Σ _ : Fin n, Free.ChooseBasisIndex ℤ (𝓞 E)
  have hκ : Fintype.card κ = finrank ℚ E * n := by
    simp [κ, ← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, mul_comm]
  let fam : Matrix (Fin n) (Fin n) R → κ → Fin n → R := fun c p => τ (integralBasis E p.2) • c p.1
  let G : Matrix (Fin n) (Fin n) R → ℝ := fun c => (gram ℝ fun p => ε (fam c p)).det
  have hGc : Continuous G := Continuous.matrix_det (continuous_matrix fun p q => by
    simp only [gram_apply, fam]; fun_prop)
  have hG1 : ∀ c, G c ≠ 0 → IsUnit c := fun c h => by
    have h1 : LinearIndependent ℝ (fam c) :=
      LinearIndependent.of_comp ε.toLinearEquiv.toLinearMap (det_gram_ne_zero_iff_linearIndependent.1 h)
    have h2 := h1.span_eq_top_of_card_eq_finrank' (by rw [hκ, finrank_pi_fintype, hd]; simp [mul_comm])
    refine vecMul_surjective_iff_isUnit.1 fun x => ?_
    have h3 : Submodule.span ℝ (Set.range (fam c)) ≤ (LinearMap.range (vecMulLinear c)).restrictScalars ℝ := by
      rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      exact ⟨Pi.single p.1 (τ (integralBasis E p.2)), by simp [fam, single_vecMul]; rfl⟩
    exact h3 (h2 ▸ Submodule.mem_top)
  have hG2 : ∀ c : GL (Fin n) R, G c.1 ≠ 0 := fun c => by
    have h1 := GlobalTheory.T.linearIndependent_vecMul_of_span_rat' E R τ hτ hd n κ (Pi.basis fun _ => integralBasis E) hκ (Basis.span_eq _) c
    refine det_gram_ne_zero_iff_linearIndependent.2 ?_
    have h2 := h1.map' ε.toLinearEquiv.toLinearMap ε.toLinearEquiv.ker
    refine (show _ = fun p => ε (fam c.1 p) from funext fun p => ?_) ▸ h2
    have : (fun i => τ ((Pi.basis fun _ => integralBasis E) p i)) = Pi.single p.1 (τ (integralBasis E p.2)) := by
      ext i; simp [Pi.single_apply, apply_ite τ]
    simp only [Function.comp, this, single_vecMul]; rfl
  set c₀ : ℝ := (Fintype.card (Fin (finrank ℚ E * n)) : ℝ) ^ ((Fintype.card (Fin (finrank ℚ E * n)) : ℝ) / 2) with hc₀
  have hc₀' : 0 ≤ c₀ := by positivity
  set c₁ : ℝ := ((2 ^ finrank ℚ E) ^ n * c₀) ^ 2 + 1 with hc₁
  have hc₁' : 0 < c₁ := by positivity
  obtain ⟨C, hC1, hC2⟩ := GlobalTheory.T.exists_bound_inv_entries_of_bounded_entries R n G hGc hG1 ‖ε.symm.toContinuousLinearMap‖ c₁⁻¹ (inv_pos.2 hc₁')
  refine ⟨⌈c₁ * C⌉₊.factorial, max C ‖ε.symm.toContinuousLinearMap‖, Nat.factorial_pos _, fun Λ hΛ g => ?_⟩
  obtain ⟨u, hu, hu'⟩ := GlobalTheory.T.exists_int_span_generators_of_isLattice_pi E n Λ hΛ
  let φ : (Fin n → E) →ₗ[ℤ] EuclideanSpace ℝ (Fin (finrank ℝ (Fin n → R))) := AddMonoidHom.toIntLinearMap
    { toFun := fun x => ε ((fun i => τ (x i)) ᵥ* g.1)
      map_zero' := by simp [← Pi.zero_def]
      map_add' := fun x y => by rw [← map_add, ← add_vecMul]; simp [← Pi.add_def] }
  have hφ : ∀ x, φ x = ε ((fun i => τ (x i)) ᵥ* g.1) := fun _ => rfl
  have hφu : LinearIndependent ℝ fun k => φ (u k) :=
    (GlobalTheory.T.linearIndependent_vecMul_of_span_rat' E R τ hτ hd n _ u (Fintype.card_fin _) hu' g).map' ε.toLinearEquiv.toLinearMap ε.toLinearEquiv.ker
  obtain ⟨w, hw, hwu, hle⟩ := GlobalTheory.SW.exists_linearIndependent_prod_norm_le (E := E) (N := n) (Fintype.card_fin _) φ u hφu
  have hGu : 0 < (gram ℝ fun k => φ (u k)).det := (posDef_gram_of_linearIndependent hφu).det_pos
  obtain ⟨δ, hδ⟩ : IsUnit (of w) := linearIndependent_rows_iff_isUnit.1 hw
  have hw0 : ∀ i, 0 < ‖φ (w i)‖ := fun i => norm_pos_iff.2 fun h => hw.ne_zero i (funext fun k => τ.injective (by
    have := (vecMul_injective_of_isUnit g.isUnit) ((ε.map_eq_zero_iff.1 h).trans (zero_vecMul _).symm)
    rw [Pi.zero_apply, map_zero]; exact congrFun this k))
  choose l hl using fun i => exists_mem_Ioc_zpow (hw0 i) one_lt_two
  let s : Rˣ := Units.map (algebraMap ℝ R).toMonoidHom (Units.mk0 2 two_ne_zero)
  have hs : ∀ z : ℤ, (s ^ z).1 = algebraMap ℝ R (2 ^ z) := fun z => by
    rw [← map_zpow]
    exact congrArg (algebraMap ℝ R) (Units.val_zpow_eq_zpow_val _ _)
  set c : GL (Fin n) R := (dg s fun i => l i + 1)⁻¹ * (bc τ δ * g) with hc
  have h1 : δ.1.map τ * g.1 = diagonal (fun i => algebraMap ℝ R (2 ^ (l i + 1))) * c.1 := by
    rw [← funext fun i => hs (l i + 1)]
    exact congrArg Units.val (mul_inv_cancel_left (dg s fun i => l i + 1) (bc τ δ * g)).symm
  have h2 : ∀ i, (fun k => τ (w i k)) ᵥ* g.1 = (2 : ℝ) ^ (l i + 1) • c.1 i := fun i => funext fun k => by
    have := congrFun (congrFun h1 i) k
    rw [diagonal_mul, hδ, ← Algebra.smul_def] at this
    exact this
  have h3 : ∀ i j, ‖c.1 i j‖ ≤ ‖ε.symm.toContinuousLinearMap‖ := fun i j => by
    have h4 := (hl i).2
    rw [hφ, h2, map_smul, norm_smul, Real.norm_of_nonneg (by positivity), mul_le_iff_le_one_right (by positivity)] at h4
    refine (norm_le_pi_norm _ j).trans ?_
    simpa using ε.symm.toContinuousLinearMap.le_of_opNorm_le_of_le le_rfl h4
  let v : κ → Fin n → E := fun p => integralBasis E p.2 • w p.1
  have hv : ∀ p : κ, v p = RingOfIntegers.basis E p.2 • w p.1 := fun p => by
    simp only [v, integralBasis_apply]; rfl
  obtain ⟨m, hm1, hm2⟩ := GlobalTheory.T.gram_det_eq_sq_mul_gram_det_of_mem_span _ _ _ κ φ u v (by rw [hκ, Fintype.card_fin])
    fun p => (hu _).1 (hv p ▸ Λ.smul_mem _ ((hu _).2 (hwu _)))
  have h5 : ∀ p : κ, φ (v p) = (2 : ℝ) ^ (l p.1 + 1) • ε (fam c.1 p) := fun p => by
    rw [hφ, ← map_smul, ← smul_comm, ← h2, ← smul_vecMul]
    congr 2; ext i; exact map_mul τ _ _
  simp only [h5, det_gram_smul] at hm1
  have h6 : ∏ p : κ, (2 : ℝ) ^ (l p.1 + 1) ≤ (2 ^ finrank ℚ E) ^ n * ∏ i, ‖φ (w i)‖ ^ finrank ℚ E := by
    rw [Fintype.prod_sigma]
    simp only [Finset.prod_const, Finset.card_univ, ← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
    calc _ ≤ ∏ i, (2 * ‖φ (w i)‖) ^ finrank ℚ E := Finset.prod_le_prod (fun _ _ => by positivity) fun i _ =>
          pow_le_pow_left₀ (by positivity) (by rw [zpow_add_one₀ two_ne_zero]; linarith [(hl i).1]) _
      _ = _ := by simp [mul_pow, Finset.prod_mul_distrib]
  have h7 : (∏ p : κ, (2 : ℝ) ^ (l p.1 + 1)) ^ 2 ≤ c₁ * (gram ℝ fun k => φ (u k)).det := by
    refine (pow_le_pow_left₀ (by positivity) (h6.trans (mul_le_mul_of_nonneg_left hle (by positivity))) 2).trans ?_
    rw [← mul_assoc, mul_pow, Real.sq_sqrt hGu.le]
    exact mul_le_mul_of_nonneg_right (by linarith) hGu.le
  have hG0 : 0 ≤ G c.1 := (posSemidef_gram ℝ _).det_nonneg
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at hm1
    exact mul_ne_zero (by positivity) (hG2 c) hm1
  have h8 : (m : ℝ) ^ 2 ≤ c₁ * G c.1 := by
    refine le_of_mul_le_mul_right ?_ hGu
    rw [← hm1, mul_right_comm]
    exact mul_le_mul_of_nonneg_right h7 hG0
  have hm3 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  have h9 : m ∣ ⌈c₁ * C⌉₊.factorial := Nat.dvd_factorial (Nat.pos_of_ne_zero hm0) (by
    refine Nat.cast_le (α := ℝ).1 (le_trans ?_ (Nat.le_ceil _))
    nlinarith [mul_le_mul_of_nonneg_left (hC1 c.1 h3) hc₁'.le])
  refine ⟨δ, _, c, fun i => hδ ▸ (hu _).2 (hwu i), fun x hx => ?_, fun i j => ⟨(h3 i j).trans (le_max_right _ _),
    (hC2 c h3 ((inv_le_iff_one_le_mul₀' hc₁').2 (by nlinarith)) i j).trans (le_max_left _ _)⟩, h1⟩
  have h10 : ∀ z ∈ Submodule.span ℤ (Set.range v), ∃ y : Fin n → 𝓞 E, z = (fun i => (y i : E)) ᵥ* δ.1 := fun z hz => by
    induction hz using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨p, rfl⟩ := h
      refine ⟨Pi.single p.1 (RingOfIntegers.basis E p.2), ?_⟩
      have : (fun i => ((Pi.single p.1 (RingOfIntegers.basis E p.2) : Fin n → 𝓞 E) i : E)) =
          Pi.single p.1 (integralBasis E p.2) := by
        ext i
        by_cases h : i = p.1
        · subst h; simp [integralBasis_apply]
        · simp [h]
      rw [this, single_vecMul, hδ]; rfl
    | zero => exact ⟨0, by simp [← Pi.zero_def]⟩
    | add _ _ _ _ h h' =>
      obtain ⟨y, rfl⟩ := h; obtain ⟨y', rfl⟩ := h'
      exact ⟨y + y', by rw [← add_vecMul]; simp [← Pi.add_def]⟩
    | smul a _ _ h =>
      obtain ⟨y, rfl⟩ := h
      exact ⟨a • y, by rw [← smul_vecMul]; congr 1⟩
  obtain ⟨r, hr⟩ := h9
  refine h10 _ ?_
  have h11 : (m : ℤ) • x ∈ Submodule.span ℤ (Set.range v) :=
    (Submodule.span_le (p := (Submodule.span ℤ (Set.range v)).comap (LinearMap.lsmul ℤ _ (m : ℤ)))).2
      (by rintro _ ⟨i, rfl⟩; exact hm2 i) ((hu x).1 hx)
  convert Submodule.smul_mem _ (r : ℤ) h11 using 1
  rw [hr, smul_smul, ← Int.cast_smul_eq_zsmul E]
  push_cast; rw [mul_comm]

theorem red_gl (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hc : IsCMExt F E σ) (n : ℕ) : ∃ Ω : Set (AF F ⊗[F] E), IsCompact Ω ∧ ∀ β : GL (Fin n) (AF F ⊗[F] E),
      ∃ (δ : GL (Fin n) E) (l : Fin n → ℤ) (c : GL (Fin n) (AF F ⊗[F] E)), (∀ i j, c.1 i j ∈ Ω ∧ c⁻¹.1 i j ∈ Ω) ∧
        δ.1.map (inclR (F := F) (AF F)) * β.1 = diagonal (fun i => (halfE F E ^ l i).1) * c.1 := by
  haveI := hc.2.1
  obtain ⟨e, he, he1, he2⟩ := GlobalTheory.T.exists_cmAdele_split_complex_finiteAdeles F E σ hc
  obtain ⟨M, C, hM, H⟩ := red_inf E _ _ (GlobalTheory.T.span_range_embedding_and_finrank_of_isTotallyComplex E).1 (GlobalTheory.T.span_range_embedding_and_finrank_of_isTotallyComplex E).2 n
  let O : Set (FiniteAdeleRing (𝓞 E) E) := {a | ∀ v, a v ∈ v.adicCompletionIntegers E}
  have hO : IsCompact O := GlobalTheory.AdeleCocompact.isCompact_integral E
  haveI : ProperSpace (InfinitePlace E → ℂ) := inferInstance
  refine ⟨e.symm '' (Metric.closedBall 0 C ×ˢ (O ∪ (fun a => algebraMap E _ (M : E)⁻¹ * a) '' O)),
    ((isCompact_closedBall _ _).prod (hO.union (hO.image (continuous_const.mul continuous_id)))).image he, fun β => ?_⟩
  let p₁ := (RingHom.fst _ _).comp e.toRingHom
  let p₂ := (RingHom.snd _ _).comp e.toRingHom
  obtain ⟨Λ, hΛ, H'⟩ := GlobalTheory.T.exists_lattice_adelicMatrix_integral_translate E n (bc p₂ β)
  obtain ⟨δ, l, c₁, h1, h2, h3, h4⟩ := H Λ hΛ (bc p₁ β)
  replace H' := H' M δ h1 h2
  set c := (dg (halfE F E) fun i => -l i)⁻¹ * (bc (inclR (F := F) (AF F)) δ * β) with hc
  have hd : ∀ {B : Type} [CommRing B] (p : AF F ⊗[F] E →+* B), bc p (dg (halfE F E) fun i => -l i) =
      dg (Units.map p.toMonoidHom (halfE F E)) fun i => -l i := fun p => Units.ext (by
    change (diagonal _).map p = diagonal _
    rw [diagonal_map (map_zero p)]
    exact congrArg diagonal (funext fun i => congrArg Units.val (map_zpow (Units.map p.toMonoidHom) _ _)))
  have h5 : bc p₁ c = c₁ := by
    rw [hc, map_mul, map_mul, map_inv, inv_mul_eq_iff_eq_mul, hd]
    refine Units.ext (Eq.trans ?_ (h4.trans ?_))
    · exact congrArg (· * (bc p₁ β).1) (Matrix.ext fun i j => congrArg Prod.fst (he1 _))
    · have : Units.map p₁.toMonoidHom (halfE F E) =
          (Units.map (algebraMap ℝ (InfinitePlace E → ℂ)).toMonoidHom (Units.mk0 2 two_ne_zero))⁻¹ :=
        Units.ext ((congrArg Prod.fst he2).trans (by ext; simp))
      refine congrArg (· * c₁.1) (congrArg diagonal (funext fun i => ?_))
      rw [this, _root_.inv_zpow', neg_neg, ← map_zpow]
      exact congrArg (algebraMap ℝ (InfinitePlace E → ℂ)) (Units.val_zpow_eq_zpow_val (Units.mk0 (2 : ℝ) two_ne_zero) _).symm
  have h6 : bc p₂ c = bc (algebraMap E _) δ * bc p₂ β := by
    have : Units.map p₂.toMonoidHom (halfE F E) = 1 := Units.ext (congrArg Prod.snd he2)
    rw [hc, map_mul, map_mul, map_inv, hd, this, show (dg 1 fun i => -l i) = 1 from Units.ext (by simp [dg]), inv_one,
      one_mul]
    exact congrArg (· * bc p₂ β) (Units.ext (Matrix.ext fun i j => congrArg Prod.snd (he1 _)))
  refine ⟨δ, fun i => -l i, c, fun i j => ⟨⟨e _, ⟨mem_closedBall_zero_iff.2 ?_, .inl fun v => ?_⟩, e.symm_apply_apply _⟩,
    ⟨e _, ⟨mem_closedBall_zero_iff.2 ?_, .inr ⟨_, fun v => (H' i j v).2, ?_⟩⟩, e.symm_apply_apply _⟩⟩,
    congrArg Units.val (mul_inv_cancel_left (dg (halfE F E) fun i => -l i) (bc (inclR (F := F) (AF F)) δ * β)).symm⟩
  · change ‖(bc p₁ c).1 i j‖ ≤ C
    rw [h5]; exact (h3 i j).1
  · change (bc p₂ c).1 i j v ∈ _
    rw [h6]; exact (H' i j v).1
  · change ‖(bc p₁ c⁻¹).1 i j‖ ≤ C
    rw [map_inv, h5]; exact (h3 i j).2
  · change _ = (bc p₂ c⁻¹).1 i j
    beta_reduce
    rw [← mul_assoc, ← map_natCast (algebraMap E (FiniteAdeleRing (𝓞 E) E)), ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 hM.ne'), map_one, one_mul, map_inv, h6, _root_.mul_inv_rev, ← map_inv (bc _) δ]
    rfl

end Reduction

section Adelic

open scoped TensorProduct
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}

theorem summable_hgt (hc : IsCMExt F E σ) (hσ : ∀ x, σ (σ x) = x) (h : Q = dblGram finSumFinEquiv J) (hJ : IsHermND σ J)
    {K : Subgroup (GAd σ Q)} (hK : IsCompact (K : Set (GAd σ Q))) (hI : HasIwasawa σ Q K) {X : Type} {γ : X → GAd σ Q}
    (hγ : ∀ q, γ q ∈ AdelicU.ratPts σ Q) (hi : ∀ q q', γ q' * (γ q)⁻¹ ∈ siegelH (AF F) σ Q → q = q') {t : ℝ}
    (ht : (n : ℝ) < t) : Summable fun q => (hgtH σ Q (absE F E) K (γ q) : ℝ) ^ t := by
  haveI := hc.1
  haveI := t2Space_adeleRing' (F := F)
  haveI := isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI := t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  haveI : Nontrivial (AF F) := inferInstanceAs (Nontrivial (Ainf F × Af F))
  haveI : Nontrivial (AF F ⊗[F] E) := inferInstance
  letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  letI : Invertible (2 : AF F ⊗[F] E) := (Invertible.map (algebraMap F (AF F ⊗[F] E)) 2).copy _ (map_ofNat _ 2).symm
  choose p k hk e using fun q => hI (γ q)
  obtain ⟨U, hU⟩ := (isUnit_iff_isUnit_det _).2 (isUnit_det_JR (F := F) (R := AF F) hJ.2)
  obtain ⟨Ω₀, C₀, hΩ₀, hcov⟩ := GlobalTheory.T.exists_adele_cover_mod_field_shrunk_compact F
  have hb : (1 : ℝ) < 4 ^ Fintype.card (InfinitePlace F) := one_lt_pow₀ (by norm_num) Fintype.card_ne_zero
  have hsc : Continuous (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) :=
    haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
    IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ).toLinearMap
  obtain ⟨C, m, h1, h2⟩ := core (inclR (F := F) (AF F)) finSumFinEquiv hsc (sigR_invol hσ)
    (by rintro _ ⟨x, rfl⟩; exact ⟨σ x, rfl⟩) (sigR_halfE σ) continuous_absE (absE_conjUnit σ)
    (fun x ⟨y, hy⟩ => by
      have h0 : y ≠ 0 := by rintro rfl; exact x.ne_zero (hy.symm.trans (map_zero _))
      rw [show x = Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 y h0) from Units.ext hy.symm, absE_inclR])
    (one_pos.trans hb) (by rw [GlobalTheory.T.tensorIdeleNormalizedAbs_ideleHalfAtInfinity F E σ hc]; simp) (GlobalTheory.T.compact_adeles_rational_points_finite_eventually_zero F E) (red_gl F E σ hc n)
    (by simpa only [← pow_mul, mul_comm _ 2, Fintype.card_fin, show (4 : ℝ) = 2 ^ 2 by norm_num] using
      GlobalTheory.T.skewHermitian_adelic_cover_of_adele_cover F E σ hc _ _ _ hΩ₀ hcov n)
    (U := U) (by rw [hU]; ext i j; exact congrArg (fun x => (1 : AF F) ⊗ₜ[F] x) (hJ.1 i j))
    ((mem_rat _).2 fun a b => hU ▸ ⟨J a b, rfl⟩) (p := fun q => matHom _ σ Q (p q)) (k := fun q => matHom _ σ Q (k q))
    (fun q => by
      rw [hU, ← JR_dblGram, ← h]
      exact (p q).1.2)
    (fun q => mem_siegelOf.1 (p q).2)
    (Bdd.map (f := k) ⟨_, hK, hk⟩ (isEmbedding_matHom _ σ Q).continuous)
    (fun q => by
      obtain ⟨x, -, hx⟩ := hγ q
      exact ⟨x, hx.trans (by rw [← map_mul, ← e]; rfl)⟩)
    fun q q' hq => hi q q' (by
      rw [← map_mul, ← map_mul, ← e, ← e, ← map_inv, ← map_mul] at hq
      exact hq)
  refine GlobalTheory.T.summable_rpow_of_fibre_card_le' X n _ C t m _ hb ht (fun q => ⟨NNReal.coe_nonneg _, ?_⟩) (by simpa only [Fintype.card_fin] using h2)
  rw [e, hgtH_mul continuous_absE hK _ (hk q)]
  exact h1 q _ rfl

end Adelic

end GlobalTheory.Eis.Conv

namespace GlobalTheory.Eis

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sphConv : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)),
    GlobalTheory.Doubling.HasIwasawa D.sp.cm.sig (GlobalTheory.Doubling.dblSp V).gram (GlobalTheory.Doubling.Khat V a) → GlobalTheory.Eis.SphConv V a := by
  intro D V a hI σ hσ
  have hc := GlobalTheory.AdelicU.isCMExt_host D
  have hs : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hc.2.2.2, hc.2.2.2, star_star])
  refine Conv.summable_hgt hc hs (GlobalTheory.Doubling.gram_hdbl V) (GlobalTheory.Doubling.isHermND_gram V)
    (GlobalTheory.Doubling.isCompact_Khat V a) hI (fun q : SiegelCosets V => q.out.2) (fun q q' h => ?_) (by linarith)
  rw [← q.out_eq, ← q'.out_eq]
  exact GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨q'.out * q.out⁻¹, h⟩, inv_mul_cancel_right _ _⟩

end GlobalTheory.Eis

end
