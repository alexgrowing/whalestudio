import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CoveringRadiusStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Transference
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BabaiCovering
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ConjugateConjugate

namespace GlobalTheory.CMTransference

open NumberField Matrix Module Submodule ReciprocityTheory.MultiplicativeHeights ComplexConjugate

theorem exists_short_family {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ V) (bd : ι → V)
    (hd : ∀ i j, inner ℝ (b i) (bd j) = if i = j then 1 else 0) (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ x ∈ span ℤ (Set.range bd), x ≠ 0 → lam ≤ ‖x‖) :
    ∃ y : Fin (finrank ℝ V) → V, (∀ i, y i ∈ span ℤ (Set.range b)) ∧ LinearIndependent ℝ y ∧
      ∀ i, ‖y i‖ ≤ (finrank ℝ V : ℝ) ^ 2 / lam := by
  classical
  set n := finrank ℝ V with hn
  have hcard : Fintype.card ι = n := (finrank_eq_card_basis b).symm
  have hli : LinearIndependent ℝ bd := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrArg (inner ℝ (b i)) hg
    simpa [inner_sum, real_inner_smul_right, hd] using this
  let Bd : Basis ι ℝ V := Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' hcard).ge
  have hBd : ∀ i, Bd i = bd i := fun i => Basis.mk_apply _ _ _
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let φ : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) := (stdOrthonormalBasis ℝ V).repr
  let B' : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := (Bd.reindex e).map φ.toLinearEquiv
  have hB' : ∀ j, B' j = φ (bd (e.symm j)) := fun j => by simp [B', hBd]
  have hmin' : ∀ x ∈ span ℤ (Set.range B'), x ≠ 0 → lam ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
    have hw : (∑ i, c i • B' i) = φ (∑ i, c i • bd (e.symm i)) := by
      simp [hB', map_sum, map_zsmul]
    have hwmem : (∑ i, c i • bd (e.symm i)) ∈ span ℤ (Set.range bd) :=
      sum_mem fun i _ => zsmul_mem (subset_span (Set.mem_range_self _)) _
    rw [hw, LinearIsometryEquiv.norm_map]
    refine hmin _ hwmem ?_
    intro h0
    apply hx0
    rw [hw, h0, map_zero]
  obtain ⟨y, hyli, hyint, hynorm⟩ := ReciprocityTheory.ChartRestriction.G.T0.transference_dual B' lam hlam hmin'
  let yV : Fin n → V := fun i => φ.symm (y i)
  have hyVint : ∀ i k, ∃ m : ℤ, inner ℝ (yV i) (bd k) = m := by
    intro i k
    obtain ⟨m, hm⟩ := hyint i (e k)
    refine ⟨m, ?_⟩
    rw [← hm, hB', Equiv.symm_apply_apply, ← LinearIsometryEquiv.inner_map_map φ]
    simp [yV]
  have hyVmem : ∀ i, yV i ∈ span ℤ (Set.range b) := by
    intro i
    have hrep : ∀ k, b.repr (yV i) k = inner ℝ (yV i) (bd k) := by
      intro k
      have h : inner ℝ (yV i) (bd k) = ∑ l, b.repr (yV i) l * inner ℝ (b l) (bd k) := by
        conv_lhs => rw [← b.sum_repr (yV i)]
        rw [sum_inner]
        simp_rw [real_inner_smul_left]
      rw [h]
      simp [hd]
    rw [← b.sum_repr (yV i)]
    refine sum_mem fun k _ => ?_
    obtain ⟨m, hm⟩ := hyVint i k
    rw [hrep, hm, Int.cast_smul_eq_zsmul]
    exact zsmul_mem (subset_span (Set.mem_range_self k)) m
  refine ⟨yV, hyVmem, hyli.map' φ.symm.toLinearEquiv.toLinearMap φ.symm.toLinearEquiv.ker,
    fun i => ?_⟩
  have : ‖yV i‖ = ‖y i‖ := by simp [yV]
  rw [this]
  exact hynorm i

section CMType

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {σ : ι → K →+* ℂ}

omit [NumberField K] [Fintype ι] in

theorem sumElim_bijective (hσ : Function.Injective σ)
    (hcm : ∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ) :
    Function.Bijective (Sum.elim σ fun i => ComplexEmbedding.conjugate (σ i)) := by
  have hcc : ∀ τ : K →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
    fun τ => by ext x; simp
  constructor
  · rintro (i | i) (j | j) h
    · exact congrArg _ (hσ h)
    · exact absurd ⟨i, h⟩ ((hcm (σ j)).1 ⟨j, rfl⟩)
    · exact absurd ⟨j, h.symm⟩ ((hcm (σ i)).1 ⟨i, rfl⟩)
    · have h' := congrArg ComplexEmbedding.conjugate h
      simp only [Sum.elim_inr, hcc] at h'
      exact congrArg _ (hσ h')
  · intro τ
    by_cases h : ∃ i, σ i = τ
    · obtain ⟨i, hi⟩ := h
      exact ⟨Sum.inl i, hi⟩
    · rw [hcm, not_not] at h
      obtain ⟨i, hi⟩ := h
      exact ⟨Sum.inr i, by simp only [Sum.elim_inr, hi, hcc]⟩

theorem finrank_eq_two_mul (hσ : Function.Injective σ)
    (hcm : ∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ) :
    finrank ℚ K = 2 * Fintype.card ι := by
  rw [← Embeddings.card K ℂ, ← Fintype.card_of_bijective (sumElim_bijective hσ hcm),
    Fintype.card_sum, two_mul]

theorem trace_eq_two_mul_sum_re (hσ : Function.Injective σ)
    (hcm : ∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ) (y : K) :
    (Algebra.trace ℚ K y : ℝ) = 2 * ∑ i, (σ i y).re := by
  have h1 := trace_eq_sum_embeddings (K := ℚ) (L := K) (E := ℂ) (x := y)
  have h2 : ∑ σ : K →ₐ[ℚ] ℂ, σ y = ∑ φ : K →+* ℂ, φ y :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => φ y) (fun σ => σ y)
      (fun φ => by simp [RingHom.equivRatAlgHom_apply])).symm
  rw [h2, ← (sumElim_bijective hσ hcm).sum_comp (fun φ : K →+* ℂ => φ y),
    Fintype.sum_sum_type] at h1
  have h := congrArg Complex.re h1
  simp only [Sum.elim_inl, Sum.elim_inr, ComplexEmbedding.conjugate_coe_eq, Complex.add_re,
    Complex.re_sum, Complex.conj_re] at h
  rw [two_mul, ← h]
  simp

end CMType

section Lattice

variable {K : Type} [Field K] [NumberField K] {r : ℕ}

theorem exists_ratBasis {L : Submodule (𝓞 K) (Fin r → K)} (hL : IsLattice L) :
    ∃ (n : ℕ) (b : Basis (Fin n) ℚ (Fin r → K)),
      ∀ x, x ∈ L ↔ x ∈ span ℤ (Set.range b) := by
  have : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.2 hL.1
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 K) L
  have : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  let b0 := Module.finBasis ℤ L
  let v : Fin (finrank ℤ L) → Fin r → K := fun i => (b0 i : Fin r → K)
  have hli : LinearIndependent ℤ v :=
    b0.linearIndependent.map' (L.subtype.restrictScalars ℤ) (by
      rw [LinearMap.ker_eq_bot]; exact Subtype.val_injective)
  have hmem : ∀ x, x ∈ L ↔ x ∈ span ℤ (Set.range v) := by
    intro x
    constructor
    · intro hx
      have h := congrArg Subtype.val (b0.sum_repr ⟨x, hx⟩)
      simp only [AddSubmonoidClass.coe_finsetSum] at h
      rw [← h]
      exact sum_mem fun i _ => zsmul_mem (subset_span (Set.mem_range_self i)) _
    · intro hx
      obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
      exact sum_mem fun i _ => zsmul_mem (b0 i).2 _
  have hsp : ⊤ ≤ span ℚ (Set.range v) := by
    have key : ∀ x ∈ span K (L : Set (Fin r → K)), ∀ k : K, k • x ∈ span ℚ (Set.range v) := by
      intro x hx
      induction hx using span_induction with
      | mem x hx =>
        intro k
        obtain ⟨m, hm0, hm⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ K).2
          (Algebra.IsAlgebraic.isAlgebraic k)).exists_integral_multiple
        have h1 : (⟨m • k, hm⟩ : 𝓞 K) • x ∈ L := L.smul_mem _ hx
        have h2 := span_le_restrictScalars ℤ ℚ _ ((hmem _).1 h1)
        have h3 : k • x = (m : ℚ)⁻¹ • ((⟨m • k, hm⟩ : 𝓞 K) • x) := by
          ext a
          have : (m : K) ≠ 0 := by exact_mod_cast hm0
          change k * x a = (m : ℚ)⁻¹ • ((m • k) * x a)
          rw [Rat.smul_def]
          push_cast
          rw [zsmul_eq_mul]
          field_simp
        rw [h3]
        exact smul_mem _ _ h2
      | zero => intro k; simp
      | add x y _ _ hx hy => intro k; rw [smul_add]; exact add_mem (hx k) (hy k)
      | smul a x _ hx => intro k; rw [smul_smul]; exact hx _
    intro x _
    simpa using key x (hL.2 ▸ mem_top) 1
  refine ⟨_, Basis.mk ((LinearIndependent.iff_fractionRing ℤ ℚ).1 hli) hsp, fun x => ?_⟩
  rw [Basis.coe_mk]
  exact hmem x

theorem h_add_left (S : HermForm K r) (x x' y : Fin r → K) :
    S.h (x + x') y = S.h x y + S.h x' y := by
  simp [HermForm.h, add_mul, Finset.sum_add_distrib]

theorem h_add_right (S : HermForm K r) (x y y' : Fin r → K) :
    S.h x (y + y') = S.h x y + S.h x y' := by
  simp [HermForm.h, mul_add, Finset.sum_add_distrib]

theorem h_smul_left (S : HermForm K r) (a : K) (x y : Fin r → K) :
    S.h (a • x) y = S.c a * S.h x y := by
  simp [HermForm.h, Finset.mul_sum, mul_assoc]

theorem h_smul_right (S : HermForm K r) (a : K) (x y : Fin r → K) :
    S.h x (a • y) = a * S.h x y := by
  simp only [HermForm.h, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

noncomputable def traceForm (S : HermForm K r) : LinearMap.BilinForm ℚ (Fin r → K) :=
  LinearMap.mk₂ ℚ (fun x y => Algebra.trace ℚ K (S.h x y))
    (fun x x' y => by rw [h_add_left, map_add])
    (fun q x y => by
      rw [← algebraMap_smul K q x, h_smul_left, ← map_smul, Algebra.smul_def]; simp)
    (fun x y y' => by rw [h_add_right, map_add])
    (fun q x y => by
      rw [← algebraMap_smul K q y, h_smul_right, ← map_smul, Algebra.smul_def])

theorem traceForm_apply (S : HermForm K r) (x y : Fin r → K) :
    traceForm S x y = Algebra.trace ℚ K (S.h x y) := rfl

theorem discr_smul_mem [IsCMField K] {S : HermForm K r} {L : Submodule (𝓞 K) (Fin r → K)}
    (hL : IsSelfDual S L) {z : Fin r → K} (hz : ∀ y ∈ L, ∃ k : ℤ, traceForm S z y = k) :
    (discr K : K) • z ∈ L := by
  refine hL.2 _ fun y hy => ?_
  have h := ReciprocityTheory.ChartRestriction.G.FD.d4l2_dual_int (S.h z y) fun γ => by
    obtain ⟨k, hk⟩ := hz _ (L.smul_mem γ hy)
    refine ⟨k, ?_⟩
    rw [← hk, traceForm_apply, mul_comm, ← h_smul_right]
    rfl
  refine ⟨⟨_, h⟩, ?_⟩
  rw [h_smul_left, map_intCast]
  rfl

end Lattice

section Embedding

variable {K : Type} [Field K] [NumberField K] {r : ℕ} {ι : Type} [Fintype ι]

omit [Fintype ι] in
theorem embVec_add (τ : K →+* ℂ) (x y : Fin r → K) :
    embVec τ (x + y) = embVec τ x + embVec τ y := by
  ext a; simp [embVec]

noncomputable def emb (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ) :
    (Fin r → K) →+ EuclideanSpace ℂ (ι × Fin r) :=
  AddMonoidHom.mk' (fun x => WithLp.toLp 2 fun ik => (Q ik.1 *ᵥ embVec (σ ik.1) x) ik.2)
    (fun x y => by ext ik; simp [embVec_add, mulVec_add])

noncomputable def embDual (p : ℕ) (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ) :
    (Fin r → K) →+ EuclideanSpace ℂ (ι × Fin r) :=
  AddMonoidHom.mk'
    (fun x => WithLp.toLp 2 fun ik => 2 * sgn p ik.2 * (Q ik.1 *ᵥ embVec (σ ik.1) x) ik.2)
    (fun x y => by ext ik; simp [embVec_add, mulVec_add, mul_add])

variable (p : ℕ) (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ)

theorem norm_emb_sub_sq (x : Fin r → K) (w : ι → Fin r → ℂ) :
    ‖(WithLp.toLp 2 fun ik : ι × Fin r => w ik.1 ik.2 : EuclideanSpace ℂ (ι × Fin r)) -
      emb σ Q x‖ ^ 2 = ∑ i, normSq (Q i *ᵥ embVec (σ i) x - w i) := by
  rw [norm_sub_rev, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl

theorem norm_emb_sq (x : Fin r → K) : ‖emb σ Q x‖ ^ 2 = majSq σ Q x := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl

theorem norm_embDual_sq (x : Fin r → K) : ‖embDual p σ Q x‖ ^ 2 = 4 * majSq σ Q x := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, majSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [normSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  change ‖2 * sgn p k * (Q i *ᵥ embVec (σ i) x) k‖ ^ 2 = _
  have : ‖sgn p k‖ = 1 := by unfold sgn; split_ifs <;> simp
  rw [norm_mul, norm_mul, this]
  simp only [Complex.norm_ofNat]
  ring

theorem majSq_intCast_smul (d : ℤ) (x : Fin r → K) :
    majSq σ Q ((d : K) • x) = (d : ℝ) ^ 2 * majSq σ Q x := by
  rw [← norm_emb_sq, ← norm_emb_sq, Int.cast_smul_eq_zsmul, map_zsmul,
    ← Int.cast_smul_eq_zsmul ℝ, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

theorem normSq_le_majSq (i : ι) (x : Fin r → K) :
    normSq (Q i *ᵥ embVec (σ i) x) ≤ majSq σ Q x :=
  Finset.single_le_sum (f := fun i => normSq (Q i *ᵥ embVec (σ i) x))
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)

variable {p σ Q}

theorem inner_emb_embDual {S : HermForm K r} (hσ : Function.Injective σ)
    (hcm : ∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ)
    (hQ : ∀ i x y, σ i (S.h x y) = jForm p (Q i *ᵥ embVec (σ i) x) (Q i *ᵥ embVec (σ i) y))
    (x y : Fin r → K) :
    inner ℝ (emb σ Q y) (embDual p σ Q x) = (traceForm S x y : ℝ) := by
  rw [traceForm_apply, trace_eq_two_mul_sum_re hσ hcm, PiLp.inner_apply, Fintype.sum_prod_type,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hQ, jForm, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.inner]
  change (2 * sgn p k * (Q i *ᵥ embVec (σ i) x) k * conj ((Q i *ᵥ embVec (σ i) y) k)).re = _
  unfold sgn
  split_ifs <;> simp <;> ring

end Embedding

theorem cmApproximation_transference : ReciprocityTheory.ChartRestriction.G.FD.CoveringRadiusStatement := by
  classical
  intro K _ _ _ ι _ _ r p S σ Q L la hσ hcm _ hla _ hQ hL hsd hmin μ
  set d : ℝ := |(discr K : ℝ)| with hd
  have hd0 : 0 < d := abs_pos.2 (by exact_mod_cast discr_ne_zero K)

  have hdual : ∀ z : Fin r → K, z ≠ 0 → (∀ y ∈ L, ∃ k : ℤ, traceForm S z y = k) →
      la ^ 2 ≤ d ^ 2 * majSq σ Q z := by
    intro z hz0 hz
    obtain ⟨i, hi⟩ := hmin _ (discr_smul_mem hsd hz)
      (smul_ne_zero (by exact_mod_cast discr_ne_zero K) hz0)
    have := hi.trans (normSq_le_majSq σ Q i _)
    rwa [majSq_intCast_smul, ← sq_abs (discr K : ℝ)] at this
  have hnd : (traceForm S).Nondegenerate := by
    refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun z hz => ?_
    by_contra hz0
    obtain ⟨m, hm⟩ := exists_nat_gt (d ^ 2 * majSq σ Q z / la ^ 2)
    have hm0 : ((m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have h1 := hdual (((m + 1 : ℕ) : ℚ)⁻¹ • z) (smul_ne_zero (inv_ne_zero hm0) hz0)
      (fun y _ => ⟨0, by rw [map_smul, LinearMap.smul_apply, hz y]; simp⟩)
    have h2 := majSq_intCast_smul σ Q ((m + 1 : ℕ) : ℤ) (((m + 1 : ℕ) : ℚ)⁻¹ • z)
    rw [Int.cast_smul_eq_zsmul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, Int.cast_natCast,
      mul_inv_cancel₀ hm0, one_smul] at h2
    rw [div_lt_iff₀ (by positivity), h2] at hm
    push_cast at hm h1
    have h3 := mul_le_mul_of_nonneg_left h1 (sq_nonneg ((m : ℝ) + 1))
    have h4 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h5 : 0 < la ^ 2 := by positivity
    nlinarith [mul_nonneg (mul_nonneg h4 h4) h5.le, mul_nonneg h4 h5.le]
  obtain ⟨n, b, hb⟩ := exists_ratBasis hL
  let b' := (traceForm S).dualBasis hnd b
  have hV : finrank ℝ (EuclideanSpace ℂ (ι × Fin r)) = 2 * (Fintype.card ι * r) := by
    rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, finrank_euclideanSpace,
      Fintype.card_prod, Fintype.card_fin]
  have hK : finrank ℚ (Fin r → K) = 2 * (Fintype.card ι * r) := by
    rw [← Module.finrank_mul_finrank ℚ K, finrank_eq_two_mul hσ hcm, Module.finrank_fin_fun,
      mul_assoc]
  have hn : Fintype.card (Fin n) = finrank ℝ (EuclideanSpace ℂ (ι × Fin r)) := by
    rw [hV, ← hK, finrank_eq_card_basis b]
  have hinner : ∀ i j, inner ℝ (emb σ Q (b i)) (embDual p σ Q (b' j)) =
      if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [inner_emb_embDual hσ hcm hQ, LinearMap.BilinForm.apply_dualBasis_left]
    split_ifs <;> simp
  have hli : LinearIndependent ℝ fun i => emb σ Q (b i) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have := congrArg (fun v => inner ℝ v (embDual p σ Q (b' j))) hg
    simpa [sum_inner, real_inner_smul_left, hinner] using this
  let B : Basis (Fin n) ℝ (EuclideanSpace ℂ (ι × Fin r)) :=
    Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' hn).ge
  have hB : ∀ i, B i = emb σ Q (b i) := fun i => Basis.mk_apply _ _ _
  have hBmem : ∀ x ∈ span ℤ (Set.range B), ∃ l ∈ L, emb σ Q l = x := by
    intro x hx
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
    refine ⟨∑ i, c i • b i, (hb _).2
      (sum_mem fun i _ => zsmul_mem (subset_span (Set.mem_range_self i)) _), ?_⟩
    simp only [map_sum, map_zsmul, hB]
  have hlam : 0 < 2 * la / d := by positivity
  have hmin' : ∀ x ∈ span ℤ (Set.range fun j => embDual p σ Q (b' j)), x ≠ 0 →
      2 * la / d ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
    have hw : ∑ i, c i • embDual p σ Q (b' i) = embDual p σ Q (∑ i, c i • b' i) := by
      simp only [map_sum, map_zsmul]
    rw [hw] at hx0 ⊢
    have h1 := hdual (∑ i, c i • b' i) (fun h => hx0 (by rw [h, map_zero])) (by
      intro y hy
      obtain ⟨e, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 ((hb y).1 hy)
      refine ⟨∑ i, c i * e i, ?_⟩
      have hbb : ∀ i j, traceForm S (b' i) (b j) = if j = i then 1 else 0 :=
        LinearMap.BilinForm.apply_dualBasis_left hnd b
      simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, hbb]
      simp [mul_comm])
    refine (pow_le_pow_iff_left₀ hlam.le (norm_nonneg _) two_ne_zero).1 ?_
    rw [norm_embDual_sq, div_pow, div_le_iff₀ (by positivity)]
    linarith
  have hinner' : ∀ i j, inner ℝ (B i) (embDual p σ Q (b' j)) = if i = j then (1 : ℝ) else 0 :=
    fun i j => by rw [hB, hinner]
  set t : ℕ := Fintype.card ι * r with ht
  have hμ : μ = 4 * (t : ℝ) ^ 3 * (d / la) := by
    simp only [μ, ReciprocityTheory.ChartRestriction.G.FD.d5mu, ht]
    push_cast
    ring
  have htt : (t : ℝ) ≤ (t : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow two_ne_zero t
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hq : 0 < d / la := by positivity
  have hbound : ((2 * t : ℕ) : ℝ) ^ 2 / (2 * la / d) = 2 * (t : ℝ) ^ 2 * (d / la) := by
    push_cast
    field_simp
  refine ⟨fun w => ?_, ?_⟩
  · obtain ⟨x, hx, hxb⟩ := ReciprocityTheory.ChartRestriction.G.FD.BabaiCovering.cover B _ hinner' _ hlam hmin'
      (WithLp.toLp 2 fun ik : ι × Fin r => w ik.1 ik.2)
    obtain ⟨l, hl, rfl⟩ := hBmem x hx
    refine ⟨l, hl, ?_⟩
    rw [norm_emb_sub_sq, hV, hbound] at hxb
    refine hxb.trans ?_
    rw [hμ]
    push_cast
    have h1 := mul_le_mul_of_nonneg_right htt
      (by positivity : (0 : ℝ) ≤ (t : ℝ) ^ 4 * (d / la) ^ 2)
    have h2 : (0 : ℝ) ≤ (t : ℝ) ^ 6 * (d / la) ^ 2 := by positivity
    nlinarith
  · obtain ⟨y, hy, hyli, hyn⟩ := exists_short_family B _ hinner' _ hlam hmin'
    choose l hl hly using fun i => hBmem _ (hy i)
    have hlZ : LinearIndependent ℤ l := by
      refine LinearIndependent.of_comp (emb σ Q).toIntLinearMap ?_
      have : (emb σ Q).toIntLinearMap ∘ l = y := funext hly
      rw [this]
      exact hyli.restrict_scalars' ℤ
    have hlQ : LinearIndependent ℚ l := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hlZ
    have hspQ : span ℚ (Set.range l) = ⊤ :=
      hlQ.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hV, hK])
    have hspK : ⊤ ≤ span K (Set.range l) := fun x _ =>
      span_le_restrictScalars ℚ K _ (hspQ ▸ mem_top)
    let c := (Basis.ofSpan hspK).reindex
      ((Basis.ofSpan hspK).indexEquiv (Pi.basisFun K (Fin r)))
    have hc : ∀ j, ∃ i, l i = c j := fun j =>
      Basis.ofSpan_subset hspK ⟨_, (Basis.reindex_apply _ _ j).symm⟩
    refine ⟨c, fun j => ?_, c.linearIndependent, fun j => ?_⟩
    · obtain ⟨i, hi⟩ := hc j
      exact hi ▸ hl i
    · obtain ⟨i, hi⟩ := hc j
      have h0 := hyn i
      rw [← hi, ← norm_emb_sq, hly]
      refine pow_le_pow_left₀ (norm_nonneg _) (h0.trans ?_) 2
      rw [hV, hbound, hμ]
      have h1 := mul_le_mul_of_nonneg_right htt
        (by positivity : (0 : ℝ) ≤ (t : ℝ) * (d / la))
      have h2 : (0 : ℝ) ≤ (t : ℝ) ^ 3 * (d / la) := by positivity
      nlinarith

end GlobalTheory.CMTransference
