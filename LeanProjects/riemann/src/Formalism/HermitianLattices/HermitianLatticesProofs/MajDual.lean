import Mathlib
import Formalism.HermitianLattices.StatementMaj
import Formalism.HermitianLattices.HermitianLatticesProofs.MajLattice

open NumberField
open scoped nonZeroDivisors

noncomputable section

namespace Formalism.HermitianLatticesTheory

lemma majDual_trace {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (a : K) :
    ((Algebra.trace ℚ K a : ℚ) : ℝ) = 2 * ∑ v : InfinitePlace K, (v.embedding a).re := by
  have h1 : ((Algebra.trace ℚ K a : ℚ) : ℂ) = ∑ φ : K →+* ℂ, φ a := by
    rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings (E := ℂ)]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ : K →+* ℂ => φ a) (fun σ => σ a)
      fun _ => rfl).symm
  have hre : ((Algebra.trace ℚ K a : ℚ) : ℝ) = ∑ φ : K →+* ℂ, (φ a).re := by
    rw [← Complex.re_sum, ← h1, Complex.ratCast_re]
  classical
  rw [hre, ← Finset.sum_fiberwise Finset.univ InfinitePlace.mk (fun φ : K →+* ℂ => (φ a).re),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => (w.embedding a).re) ?_, Finset.sum_const, nsmul_eq_mul]
  · congr 1
    norm_cast
    convert InfinitePlace.card_filter_mk_eq w
    rw [InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.2
      (IsTotallyComplex.isComplex w))]
  · intro φ hφ
    have hw : InfinitePlace.mk φ = InfinitePlace.mk w.embedding := by
      rw [(Finset.mem_filter.1 hφ).2, InfinitePlace.mk_embedding]
    rcases InfinitePlace.mk_eq_iff.1 hw with h | h
    · rw [h]
    · rw [← h, NumberField.ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]

section
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

lemma majDual_herm (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V) (v : InfinitePlace K)
    (hst : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a)) (x y : V) :
    v.embedding (h x y) = dotProduct (star (vecAt b v x)) ((gramAt h b v).mulVec (vecAt b v y)) := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul,
    smul_eq_mul, map_mul, starRingEnd_apply, hst, RingHom.id_apply]
  simp only [dotProduct, Matrix.mulVec, vecAt, gramAt, Matrix.of_apply, Pi.star_apply]
  simp only [Finset.mul_sum]
  first
  | exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring1
  | (rw [Finset.sum_comm]
     exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring1)

lemma majDual_mat (G X : Matrix ι ι ℂ) (hX : IsUnit X.det) (a c : ι → ℂ) :
    dotProduct (star (X⁻¹.mulVec a)) (((X.conjTranspose * G * X)).mulVec (X⁻¹.mulVec c)) =
      dotProduct (star a) (G.mulVec c) := by
  have h1 : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv X hX
  have e1 : (X.conjTranspose * G * X).mulVec (X⁻¹.mulVec c) = X.conjTranspose.mulVec (G.mulVec c) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, h1, Matrix.mul_one, Matrix.mulVec_mulVec]
  rw [e1, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

lemma majDual_realize_apply (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V)
    (p : InfinitePlace K × ι × Fin 2) :
    realize b X x p = if p.2.2 = 0 then (fcoord b X p.1 x p.2.1).re
      else (fcoord b X p.1 x p.2.1).im := rfl

lemma majDual_jW_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (w : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) p :
    jW h b X w p = sgnAt h b X p.1 p.2.1 * w p := rfl

lemma majDual_sgn (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsFrame h b v (X v)) (v : InfinitePlace K) :
    (X v).conjTranspose * gramAt h b v * X v =
      Matrix.diagonal (fun i => ((sgnAt h b X v i : ℝ) : ℂ)) ∧
      ∀ i, sgnAt h b X v i = 1 ∨ sgnAt h b X v i = -1 := by
  obtain ⟨-, ε, hε, hXe⟩ := hX v
  have hs : ∀ i, sgnAt h b X v i = (ε i).re := fun i => by
    simp only [sgnAt, hXe, Matrix.diagonal_apply_eq]
  refine ⟨?_, fun i => ?_⟩
  · rw [hXe]
    congr 1
    funext i
    rw [hs]
    rcases hε i with h1 | h1 <;> simp [h1]
  · rw [hs]
    rcases hε i with h1 | h1 <;> simp [h1]

end

section
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

lemma majDual_re (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ)
    (hst : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a))
    (hX : ∀ v, IsFrame h b v (X v)) (v : InfinitePlace K) (x y : V) :
    (v.embedding (h x y)).re = ∑ i, sgnAt h b X v i * ((fcoord b X v x i).re * (fcoord b X v y i).re
      + (fcoord b X v x i).im * (fcoord b X v y i).im) := by
  obtain ⟨hu, -⟩ := hX v
  rw [majDual_herm h b v hst x y, ← majDual_mat (gramAt h b v) (X v) hu,
    (majDual_sgn h b X hX v).1]
  simp only [fcoord, dotProduct, Matrix.mulVec_diagonal, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring1

lemma majDual_inner [IsTotallyComplex K] (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ)
    (hst : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a))
    (hX : ∀ v, IsFrame h b v (X v)) (x y : V) :
    inner ℝ (realize b X x) (jW h b X (realize b X y)) =
      ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ) / 2 := by
  rw [majDual_trace, mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℝ) ≠ 0)]
  simp only [majDual_re h b X hst hX]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fintype.sum_prod_type,
    Fin.sum_univ_two, majDual_jW_apply, majDual_realize_apply, Fin.isValue, eq_self_iff_true,
    if_true, one_ne_zero, if_false, ↓reduceIte]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
  ring1

end

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]

lemma majDual_star_int (r : RingOfIntegers K) : IsIntegral ℤ (star (r : K)) := by
  exact (NumberField.RingOfIntegers.isIntegral_coe r).map (starRingEnd K).toIntAlgHom

lemma majDual_tdual (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (RingOfIntegers K) V) (y : V) :
    y ∈ tdual h L ↔ y ∈ dualI h L (invDiff K) := by
  simp only [tdual, dualI, invDiff, Set.mem_setOf_eq]
  constructor
  · intro hy x hx r
    have hr : IsIntegral ℤ (star (r : K)) := majDual_star_int r
    let r' : RingOfIntegers K := ⟨star (r : K), hr⟩
    have e : r' • x = (star (r : K)) • x := (IsScalarTower.algebraMap_smul K r' x).symm
    obtain ⟨z, hz⟩ := hy (r' • x) (L.smul_mem r' hx)
    refine ⟨z, ?_⟩
    rw [e, map_smulₛₗ h, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star] at hz
    rw [mul_comm]
    exact hz
  · intro hy x hx
    obtain ⟨z, hz⟩ := hy x hx 1
    refine ⟨z, ?_⟩
    have e1 : ((1 : RingOfIntegers K) : K) = 1 := rfl
    rw [e1, mul_one] at hz
    exact hz

abbrev majDualI (K : Type) [Field K] [NumberField K] :
    FractionalIdeal (RingOfIntegers K)⁰ K :=
  FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (RingOfIntegers K)⁰ K)

lemma majDual_memI (a : K) : a ∈ majDualI K ↔ a ∈ invDiff K := by
  have h10 : (1 : FractionalIdeal (RingOfIntegers K)⁰ K) ≠ 0 := by
    intro h0
    have h1 : (1 : K) ∈ (1 : FractionalIdeal (RingOfIntegers K)⁰ K) :=
      (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
    rw [h0, FractionalIdeal.mem_zero_iff] at h1
    exact one_ne_zero h1
  rw [majDualI, FractionalIdeal.mem_dual h10]
  constructor
  · intro h r
    obtain ⟨z, hz⟩ := RingHom.mem_range.1
      (h (algebraMap (RingOfIntegers K) K r) ((FractionalIdeal.mem_one_iff _).2 ⟨r, rfl⟩))
    rw [Algebra.traceForm_apply] at hz
    exact ⟨z, hz.symm.trans (eq_intCast (algebraMap ℤ ℚ) z)⟩
  · intro h x hx
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
    obtain ⟨z, hz⟩ := h r
    rw [RingHom.mem_range]
    refine ⟨z, ?_⟩
    rw [Algebra.traceForm_apply]
    exact (eq_intCast (algebraMap ℤ ℚ) z).trans hz.symm

end

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]

lemma majDual_invDiffSub : invDiffSub K = (majDualI K : Submodule (RingOfIntegers K) K) := by
  have e : invDiff K = ((majDualI K : Submodule (RingOfIntegers K) K) : Set K) := by
    ext a
    exact (majDual_memI a).symm
  rw [invDiffSub, e, Submodule.span_eq]

lemma majDual_unimod (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (RingOfIntegers K) V)
    (hU : IsUnimodular h L) (y : V) :
    y ∈ dualI h L (invDiff K) ↔ y ∈ idealSmul (invDiffSub K) L := by
  have h10 : (1 : FractionalIdeal (RingOfIntegers K)⁰ K) ≠ 0 := by
    intro h0
    have h1 : (1 : K) ∈ (1 : FractionalIdeal (RingOfIntegers K)⁰ K) :=
      (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
    rw [h0, FractionalIdeal.mem_zero_iff] at h1
    exact one_ne_zero h1
  have hne : majDualI K ≠ 0 := by
    first
    | exact FractionalIdeal.dual_ne_zero ℤ ℚ h10
    | exact FractionalIdeal.dual_ne_zero h10
  have hU' : dual h L = L := hU
  have hdual : ∀ x : V, x ∈ L ↔ ∀ z ∈ L, h z x ∈ (1 : Submodule (RingOfIntegers K) K) := by
    intro x
    conv_lhs => rw [← hU']
    simp only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply]
  have hD : ∀ x : V, x ∈ dualI h L (invDiff K) ↔
      ∀ z ∈ L, h z x ∈ (majDualI K : Submodule (RingOfIntegers K) K) := by
    intro x
    simp only [dualI, Set.mem_setOf_eq]
    exact forall₂_congr fun z _ => (majDual_memI (h z x)).symm
  rw [hD, majDual_invDiffSub]
  constructor
  · intro hy
    have hJ : ∀ d ∈ ((majDualI K)⁻¹ : FractionalIdeal (RingOfIntegers K)⁰ K), d • y ∈ L := by
      intro d hd
      rw [hdual]
      intro z hz
      rw [map_smul, smul_eq_mul, Submodule.mem_one]
      have hm : h z y * d ∈ majDualI K * (majDualI K)⁻¹ :=
        FractionalIdeal.mul_mem_mul (hy z hz) hd
      rw [mul_inv_cancel₀ hne, FractionalIdeal.mem_one_iff] at hm
      obtain ⟨r, hr⟩ := hm
      exact ⟨r, by rw [hr, mul_comm]⟩
    have h1 : (1 : K) ∈ ((majDualI K : Submodule (RingOfIntegers K) K) *
        (((majDualI K)⁻¹ : FractionalIdeal (RingOfIntegers K)⁰ K) :
          Submodule (RingOfIntegers K) K)) := by
      rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hne]
      exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
    have key : ∀ t ∈ ((majDualI K : Submodule (RingOfIntegers K) K) *
        (((majDualI K)⁻¹ : FractionalIdeal (RingOfIntegers K)⁰ K) :
          Submodule (RingOfIntegers K) K)),
        t • y ∈ idealSmul (majDualI K : Submodule (RingOfIntegers K) K) L := by
      intro t ht
      refine Submodule.mul_induction_on ht ?_ ?_
      · intro m hm n hn
        rw [mul_smul]
        exact Submodule.subset_span ⟨m, hm, n • y, hJ n hn, rfl⟩
      · intro a c ha hc
        rw [add_smul]
        exact Submodule.add_mem _ ha hc
    simpa using key 1 h1
  · intro hy
    unfold idealSmul at hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      intro w hw
      obtain ⟨r, hr⟩ := Submodule.mem_one.1 ((hdual x).1 hx w hw)
      rw [map_smul, smul_eq_mul, ← hr, mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ r ha
    | zero =>
      intro w _
      rw [map_zero]
      exact Submodule.zero_mem _
    | add a c _ _ ha hc =>
      intro w hw
      rw [map_add]
      exact Submodule.add_mem _ (ha w hw) (hc w hw)
    | smul r a _ ha =>
      intro w hw
      rw [← IsScalarTower.algebraMap_smul K r a, map_smul, smul_eq_mul, ← Algebra.smul_def]
      exact Submodule.smul_mem _ r (ha w hw)

end

section
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

lemma majDual_mem_zmap {R W : Type*} [Ring R] [Module R V] [AddCommGroup W] (f : V →+ W)
    (M : Submodule R V) (w : W) : w ∈ zmap f M ↔ ∃ y ∈ M, f y = w := by
  exact Iff.rfl

lemma majDual_realize_qsmul (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (q : ℚ) (x : V) : realize b X (algebraMap ℚ K q • x) = (q : ℝ) • realize b X x := by
  have hf : ∀ v : InfinitePlace K,
      fcoord b X v (algebraMap ℚ K q • x) = (q : ℂ) • fcoord b X v x := by
    intro v
    have hv : vecAt b v (algebraMap ℚ K q • x) = (q : ℂ) • vecAt b v x := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul]
      simp only [vecAt]
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, eq_ratCast (algebraMap ℚ K) q,
        map_ratCast]
    rw [fcoord, fcoord, hv, Matrix.mulVec_smul]
  ext p
  rw [PiLp.smul_apply, majDual_realize_apply, majDual_realize_apply, hf]
  split_ifs <;> simp

def majDualJ (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) :
    EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ]
      EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) where
  toFun := jW h b X
  map_add' := by
    intro u w; ext p; simp only [majDual_jW_apply, PiLp.add_apply]; ring
  map_smul' := by
    intro c u; ext p; simp only [majDual_jW_apply, PiLp.smul_apply, smul_eq_mul,
      RingHom.id_apply]; ring

lemma majDualJ_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (u : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) :
    majDualJ h b X u = jW h b X u := rfl

lemma majDual_jW_jW (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsFrame h b v (X v))
    (u : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) : jW h b X (jW h b X u) = u := by
  ext p
  rw [majDual_jW_apply, majDual_jW_apply, ← mul_assoc]
  rcases (majDual_sgn h b X hX p.1).2 p.2.1 with hs | hs <;> simp [hs]

variable [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]

lemma majDual_zdual [IsTotallyComplex K] (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ)
    (hst : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a))
    (hX : ∀ v, IsFrame h b v (X v)) (L : Submodule (RingOfIntegers K) V)
    [DiscreteTopology (zmap (realize b X) L)] [IsZLattice ℝ (zmap (realize b X) L)]
    (w : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) :
    w ∈ Formalism.HadamardInequality.zdual (zmap (realize b X) L) ↔
      ∃ y : V, (∀ x ∈ L, ∃ z : ℤ, Algebra.trace ℚ K (h x y) = 2 * z) ∧
        w = jW h b X (realize b X y) := by
  classical
  have hinner := majDual_inner h b X hst hX
  have hmemZ : ∀ u, u ∈ Formalism.HadamardInequality.zdual (zmap (realize b X) L) ↔
      ∀ x ∈ zmap (realize b X) L, ∃ z : ℤ, inner ℝ x u = z := fun u => Iff.rfl
  constructor
  swap
  · rintro ⟨y, hy, rfl⟩
    rw [hmemZ]
    intro x hx
    obtain ⟨x', hx', rfl⟩ := (majDual_mem_zmap (realize b X) L x).1 hx
    obtain ⟨z, hz⟩ := hy x' hx'
    refine ⟨z, ?_⟩
    rw [hinner, hz]
    (try push_cast) <;> ring
  intro hw
  rw [hmemZ] at hw
  set bZ := Module.Free.chooseBasis ℤ (zmap (realize b X) L) with hbZ
  set bb := bZ.ofZLatticeBasis ℝ (zmap (realize b X) L) with hbb
  have hbbΛ : ∀ i, bb i ∈ zmap (realize b X) L := fun i => by
    rw [hbb, Module.Basis.ofZLatticeBasis_apply]
    exact (bZ i).2
  have hm : ∀ i, ∃ m ∈ L, realize b X m = bb i := fun i =>
    (majDual_mem_zmap (realize b X) L (bb i)).1 (hbbΛ i)
  choose m hmL hmR using hm
  have hext : ∀ p q : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2),
      (∀ i, inner ℝ (bb i) p = inner ℝ (bb i) q) → p = q := by
    intro p q hpq
    apply ext_inner_left ℝ
    intro u
    rw [← bb.sum_repr u, sum_inner, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_left, real_inner_smul_left, hpq i]
  set Gq : Matrix (Module.Free.ChooseBasisIndex ℤ (zmap (realize b X) L))
    (Module.Free.ChooseBasisIndex ℤ (zmap (realize b X) L)) ℚ :=
    Matrix.of fun i k => Algebra.trace ℚ K (h (m i) (m k)) / 2 with hGq
  have hGr : ∀ i k, inner ℝ (bb i) (jW h b X (bb k)) = (Gq i k : ℝ) := by
    intro i k
    rw [← hmR i, ← hmR k, hinner, hGq, Matrix.of_apply]
    (try push_cast) <;> ring
  have hdet : Gq.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    set u := ∑ k, (v k : ℝ) • bb k with hu
    have hJu : jW h b X u = 0 := by
      apply hext
      intro i
      rw [inner_zero_right, ← majDualJ_apply, hu, map_sum, inner_sum]
      simp only [map_smul, real_inner_smul_right, majDualJ_apply, hGr]
      have h1 := congrFun hv i
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h1
      have h2 : ((∑ k, Gq i k * v k : ℚ) : ℝ) = 0 := by
        rw [h1]
        simp
      push_cast at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have hu0 : u = 0 := by
      rw [← majDual_jW_jW h b X hX u, hJu, ← majDualJ_apply, map_zero]
    apply hv0
    have hli := bb.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    funext k
    have h3 := hli (fun k => (v k : ℝ)) (hu.symm.trans hu0) k
    simp only [Pi.zero_apply]
    exact_mod_cast h3
  have hn : ∀ i, ∃ z : ℤ, inner ℝ (bb i) w = z := fun i => hw (bb i) (hbbΛ i)
  choose nz hnz using hn
  set qv := Matrix.mulVec Gq⁻¹ (fun i => (nz i : ℚ)) with hqv
  set y : V := ∑ k, (algebraMap ℚ K (qv k)) • m k with hy
  have htr : ∀ x : V, Algebra.trace ℚ K (h x y) =
      ∑ k, qv k * Algebra.trace ℚ K (h x (m k)) := by
    intro x
    rw [hy, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul, ← Algebra.smul_def, map_smul, smul_eq_mul]
  have hq : ∀ i, Algebra.trace ℚ K (h (m i) y) / 2 = nz i := by
    intro i
    have e1 : Matrix.mulVec Gq qv = fun i => (nz i : ℚ) := by
      rw [hqv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Gq (isUnit_iff_ne_zero.mpr hdet),
        Matrix.one_mulVec]
    have e2 := congrFun e1 i
    simp only [Matrix.mulVec, dotProduct] at e2
    rw [← e2, htr, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hGq, Matrix.of_apply]
    ring
  have hwy : w = jW h b X (realize b X y) := by
    apply hext
    intro i
    rw [hnz i, ← hmR i, hinner]
    have e3 := congrArg (fun q : ℚ => (q : ℝ)) (hq i)
    push_cast at e3
    exact e3.symm
  refine ⟨y, ?_, hwy⟩
  intro x hx
  obtain ⟨z, hz⟩ := hw (realize b X x) ((majDual_mem_zmap (realize b X) L _).2 ⟨x, hx, rfl⟩)
  refine ⟨z, ?_⟩
  rw [hwy, hinner] at hz
  have e4 : ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ) = ((2 * z : ℚ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast e4

end

theorem majDual : MajDual := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ h b X _ hst hX
  refine ⟨majDual_inner h b X hst hX, fun L hL => ?_⟩
  obtain ⟨hD, hS⟩ := majLattice K V ι b X (fun v => (hX v).1) L hL
  have hZ : IsZLattice ℝ (zmap (realize b X) L) := ⟨hS⟩
  refine ⟨⟨hD, hZ⟩, fun w => ?_, fun y => majDual_tdual h L y, fun hU y => majDual_unimod h L hU y⟩
  exact majDual_zdual h b X hst hX L w

end Formalism.HermitianLatticesTheory
