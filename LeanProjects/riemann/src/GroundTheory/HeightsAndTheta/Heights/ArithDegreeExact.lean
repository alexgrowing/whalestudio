import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithDegree
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes

namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

section Span

variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) (σ : K →+* ℂ)

theorem mem_span_fibreVec {ι : Type*} [Fintype ι] {s : ι → E} (hs : LinearIndependent (𝓞 K) s)
    (hcard : Fintype.card ι = Module.finrank (𝓞 K) E) (y : Fibre σ E) :
    FibreSpace.equiv h σ y ∈ Submodule.span ℂ (Set.range fun i ↦ fibreVec h σ (s i)) := by
  have hfin := finite_quotient_span hs hcard
  set n := Nat.card (E ⧸ Submodule.span (𝓞 K) (Set.range s))
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  set W := Submodule.span ℂ (Set.range fun i ↦ fibreVec h σ (s i))
  have key : ∀ e : E, fibreVec h σ e ∈ W := by
    intro e
    have hmem : (n : 𝓞 K) • e ∈ Submodule.span (𝓞 K) (Set.range s) := by
      have := card_nsmul_eq_zero' (G := E ⧸ Submodule.span (𝓞 K) (Set.range s))
        (x := Submodule.Quotient.mk e)
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
      rwa [Nat.cast_smul_eq_nsmul]
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hmem
    have h1 : fibreVec h σ ((n : 𝓞 K) • e) = (n : ℂ) • fibreVec h σ e := by
      rw [fibreVec_smul]
      congr 1
      simp
    have h2 : fibreVec h σ ((n : 𝓞 K) • e) ∈ W := by
      rw [← hc, fibreVec_sum]
      exact Submodule.sum_mem _ fun i _ ↦ W.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [h1] at h2
    have := W.smul_mem ((n : ℂ)⁻¹) h2
    rwa [smul_smul, inv_mul_cancel₀ hn, one_smul] at this
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact W.zero_mem
  | tmul z e =>
    have : FibreSpace.equiv h σ (z ⊗ₜ e) = ((ofComplex σ).symm z) • fibreVec h σ e := by
      rw [fibreVec, ← map_smul, smul_tmul', complex_smul_def, mul_one, AlgEquiv.apply_symm_apply]
    rw [this]
    exact W.smul_mem _ (key e)
  | add x y hx hy => rw [map_add]; exact W.add_mem hx hy

end Span

omit [NumberField K] in

theorem lTensor_complex_smul (σ : K →+* ℂ) {M N : Type*} [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N] (f : M →ₗ[𝓞 K] N) (c : ℂ) (x : Fibre σ M) :
    f.lTensor (ComplexAt σ) (c • x) = c • f.lTensor (ComplexAt σ) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul z m => rw [smul_tmul', LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

section GramBlock

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem det_gram_im {n : Type*} [Fintype n] [DecidableEq n] (v : n → V) :
    (det (gram ℂ v)).im = 0 :=
  ((Complex.nonneg_iff.mp (posSemidef_gram ℂ v).det_nonneg).2).symm

theorem det_gram_sumElim {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (a : m → V) (b q : n → V) (C : Matrix m n ℂ) (hq : ∀ j, q j = b j - ∑ i, C i j • a i)
    (horth : ∀ i j, inner ℂ (a i) (q j) = 0) :
    det (gram ℂ (Sum.elim a b)) = det (gram ℂ a) * det (gram ℂ q) := by
  let T : Matrix (m ⊕ n) (m ⊕ n) ℂ := fromBlocks 1 (-C) 0 1
  have h1 : Sum.elim a q = fun k ↦ ∑ l, T l k • Sum.elim a b l := by
    funext k
    rcases k with i | j
    · simp [T, Fintype.sum_sum_type, one_apply, ite_smul]
    · simp only [T, Fintype.sum_sum_type, Sum.elim_inr, Sum.elim_inl, fromBlocks_apply₁₂,
        fromBlocks_apply₂₂, one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, hq j]
      simp only [Matrix.neg_apply, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]
      exact add_comm _ _
  have h2 : det T = 1 := by simp [T]
  have h3 : gram ℂ (Sum.elim a q) = fromBlocks (gram ℂ a) 0 0 (gram ℂ q) := by
    ext k l
    rcases k with i | j <;> rcases l with i' | j'
    · rfl
    · simp [gram_apply, horth]
    · simp [gram_apply, inner_eq_zero_symm.mp (horth i' j)]
    · rfl
  calc det (gram ℂ (Sum.elim a b)) = det (gram ℂ (Sum.elim a q)) := by
        rw [h1, gram_comb, det_mul, det_mul, det_conjTranspose, h2, star_one, one_mul, mul_one]
    _ = det (gram ℂ a) * det (gram ℂ q) := by rw [h3, det_fromBlocks_zero₂₁]

end GramBlock

def HermitianBundle.arithDegree (A : HermitianBundle K) : ℝ :=
  GroundTheory.Heights₂.Heights.arithDegree A.metric

namespace HermitianExtension

variable {E' E E'' : HermitianBundle K} (X : HermitianExtension E' E E'')

theorem proj_incl (y : E'.carrier) : X.proj (X.incl y) = 0 := X.exact.apply_apply_eq_zero y

include X in

theorem finrank_eq : Module.finrank (𝓞 K) E.carrier =
    Module.finrank (𝓞 K) E'.carrier + Module.finrank (𝓞 K) E''.carrier := by
  have h1 := rank_quotient_add_rank_of_isDomain (LinearMap.range X.incl)
  have hker : LinearMap.ker X.proj = LinearMap.range X.incl := X.exact.linearMap_ker_eq
  let e1 : (E.carrier ⧸ LinearMap.range X.incl) ≃ₗ[𝓞 K] E''.carrier :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      (X.proj.quotKerEquivOfSurjective X.proj_surjective)
  let e2 : E'.carrier ≃ₗ[𝓞 K] LinearMap.range X.incl :=
    LinearEquiv.ofInjective X.incl X.incl_injective
  rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank] at h1
  norm_cast at h1
  rw [e1.finrank_eq, ← e2.finrank_eq] at h1
  omega

variable {m n : Type*} [Fintype m] [Fintype n]

theorem linearIndependent_sumElim {s' : m → E'.carrier} {s'' : n → E''.carrier}
    {u : n → E.carrier} (hu : ∀ j, X.proj (u j) = s'' j) (hs' : LinearIndependent (𝓞 K) s')
    (hs'' : LinearIndependent (𝓞 K) s'') :
    LinearIndependent (𝓞 K) (Sum.elim (fun i ↦ X.incl (s' i)) u) := by
  rw [Fintype.linearIndependent_iff] at hs' hs'' ⊢
  intro g hg
  rw [Fintype.sum_sum_type] at hg
  simp only [Sum.elim_inl, Sum.elim_inr] at hg
  have h2 : ∑ j, g (Sum.inr j) • s'' j = 0 := by
    have := congrArg X.proj hg
    simpa [map_add, map_sum, map_smul, proj_incl, hu] using this
  have hr := hs'' _ h2
  have h1 : ∑ i, g (Sum.inl i) • s' i = 0 := by
    apply X.incl_injective
    simp only [hr, zero_smul, Finset.sum_const_zero, add_zero] at hg
    rw [map_sum, map_zero]
    simpa [map_smul] using hg
  have hl := hs' _ h1
  rintro (i | j)
  exacts [hl i, hr j]

theorem card_quotient_sumElim {s' : m → E'.carrier} {s'' : n → E''.carrier}
    {u : n → E.carrier} (hu : ∀ j, X.proj (u j) = s'' j) (hs'' : LinearIndependent (𝓞 K) s'') :
    Nat.card (E.carrier ⧸ Submodule.span (𝓞 K) (Set.range (Sum.elim (fun i ↦ X.incl (s' i)) u))) =
      Nat.card (E'.carrier ⧸ Submodule.span (𝓞 K) (Set.range s')) *
        Nat.card (E''.carrier ⧸ Submodule.span (𝓞 K) (Set.range s'')) := by
  set w := Sum.elim (fun i ↦ X.incl (s' i)) u
  set N := Submodule.span (𝓞 K) (Set.range w)
  set S := N ⊔ LinearMap.range X.incl
  rw [← Submodule.card_quotient_mul_card_quotient S N le_sup_left]
  congr 1
  · have hS : S.map N.mkQ = LinearMap.range (N.mkQ ∘ₗ X.incl) := by
      rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, LinearMap.range_comp]
    have hker : LinearMap.ker (N.mkQ ∘ₗ X.incl) = Submodule.span (𝓞 K) (Set.range s') := by
      ext x
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      constructor
      · intro hx
        obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hx
        rw [Fintype.sum_sum_type] at hg
        simp only [w, Sum.elim_inl, Sum.elim_inr] at hg
        have h2 : ∑ j, g (Sum.inr j) • s'' j = 0 := by
          have := congrArg X.proj hg
          simpa [map_add, map_sum, map_smul, proj_incl, hu] using this
        have hr := (Fintype.linearIndependent_iff.mp hs'') _ h2
        simp only [hr, zero_smul, Finset.sum_const_zero, add_zero] at hg
        have : X.incl (∑ i, g (Sum.inl i) • s' i) = X.incl x := by
          rw [← hg, map_sum]
          simp [map_smul]
        rw [← X.incl_injective this]
        exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      · intro hx
        have : X.incl x ∈ (Submodule.span (𝓞 K) (Set.range s')).map X.incl :=
          Submodule.mem_map_of_mem hx
        rw [Submodule.map_span] at this
        refine Submodule.span_mono ?_ this
        rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨Sum.inl i, rfl⟩
    rw [hS, ← hker]
    exact Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv.symm
  · set φ := (Submodule.span (𝓞 K) (Set.range s'')).mkQ ∘ₗ X.proj
    have hφ : Function.Surjective φ := (Submodule.mkQ_surjective _).comp X.proj_surjective
    have hker : LinearMap.ker φ = S := by
      apply le_antisymm
      · intro x hx
        simp only [φ, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
          Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
        obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hx
        have hy : x - ∑ j, b j • u j ∈ LinearMap.range X.incl := by
          rw [← X.exact.linearMap_ker_eq, LinearMap.mem_ker, map_sub, map_sum]
          simp only [map_smul, hu, hb, sub_self]
        have hN : ∑ j, b j • u j ∈ N :=
          Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩)
        have := Submodule.add_mem_sup hN hy
        rwa [add_sub_cancel] at this
      · refine sup_le ?_ ?_
        · rw [Submodule.span_le]
          rintro _ ⟨k, rfl⟩
          rcases k with i | j
          · simp [φ, w, proj_incl]
          · simp only [φ, w, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_comp,
              Function.comp_apply, Sum.elim_inr, hu, Submodule.mkQ_apply,
              Submodule.Quotient.mk_eq_zero]
            exact Submodule.subset_span ⟨j, rfl⟩
        · rintro _ ⟨y, rfl⟩
          simp [φ, proj_incl]
    rw [← hker]
    exact Nat.card_congr (φ.quotKerEquivOfSurjective hφ).toEquiv

end HermitianExtension

namespace HermitianExtension

variable {E' E E'' : HermitianBundle K} (X : HermitianExtension E' E E'')
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem gramDet_sumElim (σ : K →+* ℂ) {s' : m → E'.carrier} {s'' : n → E''.carrier}
    {u : n → E.carrier} (hu : ∀ j, X.proj (u j) = s'' j) (hs' : LinearIndependent (𝓞 K) s')
    (hcard' : Fintype.card m = Module.finrank (𝓞 K) E'.carrier) :
    gramDet E.metric σ (Sum.elim (fun i ↦ X.incl (s' i)) u) =
      gramDet E'.metric σ s' * gramDet E''.metric σ s'' := by
  let a : m → FibreSpace E.metric σ := fun i ↦ fibreVec E.metric σ (X.incl (s' i))
  let b : n → FibreSpace E.metric σ := fun j ↦ fibreVec E.metric σ (u j)
  let W := Submodule.span ℂ (Set.range a)
  have : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range a)
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hdec : ∀ j, ∃ p ∈ W, ∃ q ∈ Wᗮ, b j = p + q := fun j ↦ W.exists_add_mem_mem_orthogonal (b j)
  choose p hpW q hqW hb using hdec
  have hc : ∀ j, ∃ c : m → ℂ, ∑ i, c i • a i = p j :=
    fun j ↦ (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hpW j)
  choose c hc using hc
  have hq : ∀ j, q j = b j - ∑ i, (Matrix.of fun i j ↦ c j i) i j • a i := by
    intro j
    simp only [Matrix.of_apply, hc, hb j]
    abel
  have horth : ∀ i j, inner ℂ (a i) (q j) = 0 := fun i j ↦
    Submodule.inner_right_of_mem_orthogonal (K := W) (Submodule.subset_span (Set.mem_range_self i))
      (hqW j)
  have hfam : (fun k ↦ fibreVec E.metric σ (Sum.elim (fun i ↦ X.incl (s' i)) u k)) =
      Sum.elim a b := by
    funext k
    rcases k with i | j <;> rfl

  let L : FibreSpace E'.metric σ →ₗ[ℂ] FibreSpace E.metric σ :=
    { toFun := fun x ↦ X.incl.lTensor (ComplexAt σ) x
      map_add' := map_add _
      map_smul' := lTensor_complex_smul σ X.incl }
  let P : FibreSpace E.metric σ →ₗ[ℂ] FibreSpace E''.metric σ :=
    { toFun := fun x ↦ X.proj.lTensor (ComplexAt σ) x
      map_add' := map_add _
      map_smul' := lTensor_complex_smul σ X.proj }
  have hga : gram ℂ a = gram ℂ (fun i ↦ fibreVec E'.metric σ (s' i)) := by
    ext i k
    exact X.incl_isometric σ (1 ⊗ₜ s' i) (1 ⊗ₜ s' k)
  have hLW : ∀ w : Fibre σ E'.carrier, L (FibreSpace.equiv E'.metric σ w) ∈ W := by
    intro w
    have hw := Submodule.mem_map_of_mem (f := L) (mem_span_fibreVec E'.metric σ hs' hcard' w)
    rw [Submodule.map_span, ← Set.range_comp] at hw
    exact hw
  have hperp : ∀ j (w : Fibre σ E'.carrier),
      (E.metric.form σ).inner (X.incl.lTensor (ComplexAt σ) w) (q j) = 0 :=
    fun j w ↦ Submodule.inner_right_of_mem_orthogonal (hLW w) (hqW j)
  have hP : ∀ j, P (q j) = fibreVec E''.metric σ (s'' j) := by
    intro j
    rw [hq j, map_sub, map_sum]
    have h0 : ∀ i, P (a i) = 0 := fun i ↦ by
      change X.proj.lTensor (ComplexAt σ) ((1 : ComplexAt σ) ⊗ₜ X.incl (s' i)) = 0
      rw [LinearMap.lTensor_tmul, proj_incl, tmul_zero]
    simp only [map_smul, h0, smul_zero, Finset.sum_const_zero, sub_zero]
    change X.proj.lTensor (ComplexAt σ) ((1 : ComplexAt σ) ⊗ₜ u j) = _
    rw [LinearMap.lTensor_tmul, hu]
    rfl
  have hgq : gram ℂ q = gram ℂ (fun j ↦ fibreVec E''.metric σ (s'' j)) := by
    ext j k
    rw [gram_apply, gram_apply, ← hP j, ← hP k]
    exact (X.proj_coisometric σ (q j) (q k) (hperp j) (hperp k)).symm
  simp only [gramDet]
  rw [hfam, det_gram_sumElim a b q _ hq horth, hga, hgq, Complex.mul_re, det_gram_im,
    det_gram_im, mul_zero, sub_zero]

include X in

theorem arithDegree_eq_add : E.arithDegree = E'.arithDegree + E''.arithDegree := by
  obtain ⟨s', hs'⟩ := exists_linearIndependent_fin (K := K) (E := E'.carrier)
  obtain ⟨s'', hs''⟩ := exists_linearIndependent_fin (K := K) (E := E''.carrier)
  choose u hu using fun j ↦ X.proj_surjective (s'' j)
  have hw := X.linearIndependent_sumElim hu hs' hs''
  have hcard : Fintype.card (Fin (Module.finrank (𝓞 K) E'.carrier) ⊕
      Fin (Module.finrank (𝓞 K) E''.carrier)) = Module.finrank (𝓞 K) E.carrier := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, X.finrank_eq]
  simp only [HermitianBundle.arithDegree]
  rw [arithDegree_eq E.metric hw hcard, arithDegree_eq E'.metric hs' (Fintype.card_fin _),
    arithDegree_eq E''.metric hs'' (Fintype.card_fin _)]
  have hfin' := finite_quotient_span hs' (Fintype.card_fin _)
  have hfin'' := finite_quotient_span hs'' (Fintype.card_fin _)
  have hg : ∀ σ : K →+* ℂ, gramDet E.metric σ (Sum.elim (fun i ↦ X.incl (s' i)) u) =
      gramDet E'.metric σ s' * gramDet E''.metric σ s'' :=
    fun σ ↦ X.gramDet_sumElim σ hu hs' (Fintype.card_fin _)
  have hlog : ∀ σ : K →+* ℂ, Real.log (gramDet E'.metric σ s' * gramDet E''.metric σ s'') =
      Real.log (gramDet E'.metric σ s') + Real.log (gramDet E''.metric σ s'') := fun σ ↦
    Real.log_mul (gramDet_pos _ σ hs').ne' (gramDet_pos _ σ hs'').ne'
  simp only [degreeWith]
  rw [X.card_quotient_sumElim hu hs'', Nat.cast_mul,
    Real.log_mul (by exact_mod_cast Nat.card_pos.ne') (by exact_mod_cast Nat.card_pos.ne')]
  simp only [hg, hlog, Finset.sum_add_distrib]
  ring

end HermitianExtension

theorem HermitianBundle.arithDegree_integers : (HermitianBundle.integers K).arithDegree = 0 :=
  GroundTheory.Heights₂.Heights.arithDegree_integers

theorem HermitianBundle.arithDegree_standard_two : (HermitianBundle.standard K 2).arithDegree = 0 := by
  rw [(HermitianExtension.standardSplit K).arithDegree_eq_add,
    HermitianBundle.arithDegree_integers, add_zero]

end

end GroundTheory.Heights₂.Heights
