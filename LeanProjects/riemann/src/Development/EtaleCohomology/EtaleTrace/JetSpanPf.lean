import Development.EtaleCohomology.EtaleTrace.LCoverCut

noncomputable section
open MvPolynomial

namespace LateralTheory.EtaleTrace.JetSpanPf

variable {k K : Type} [Field k] [Field K] [Algebra k K]

lemma aeval_mem_adj {n : ℕ} (v : Fin n → K) (g : MvPolynomial (Fin n) k) :
    aeval v g ∈ Algebra.adjoin k (Set.range v) := by
  rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨g, rfl⟩

lemma essFT {n : ℕ} (v : Fin n → K)
    (hz : ∀ z : K, ∃ f g : MvPolynomial (Fin n) k, z = aeval v g / aeval v f) :
    Algebra.EssFiniteType k K := by
  classical
  rw [Algebra.essFiniteType_iff]
  refine ⟨Finset.univ.image v, fun z => ?_⟩
  have hs : ((Finset.univ.image v : Finset K) : Set K) = Set.range v := by simp
  rw [hs]
  obtain ⟨f, g, rfl⟩ := hz z
  by_cases h : aeval v f = 0
  · refine ⟨1, Subalgebra.one_mem _, isUnit_one, ?_⟩
    simp [h]
  · refine ⟨aeval v f, aeval_mem_adj v f, IsUnit.mk0 _ h, ?_⟩
    rw [div_mul_cancel₀ _ h]; exact aeval_mem_adj v g

def T {n : ℕ} (v : Fin n → K) : Submodule K Ω[K⁄k] :=
  (Submodule.span K (Set.range (LateralTheory.EtaleTrace.Cov.jet k v))).comap (LinearMap.inr K K Ω[K⁄k])

lemma fst_mem {n : ℕ} (v : Fin n → K) (i : Fin n) (hi : v i = 1) (x : K) :
    ((x, 0) : K × Ω[K⁄k]) ∈ Submodule.span K (Set.range (LateralTheory.EtaleTrace.Cov.jet k v)) := by
  have h := Submodule.smul_mem (Submodule.span K (Set.range (LateralTheory.EtaleTrace.Cov.jet k v))) x
    (Submodule.subset_span ⟨i, rfl⟩)
  simpa [LateralTheory.EtaleTrace.Cov.jet, hi] using h

lemma dv_mem {n : ℕ} (v : Fin n → K) (i : Fin n) (hi : v i = 1) (j : Fin n) :
    KaehlerDifferential.D k K (v j) ∈ T v := by
  have h1 : LateralTheory.EtaleTrace.Cov.jet k v j ∈ Submodule.span K (Set.range (LateralTheory.EtaleTrace.Cov.jet k v)) :=
    Submodule.subset_span ⟨j, rfl⟩
  have h2 := Submodule.sub_mem _ h1 (fst_mem v i hi (v j))
  show LinearMap.inr K K Ω[K⁄k] (KaehlerDifferential.D k K (v j)) ∈
    Submodule.span K (Set.range (LateralTheory.EtaleTrace.Cov.jet k v))
  convert h2 using 1
  simp [LateralTheory.EtaleTrace.Cov.jet]

lemma dpoly_mem {n : ℕ} (v : Fin n → K) (i : Fin n) (hi : v i = 1) (g : MvPolynomial (Fin n) k) :
    KaehlerDifferential.D k K (aeval v g) ∈ T v := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add]; exact Submodule.add_mem _ hp hq
  | mul_X p j hp =>
    rw [map_mul, aeval_X, Derivation.leibniz]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (dv_mem v i hi j)) (Submodule.smul_mem _ _ hp)

lemma dall_mem {n : ℕ} (v : Fin n → K) (i : Fin n) (hi : v i = 1)
    (hz : ∀ z : K, ∃ f g : MvPolynomial (Fin n) k, z = aeval v g / aeval v f) (z : K) :
    KaehlerDifferential.D k K z ∈ T v := by
  obtain ⟨f, g, hfg⟩ := hz z
  by_cases h : aeval v f = 0
  · rw [hfg, h, div_zero, map_zero]; exact Submodule.zero_mem _
  · have hg : aeval v g = z * aeval v f := by rw [hfg, div_mul_cancel₀ _ h]
    have key := congrArg (KaehlerDifferential.D k K) hg
    rw [Derivation.leibniz] at key

    have : KaehlerDifferential.D k K z =
        (aeval v f)⁻¹ • (KaehlerDifferential.D k K (aeval v g) - z • KaehlerDifferential.D k K (aeval v f)) := by
      rw [key, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ h, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (dpoly_mem v i hi g)
      (Submodule.smul_mem _ _ (dpoly_mem v i hi f)))

end LateralTheory.EtaleTrace.JetSpanPf

open LateralTheory.EtaleTrace.JetSpanPf in
theorem LateralTheory.EtaleTrace.Cov.JetSpan_of : LateralTheory.EtaleTrace.Cov.JetSpan := by
  intro k K _ _ _ n v i hi hz
  refine ⟨?_, essFT v hz⟩
  rw [eq_top_iff]
  rintro ⟨x, ω⟩ -
  have hω : ω ∈ T (k := k) v := by
    have : (⊤ : Submodule K Ω[K⁄k]) ≤ T v := by
      rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
      rintro _ ⟨z, rfl⟩; exact dall_mem v i hi hz z
    exact this Submodule.mem_top
  have : ((x, ω) : K × Ω[K⁄k]) = (x, 0) + LinearMap.inr K K Ω[K⁄k] ω := by simp
  rw [this]
  exact Submodule.add_mem _ (fst_mem v i hi x) hω
