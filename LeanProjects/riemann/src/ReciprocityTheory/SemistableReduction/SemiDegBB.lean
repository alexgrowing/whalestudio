import ReciprocityTheory.SemistableReduction.SemiDegBA

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField

theorem relIndex_span_comb {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (b : Fin k → Fin r → K) (hb : LinearIndependent K b) (M : Matrix (Fin k) (Fin k) (𝓞 K))
    (hM : M.det ≠ 0) :
    (((Submodule.span (𝓞 K) (Set.range (fun j => ∑ i, M i j • b i))).toAddSubgroup.relIndex
      (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup : ℕ) : ℤ) = |Algebra.norm ℤ M.det| := by
  set P := Submodule.span (𝓞 K) (Set.range b) with hPdef
  set Q := Submodule.span (𝓞 K) (Set.range (fun j => ∑ i, M i j • b i)) with hQdef
  have hbO : LinearIndependent (𝓞 K) b := hb.restrict_scalars' (𝓞 K)
  let bP : Module.Basis (Fin k) (𝓞 K) P := Module.Basis.span hbO
  let f : P →ₗ[𝓞 K] P := Matrix.toLin bP bP M
  have hfb : ∀ j, ((f (bP j) : P) : Fin r → K) = ∑ i, M i j • b i := by
    intro j
    simp only [f, Matrix.toLin_self, bP, Submodule.coe_sum, Submodule.coe_smul]
    exact Finset.sum_congr rfl fun i _ => by rw [Module.Basis.span_apply]
  have hQ : Submodule.map P.subtype (LinearMap.range f) = Q := by
    rw [LinearMap.range_eq_map, ← bP.span_eq, Submodule.map_span, Submodule.map_span,
      ← Set.range_comp, ← Set.range_comp, hQdef]
    congr 2
    funext j
    exact hfb j
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := LinearMap.toMatrix_mulVec_repr bP bP f x
    rw [hx, map_zero, LinearMap.toMatrix_toLin] at h1
    have h2 : ⇑(bP.repr x) = 0 := Matrix.eq_zero_of_mulVec_eq_zero hM (by simpa using h1)
    have h3 : bP.repr x = 0 := DFunLike.coe_injective h2
    simpa using h3
  have hR : Q.toAddSubgroup.addSubgroupOf P.toAddSubgroup = (LinearMap.range f).toAddSubgroup := by
    ext x
    rw [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, ← hQ,
      Submodule.mem_toAddSubgroup, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rwa [this] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have : Module.Free (𝓞 K) P := Module.Free.of_basis bP
  have : Module.Finite (𝓞 K) P := Module.Finite.of_basis bP
  have : Module.Free ℤ P := Module.Free.of_basis ((RingOfIntegers.basis K).smulTower bP)
  have : Module.Finite ℤ P := Module.Finite.of_basis ((RingOfIntegers.basis K).smulTower bP)
  set N : Submodule ℤ P := (LinearMap.range f).toAddSubgroup.toIntSubmodule with hN
  let e : P ≃+ N := (LinearEquiv.ofInjective f hf).toAddEquiv
  have hdet : N.subtype ∘ₗ (e : P →+ N).toIntLinearMap = f.restrictScalars ℤ := by
    ext x
    rfl
  have key := Submodule.natAbs_det_equiv N e
  rw [hdet, LinearMap.det_restrictScalars, LinearMap.det_toLin] at key
  rw [AddSubgroup.relIndex, hR]
  change ((Nat.card (P ⧸ N) : ℕ) : ℤ) = _
  rw [← key, Int.natCast_natAbs]

theorem comb_diagonal {K : Type} [Field K] [NumberField K] {r k : ℕ} (v : Fin k → Fin r → K)
    (D : 𝓞 K) : (fun j => ∑ i, Matrix.diagonal (fun _ : Fin k => D) i j • v i) = fun j => D • v j := by
  funext j
  simp [Matrix.diagonal_apply, ite_smul]

theorem exists_smul_mem_span {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (b : Fin k → Fin r → K) (x : Fin r → K) (hx : x ∈ Submodule.span K (Set.range b)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ Submodule.span (𝓞 K) (Set.range b) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
  obtain ⟨⟨d, hd⟩, hdc⟩ :=
    IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K)) Finset.univ c
  refine ⟨d, nonZeroDivisors.ne_zero hd, ?_⟩
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨e, he⟩ := hdc i (Finset.mem_univ i)
  have h1 : d • (c i • b i) = e • b i := by
    rw [← smul_assoc, ← algebraMap_smul K e (b i), he]
  rw [h1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem exists_smul_le_span {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (b : Fin k → Fin r → K) (B : Submodule (𝓞 K) (Fin r → K)) (hB : B.FG)
    (hBb : ∀ x ∈ B, x ∈ Submodule.span K (Set.range b)) :
    ∃ D : 𝓞 K, D ≠ 0 ∧ ∀ x ∈ B, D • x ∈ Submodule.span (𝓞 K) (Set.range b) := by
  obtain ⟨s, hs⟩ := hB
  have hgen : ∀ g ∈ s, ∃ d : 𝓞 K, d ≠ 0 ∧ d • g ∈ Submodule.span (𝓞 K) (Set.range b) :=
    fun g hg => exists_smul_mem_span b g (hBb g (by rw [← hs]; exact Submodule.subset_span hg))
  choose! d hd0 hdm using hgen
  refine ⟨∏ g ∈ s, d g, Finset.prod_ne_zero_iff.2 hd0, ?_⟩
  intro x hx
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem d hg
    rw [ht, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (hdm g hg)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_comm]
    exact Submodule.smul_mem _ _ hx

theorem relIndex_span_ne_zero {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (b : Fin k → Fin r → K) (hb : LinearIndependent K b) (B : Submodule (𝓞 K) (Fin r → K))
    (hbB : ∀ i, b i ∈ B) (D : 𝓞 K) (hD : D ≠ 0)
    (hDB : ∀ x ∈ B, D • x ∈ Submodule.span (𝓞 K) (Set.range b)) :
    (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup ≠ 0 := by
  set P := Submodule.span (𝓞 K) (Set.range b) with hP
  let φ : (Fin r → K) →ₗ[𝓞 K] (Fin r → K) := D • LinearMap.id
  have hD' : algebraMap (𝓞 K) K D ≠ 0 := by
    rw [← map_zero (algebraMap (𝓞 K) K)]
    exact (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hD
  have hφ : Function.Injective φ := by
    intro x y hxy
    funext i
    have := congrFun hxy i
    simp only [φ, Algebra.smul_def] at this
    exact mul_left_cancel₀ hD' this
  have hPB : P ≤ B := Submodule.span_le.mpr (Set.range_subset_iff.mpr hbB)
  have hmapP : Submodule.map φ P = Submodule.span (𝓞 K)
      (Set.range (fun j => ∑ i, Matrix.diagonal (fun _ : Fin k => D) i j • b i)) := by
    rw [comb_diagonal, hP, Submodule.map_span, ← Set.range_comp]
    rfl
  have h1 : (Submodule.map φ P).toAddSubgroup ≤ (Submodule.map φ B).toAddSubgroup :=
    Submodule.map_mono hPB
  have h2 : (Submodule.map φ B).toAddSubgroup ≤ P.toAddSubgroup := by
    rintro _ ⟨x, hx, rfl⟩
    exact hDB x hx
  have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2
  have hdet : (Matrix.diagonal fun _ : Fin k => D).det ≠ 0 := by
    simp [Matrix.det_diagonal, hD]
  have hidx := relIndex_span_comb b hb (Matrix.diagonal fun _ => D) hdet
  rw [← hmapP] at hidx
  have hne : (Submodule.map φ P).toAddSubgroup.relIndex P.toAddSubgroup ≠ 0 := by
    intro h0
    rw [h0] at hidx
    have hn : Algebra.norm ℤ (Matrix.diagonal fun _ : Fin k => D).det ≠ 0 :=
      Algebra.norm_ne_zero_iff.mpr hdet
    simp only [Nat.cast_zero] at hidx
    exact hn (abs_eq_zero.mp hidx.symm)
  have heq : (Submodule.map φ P).toAddSubgroup.relIndex (Submodule.map φ B).toAddSubgroup =
      P.toAddSubgroup.relIndex B.toAddSubgroup := by
    rw [Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hφ
  rw [← heq]
  intro h0
  rw [h0, zero_mul] at hmul
  exact hne hmul.symm

end ReciprocityTheory.MultiplicativeHeights
