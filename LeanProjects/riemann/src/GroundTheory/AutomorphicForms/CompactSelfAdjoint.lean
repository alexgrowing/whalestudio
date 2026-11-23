import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Automorphic.CompactSelfAdjoint

open Module End Submodule Filter Topology
open scoped InnerProductSpace ComplexConjugate

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

theorem finite_setOf_mem_of_orthonormal {ι : Type*} {v : ι → E} (hv : Orthonormal 𝕜 v)
    (W : Submodule 𝕜 E) [FiniteDimensional 𝕜 W] : {i | v i ∈ W}.Finite := by
  let f : {i | v i ∈ W} → W := fun i => ⟨v i, i.2⟩
  have hf : LinearIndependent 𝕜 f := by
    apply LinearIndependent.of_comp W.subtype
    exact hv.linearIndependent.comp _ Subtype.val_injective
  exact Set.finite_coe_iff.1 hf.finite_of_isNoetherian

theorem isClosed_eigenspace (T : E →L[𝕜] E) (μ : 𝕜) :
    IsClosed (eigenspace (T : E →ₗ[𝕜] E) μ : Set E) := by
  have : (eigenspace (T : E →ₗ[𝕜] E) μ : Set E) =
      (T - μ • ContinuousLinearMap.id 𝕜 E) ⁻¹' {0} := by
    ext x
    simp [sub_eq_zero]
  rw [this]
  exact isClosed_singleton.preimage (map_continuous _)

section HilbertBasis

variable [CompleteSpace E]

theorem exists_hilbertBasis_subset_iUnion {α : Type*} (W : α → Submodule 𝕜 E)
    (hW : OrthogonalFamily 𝕜 (fun a => W a) fun a => (W a).subtypeₗᵢ)
    (hc : ∀ a, IsClosed (W a : Set E)) (hbot : (⨆ a, W a)ᗮ = ⊥) :
    ∃ (s : Set E) (b : HilbertBasis s 𝕜 E), ⇑b = ((↑) : s → E) ∧ s ⊆ ⋃ a, (W a : Set E) := by
  classical
  have : ∀ a, CompleteSpace (W a) := fun a =>
    completeSpace_coe_iff_isComplete.2 (hc a).isComplete
  choose w b hb using fun a => exists_hilbertBasis 𝕜 (W a)
  let v : (Σ a, w a) → E := fun p => ((p.2 : W p.1) : E)
  have hv : Orthonormal 𝕜 v :=
    hW.orthonormal_sigma_orthonormal (v_family := fun a => ((↑) : w a → W a))
      (fun a => by rw [← hb a]; exact (b a).orthonormal)
  have hkey : ∀ a, (W a : Set E) ⊆ closure (span 𝕜 (Set.range v) : Set E) := by
    intro a y hy
    let y' : W a := ⟨y, hy⟩
    have h := (W a).subtypeL.hasSum ((b a).hasSum_repr y')
    refine mem_closure_of_tendsto h (Eventually.of_forall fun t => ?_)
    refine Submodule.sum_mem _ fun i _ => ?_
    simp only [map_smul]
    refine Submodule.smul_mem _ _ (subset_span ⟨⟨a, i⟩, ?_⟩)
    simp [v, hb a]
  have hle : (⨆ a, W a) ≤ (span 𝕜 (Set.range v))ᗮᗮ := by
    rw [Submodule.orthogonal_orthogonal_eq_closure, iSup_le_iff]
    intro a y hy
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    exact hkey a hy
  have hspan : (span 𝕜 (Set.range v))ᗮ = ⊥ := by
    rw [eq_bot_iff, ← hbot, ← Submodule.triorthogonal_eq_orthogonal]
    exact Submodule.orthogonal_le hle
  have hinj : Function.Injective v := hv.linearIndependent.injective
  have hv' : Orthonormal 𝕜 ((↑) : Set.range v → E) := (orthonormal_subtype_range hinj).2 hv
  have hspan' : (span 𝕜 (Set.range ((↑) : Set.range v → E)))ᗮ = ⊥ := by
    rwa [Subtype.range_coe]
  refine ⟨Set.range v, HilbertBasis.mkOfOrthogonalEqBot hv' hspan',
    HilbertBasis.coe_mkOfOrthogonalEqBot hv' hspan', ?_⟩
  rintro _ ⟨p, rfl⟩
  exact Set.mem_iUnion.2 ⟨p.1, (p.2 : W p.1).2⟩

end HilbertBasis

section Spectrum

variable {T : E →L[𝕜] E}

theorem zero_mem_spectrum (hT : IsCompactOperator T) (hE : ¬ FiniteDimensional 𝕜 E) :
    (0 : 𝕜) ∈ spectrum 𝕜 T := by
  rw [spectrum.zero_mem_iff]
  rintro ⟨u, hu⟩
  apply hE
  have h : (⇑(↑u⁻¹ : E →L[𝕜] E) ∘ ⇑T) = id := by
    funext x
    have := congrArg (fun g : E →L[𝕜] E => g x) u.inv_mul
    simpa [hu] using this
  have hc := hT.clm_comp (↑u⁻¹ : E →L[𝕜] E)
  rw [h] at hc
  exact isCompactOperator_id_iff_finiteDimensional.1 hc

variable [CompleteSpace E]

theorem exists_real_of_hasEigenvalue (hT' : IsSelfAdjoint T) {μ : 𝕜}
    (hμ : HasEigenvalue (T : E →ₗ[𝕜] E) μ) : ∃ r : ℝ, μ = r :=
  RCLike.conj_eq_iff_real.1
    ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hT').conj_eigenvalue_eq_self hμ)

theorem finite_eigenvalues_norm_ge (hT : IsCompactOperator T) (hT' : IsSelfAdjoint T) {ε : ℝ}
    (hε : 0 < ε) : {μ : 𝕜 | HasEigenvalue (T : E →ₗ[𝕜] E) μ ∧ ε ≤ ‖μ‖}.Finite := by
  have hS := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hT'
  by_contra hinf
  set S := {μ : 𝕜 | HasEigenvalue (T : E →ₗ[𝕜] E) μ ∧ ε ≤ ‖μ‖}
  have : Infinite S := Set.infinite_coe_iff.2 hinf
  let f : ℕ ↪ S := Infinite.natEmbedding S
  have hv : ∀ n, ∃ v : E, T v = ((f n : 𝕜)) • v ∧ ‖v‖ = 1 := by
    intro n
    obtain ⟨v, hv1, hv2⟩ := (f n).2.1.exists_hasEigenvector
    refine ⟨((‖v‖⁻¹ : ℝ) : 𝕜) • v, ?_, ?_⟩
    · rw [map_smul, show T v = (f n : 𝕜) • v from mem_eigenspace_iff.1 hv1, smul_comm]
    · rw [norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hv2)]
  choose v hvT hvn using hv
  obtain ⟨K, hK, hK'⟩ := hT.image_closedBall_subset_compact 1
  obtain ⟨y, -, ψ, hψ, hψy⟩ :=
    hK.tendsto_subseq (fun n => hK' ⟨v n, by simp [hvn], rfl⟩)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hψy.cauchySeq ε hε
  have h1 : dist (T (v (ψ (N + 1)))) (T (v (ψ N))) < ε := hN (N + 1) (Nat.le_succ N)
  set a := ψ (N + 1)
  set b := ψ N
  have hne : (f a : 𝕜) ≠ f b := by
    intro h
    have := f.injective (Subtype.ext h)
    exact (hψ (Nat.lt_succ_self N)).ne this.symm
  have horth : ⟪v a, v b⟫ = 0 := by
    have := hS.orthogonalFamily_eigenspaces hne ⟨v a, mem_eigenspace_iff.2 (hvT a)⟩
      ⟨v b, mem_eigenspace_iff.2 (hvT b)⟩
    simpa using this
  have hx : ⟪T (v a), T (v b)⟫ = 0 := by
    rw [hvT, hvT, inner_smul_left, inner_smul_right, horth, mul_zero, mul_zero]
  have hnx : ε ≤ ‖T (v a)‖ := by
    rw [hvT, norm_smul, hvn, mul_one]
    exact (f a).2.2
  have hsq := norm_sub_sq (𝕜 := 𝕜) (T (v a)) (T (v b))
  rw [hx, map_zero, mul_zero, sub_zero] at hsq
  rw [dist_eq_norm] at h1
  have h2 : 0 ≤ ‖T (v a) - T (v b)‖ := norm_nonneg _
  nlinarith [sq_nonneg ‖T (v b)‖]

theorem countable_eigenvalues (hT : IsCompactOperator T) (hT' : IsSelfAdjoint T) :
    {μ : 𝕜 | HasEigenvalue (T : E →ₗ[𝕜] E) μ}.Countable := by
  have : {μ : 𝕜 | HasEigenvalue (T : E →ₗ[𝕜] E) μ} ⊆ {0} ∪
      ⋃ n : ℕ, {μ : 𝕜 | HasEigenvalue (T : E →ₗ[𝕜] E) μ ∧ 1 / ((n : ℝ) + 1) ≤ ‖μ‖} := by
    intro μ hμ
    by_cases h0 : μ = 0
    · exact Or.inl h0
    · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.2 h0)
      exact Or.inr (Set.mem_iUnion.2 ⟨n, hμ, hn.le⟩)
  exact ((Set.countable_singleton 0).union (Set.countable_iUnion fun n =>
    (finite_eigenvalues_norm_ge hT hT' (by positivity)).countable)).mono this

theorem hasEigenvalue_of_mem_spectrum (hT : IsCompactOperator T) {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 T) (h0 : μ ≠ 0) : HasEigenvalue (T : E →ₗ[𝕜] E) μ :=
  (hT.hasEigenvalue_iff_mem_spectrum h0).2 hμ

theorem finite_spectrum_norm_ge (hT : IsCompactOperator T) (hT' : IsSelfAdjoint T) {ε : ℝ}
    (hε : 0 < ε) : {μ ∈ spectrum 𝕜 T | ε ≤ ‖μ‖}.Finite :=
  (finite_eigenvalues_norm_ge hT hT' hε).subset fun _ hμ =>
    ⟨hasEigenvalue_of_mem_spectrum hT hμ.1 (norm_pos_iff.1 (hε.trans_le hμ.2)), hμ.2⟩

theorem countable_spectrum (hT : IsCompactOperator T) (hT' : IsSelfAdjoint T) :
    (spectrum 𝕜 T).Countable :=
  ((Set.countable_singleton 0).union (countable_eigenvalues hT hT')).mono fun μ hμ => by
    by_cases h0 : μ = 0
    · exact Or.inl h0
    · exact Or.inr (hasEigenvalue_of_mem_spectrum hT hμ h0)

theorem spectrum_subset_range_ofReal (hT : IsCompactOperator T) (hT' : IsSelfAdjoint T) :
    spectrum 𝕜 T ⊆ Set.range ((↑) : ℝ → 𝕜) := by
  intro μ hμ
  by_cases h0 : μ = 0
  · exact ⟨0, by simp [h0]⟩
  · obtain ⟨r, hr⟩ := exists_real_of_hasEigenvalue hT' (hasEigenvalue_of_mem_spectrum hT hμ h0)
    exact ⟨r, hr.symm⟩

theorem eventually_notMem_spectrum (hT : IsCompactOperator T) (hT' : IsSelfAdjoint T) {μ : 𝕜}
    (hμ : μ ≠ 0) : ∀ᶠ ν in 𝓝[≠] μ, ν ∉ spectrum 𝕜 T := by
  have hμ' : 0 < ‖μ‖ / 2 := by have := norm_pos_iff.2 hμ; positivity
  set F := {ν ∈ spectrum 𝕜 T | ‖μ‖ / 2 ≤ ‖ν‖}
  have hF : (F \ {μ}).Finite := (finite_spectrum_norm_ge hT hT' hμ').sdiff
  have hopen : IsOpen ((F \ {μ})ᶜ ∩ Metric.ball μ (‖μ‖ / 2)) :=
    hF.isClosed.isOpen_compl.inter Metric.isOpen_ball
  have hmem : μ ∈ (F \ {μ})ᶜ ∩ Metric.ball μ (‖μ‖ / 2) :=
    ⟨fun h => h.2 rfl, Metric.mem_ball_self hμ'⟩
  filter_upwards [inter_mem_nhdsWithin {μ}ᶜ (hopen.mem_nhds hmem)] with ν hν hνs
  obtain ⟨hne, hF', hball⟩ := hν
  apply hF'
  refine ⟨⟨hνs, ?_⟩, hne⟩
  rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hball
  have := norm_sub_norm_le μ ν
  linarith

end Spectrum

section Eigenbasis

variable [CompleteSpace E]

theorem exists_hilbertBasis_eigenvectors {T : E →L[𝕜] E} (hT : IsCompactOperator T)
    (hT' : IsSelfAdjoint T) :
    ∃ (s : Set E) (b : HilbertBasis s 𝕜 E), ⇑b = ((↑) : s → E) ∧
      ∀ v ∈ s, ∃ μ : ℝ, T v = (μ : 𝕜) • v := by
  have hS := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hT'
  obtain ⟨s, b, hb, hs⟩ := exists_hilbertBasis_subset_iUnion
    (fun μ => eigenspace (T : E →ₗ[𝕜] E) μ) hS.orthogonalFamily_eigenspaces
    (isClosed_eigenspace T) (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hT hS)
  refine ⟨s, b, hb, fun v hv => ?_⟩
  obtain ⟨μ, hμ⟩ := Set.mem_iUnion.1 (hs hv)
  have hv0 : v ≠ 0 := by
    have h := b.orthonormal.1 ⟨v, hv⟩
    rw [hb] at h
    intro h0
    simp [h0] at h
  have hE : HasEigenvalue (T : E →ₗ[𝕜] E) μ := hasEigenvalue_of_hasEigenvector ⟨hμ, hv0⟩
  obtain ⟨r, hr⟩ := exists_real_of_hasEigenvalue hT' hE
  exact ⟨r, by rw [← hr]; exact mem_eigenspace_iff.1 hμ⟩

theorem exists_hilbertBasis_eigenvectors_hasSum {T : E →L[𝕜] E} (hT : IsCompactOperator T)
    (hT' : IsSelfAdjoint T) :
    ∃ (s : Set E) (b : HilbertBasis s 𝕜 E) (l : s → ℝ), ⇑b = ((↑) : s → E) ∧
      (∀ i, T (b i) = (l i : 𝕜) • b i) ∧
      (∀ x, HasSum (fun i => ((l i : 𝕜) * ⟪b i, x⟫) • b i) (T x)) ∧
      ∀ ε > 0, {i | ε ≤ |l i|}.Finite := by
  obtain ⟨s, b, hb, hs⟩ := exists_hilbertBasis_eigenvectors hT hT'
  choose l hl using fun i : s => hs i i.2
  have hTb : ∀ i, T (b i) = (l i : 𝕜) • b i := fun i => by rw [hb]; exact hl i
  refine ⟨s, b, l, hb, hTb, fun x => ?_, fun ε hε => ?_⟩
  · have h := T.hasSum (b.hasSum_repr x)
    convert h using 1
    funext i
    simp only [map_smul, hTb, smul_smul, b.repr_apply_apply, mul_comm]
  · have hF := finite_eigenvalues_norm_ge hT hT' hε
    have hsub : {i | ε ≤ |l i|} ⊆ ⋃ μ ∈ {μ : 𝕜 | HasEigenvalue (T : E →ₗ[𝕜] E) μ ∧ ε ≤ ‖μ‖},
        {i | b i ∈ eigenspace (T : E →ₗ[𝕜] E) μ} := by
      intro i hi
      have hmem : b i ∈ eigenspace (T : E →ₗ[𝕜] E) (l i : 𝕜) := mem_eigenspace_iff.2 (hTb i)
      have hne : b i ≠ 0 := fun h => by simpa [h] using b.orthonormal.1 i
      refine Set.mem_biUnion (x := (l i : 𝕜))
        ⟨hasEigenvalue_of_hasEigenvector ⟨hmem, hne⟩, ?_⟩ hmem
      simpa [RCLike.norm_ofReal] using hi
    refine (hF.biUnion fun μ hμ => ?_).subset hsub
    have hμ0 : μ ≠ 0 := norm_pos_iff.1 (hε.trans_le hμ.2)
    have := ContinuousLinearMap.finite_dimensional_eigenspace hT μ hμ0
    exact finite_setOf_mem_of_orthonormal b.orthonormal _

theorem orthogonal_iSup_iInf_eigenspaces_eq_bot {ι : Type*} (T : ι → E →L[𝕜] E)
    (hT : ∀ i, IsCompactOperator (T i)) (hS : ∀ i, (T i : E →ₗ[𝕜] E).IsSymmetric)
    (hC : ∀ i j, Commute (T i) (T j)) :
    (⨆ χ : ι → 𝕜, ⨅ i, eigenspace (T i : E →ₗ[𝕜] E) (χ i))ᗮ = ⊥ := by
  set M := ⨆ χ : ι → 𝕜, ⨅ i, eigenspace (T i : E →ₗ[𝕜] E) (χ i) with hMdef
  have hcomm : ∀ i j v, T j (T i v) = T i (T j v) := fun i j v => by
    simpa using congrArg (fun g : E →L[𝕜] E => g v) (hC j i)
  have hJinv : ∀ (χ : ι → 𝕜) i, ∀ v ∈ ⨅ j, eigenspace (T j : E →ₗ[𝕜] E) (χ j),
      T i v ∈ ⨅ j, eigenspace (T j : E →ₗ[𝕜] E) (χ j) := by
    intro χ i v hv
    rw [Submodule.mem_iInf] at hv ⊢
    intro j
    have h := mem_eigenspace_iff.1 (hv j)
    simp only [ContinuousLinearMap.coe_coe] at h
    rw [mem_eigenspace_iff, ContinuousLinearMap.coe_coe, hcomm, h, map_smul]
  have hMinv : ∀ i, ∀ v ∈ M, T i v ∈ M := by
    intro i v hv
    refine Submodule.iSup_induction _ (motive := fun v => T i v ∈ M) hv
      (fun χ x hx => Submodule.mem_iSup_of_mem χ (hJinv χ i x hx)) (by simp) ?_
    intro x y hx hy
    simpa only [map_add] using add_mem hx hy
  have hNinv : ∀ i, ∀ v ∈ Mᗮ, T i v ∈ Mᗮ := by
    intro i v hv
    rw [Submodule.mem_orthogonal] at hv ⊢
    intro u hu
    have h := hS i u v
    simp only [ContinuousLinearMap.coe_coe] at h
    rw [← h]
    exact hv _ (hMinv i u hu)
  by_contra hne
  suffices h : ∃ w ∈ Mᗮ, w ≠ 0 ∧ w ∈ M by
    obtain ⟨w, hwN, hw0, hwM⟩ := h
    have hw : w ∈ M ⊓ Mᗮ := ⟨hwM, hwN⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hw
    exact hw0 hw
  by_cases hz : ∀ i, ∀ v ∈ Mᗮ, T i v = 0
  · obtain ⟨w, hwN, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨w, hwN, hw0, Submodule.mem_iSup_of_mem (fun _ => 0) ?_⟩
    rw [Submodule.mem_iInf]
    intro i
    rw [mem_eigenspace_iff, ContinuousLinearMap.coe_coe, hz i w hwN, zero_smul]
  push Not at hz
  obtain ⟨k, v, hvN, hvk⟩ := hz
  let S : Mᗮ →L[𝕜] Mᗮ := (T k).restrict (hNinv k)
  have hS_compact : IsCompactOperator S := (hT k).restrict' (hNinv k)
  have hS_symm : (S : Mᗮ →ₗ[𝕜] Mᗮ).IsSymmetric := (hS k).restrict_invariant (hNinv k)
  have hS0 : S ≠ 0 := by
    intro h
    apply hvk
    have := congrArg (fun g : Mᗮ →L[𝕜] Mᗮ => ((g ⟨v, hvN⟩ : Mᗮ) : E)) h
    simpa [S] using this
  obtain ⟨μ, hμ, hμ0⟩ : ∃ μ, HasEigenvalue (S : Mᗮ →ₗ[𝕜] Mᗮ) μ ∧ μ ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hS0 ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hS_compact
      hS_symm).1 h')
  obtain ⟨u, hu1, hu2⟩ := hμ.exists_hasEigenvector
  have huk : T k u = μ • (u : E) := by
    have := congrArg Subtype.val (mem_eigenspace_iff.1 hu1)
    simpa [S] using this
  set U : Submodule 𝕜 E := eigenspace (T k : E →ₗ[𝕜] E) μ ⊓ Mᗮ with hUdef
  have : FiniteDimensional 𝕜 (eigenspace (T k : E →ₗ[𝕜] E) μ) :=
    ContinuousLinearMap.finite_dimensional_eigenspace (hT k) μ hμ0
  have : FiniteDimensional 𝕜 U := Submodule.finiteDimensional_of_le inf_le_left
  have hUinv : ∀ i, ∀ x ∈ U, (T i : E →ₗ[𝕜] E) x ∈ U := by
    intro i x hx
    refine ⟨?_, hNinv i x hx.2⟩
    have h := mem_eigenspace_iff.1 hx.1
    simp only [ContinuousLinearMap.coe_coe] at h
    rw [SetLike.mem_coe, mem_eigenspace_iff, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.coe_coe, hcomm, h, map_smul]
  let R : ι → Module.End 𝕜 U := fun i => (T i : E →ₗ[𝕜] E).restrict (hUinv i)
  have hRs : ∀ i, (R i).IsSymmetric := fun i => (hS i).restrict_invariant (hUinv i)
  have hRc : Pairwise (Function.onFun Commute R) := by
    intro i j _
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp [R, LinearMap.restrict_apply, hcomm]
  have huU : (u : E) ∈ U := ⟨mem_eigenspace_iff.2 (by simpa using huk), u.2⟩
  have hUne : (⊤ : Submodule 𝕜 U) ≠ ⊥ := by
    intro h
    have : (⟨u, huU⟩ : U) ∈ (⊥ : Submodule 𝕜 U) := h ▸ Submodule.mem_top
    rw [Submodule.mem_bot] at this
    exact hu2 (Subtype.ext (by simpa using congrArg Subtype.val this))
  rw [← LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hRs hRc, ne_eq, iSup_eq_bot] at hUne
  push Not at hUne
  obtain ⟨χ, hχ⟩ := hUne
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  refine ⟨w, w.2.2, fun h => hw0 (Subtype.ext h), Submodule.mem_iSup_of_mem χ ?_⟩
  rw [Submodule.mem_iInf] at hw ⊢
  intro i
  have := congrArg Subtype.val (mem_eigenspace_iff.1 (hw i))
  rw [mem_eigenspace_iff]
  simpa [R, LinearMap.restrict_apply] using this

theorem exists_hilbertBasis_common_eigenvectors {ι : Type*} (T : ι → E →L[𝕜] E)
    (hT : ∀ i, IsCompactOperator (T i)) (hT' : ∀ i, IsSelfAdjoint (T i))
    (hC : ∀ i j, Commute (T i) (T j)) :
    ∃ (s : Set E) (b : HilbertBasis s 𝕜 E), ⇑b = ((↑) : s → E) ∧
      ∀ v ∈ s, ∀ i, ∃ μ : ℝ, T i v = (μ : 𝕜) • v := by
  have hS : ∀ i, (T i : E →ₗ[𝕜] E).IsSymmetric := fun i =>
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 (hT' i)
  let J : (ι → 𝕜) → Submodule 𝕜 E := fun χ => ⨅ i, eigenspace (T i : E →ₗ[𝕜] E) (χ i)
  have hJo : OrthogonalFamily 𝕜 (fun χ => J χ) fun χ => (J χ).subtypeₗᵢ :=
    LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces (T := fun i => (T i : E →ₗ[𝕜] E)) hS
  have hJc : ∀ χ, IsClosed (J χ : Set E) := fun χ => by
    simp only [J, Submodule.coe_iInf]
    exact isClosed_iInter fun i => isClosed_eigenspace (T i) (χ i)
  obtain ⟨s, b, hb, hs⟩ := exists_hilbertBasis_subset_iUnion J hJo hJc
    (orthogonal_iSup_iInf_eigenspaces_eq_bot T hT hS hC)
  refine ⟨s, b, hb, fun v hv i => ?_⟩
  obtain ⟨χ, hχ⟩ := Set.mem_iUnion.1 (hs hv)
  have hmem : v ∈ eigenspace (T i : E →ₗ[𝕜] E) (χ i) := (Submodule.mem_iInf _).1 hχ i
  have hv0 : v ≠ 0 := by
    have h := b.orthonormal.1 ⟨v, hv⟩
    rw [hb] at h
    intro h0
    simp [h0] at h
  obtain ⟨r, hr⟩ := exists_real_of_hasEigenvalue (hT' i)
    (hasEigenvalue_of_hasEigenvector ⟨hmem, hv0⟩)
  exact ⟨r, by rw [← hr]; exact mem_eigenspace_iff.1 hmem⟩

end Eigenbasis

end GroundTheory.Automorphic.CompactSelfAdjoint
