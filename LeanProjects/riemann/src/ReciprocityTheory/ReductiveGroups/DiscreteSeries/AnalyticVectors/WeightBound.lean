import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.LayerSpan
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Numerics
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.KUnitB

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem sqrt_nsq_eq_norm' (x : Fin n → ℝ) :
    √(nsq x) = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ := by
  first
    | (rw [EuclideanSpace.norm_eq]
       congr 1
       simp [nsq, dot, Real.norm_eq_abs, sq])
    | (rw [EuclideanSpace.norm_eq]
       congr 1
       simp only [nsq, dot, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs, sq])

theorem nsq_nonneg' (x : Fin n → ℝ) : 0 ≤ nsq x := by
  unfold nsq dot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

section Unitary

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem exists_weight_bound (hU : IsInfUnitary ε E) (hVf : FiniteDimensional ℂ V)
    (hVK : IsKStableSub ε E V) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ v ∈ V, v ≠ 0 → ∀ ν : Fin n → ℝ, (∀ a, E a a v = (ν a : ℂ) • v) →
      √(nsq (ν + rhoC ε)) ≤ R := by
  classical
  haveI := hVf
  have hT : ∀ a, {r : ℝ | Module.End.HasEigenvalue ((E a a).restrict (hVK a a rfl)) (r : ℂ)}.Finite := by
    intro a
    have hf : Set.Finite (Module.End.HasEigenvalue ((E a a).restrict (hVK a a rfl))) := by
      first
        | exact Module.End.finite_hasEigenvalue _
        | exact (Module.End.finite_spectrum _).subset fun μ h => h.mem_spectrum
    exact hf.preimage Complex.ofReal_injective.injOn
  have hW := Set.Finite.pi hT
  obtain ⟨B, hB⟩ := (hW.image fun ν => √(nsq (ν + rhoC ε))).bddAbove
  refine ⟨max B 0, le_max_right _ _, fun v hv hv0 ν hν => ?_⟩
  have hmem : ν ∈ Set.pi Set.univ fun a =>
      {r : ℝ | Module.End.HasEigenvalue ((E a a).restrict (hVK a a rfl)) (r : ℂ)} := by
    intro a _
    have hx : ((E a a).restrict (hVK a a rfl)) ⟨v, hv⟩ = (ν a : ℂ) • (⟨v, hv⟩ : V) := by
      apply Subtype.ext
      simp [hν a]
    have hx0 : (⟨v, hv⟩ : V) ≠ 0 := by simpa using hv0
    first
      | exact Module.End.hasEigenvalue_of_hasEigenvector
          (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 hx, hx0⟩)
      | exact Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hx, hx0⟩
  exact (hB ⟨ν, hmem, rfl⟩).trans (le_max_left _ _)

theorem sqrt_nsq_add_le (x y : Fin n → ℝ) : √(nsq (x + y)) ≤ √(nsq x) + √(nsq y) := by
  rw [sqrt_nsq_eq_norm', sqrt_nsq_eq_norm', sqrt_nsq_eq_norm']
  first
    | (rw [WithLp.toLp_add]; exact norm_add_le _ _)
    | (have h := norm_add_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 y)
       rwa [← WithLp.toLp_add] at h)

theorem sqrt_nsq_sum_le {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℝ) :
    √(nsq (∑ i ∈ s, f i)) ≤ ∑ i ∈ s, √(nsq (f i)) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [nsq, dot]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (sqrt_nsq_add_le _ _).trans (add_le_add le_rfl ih)

theorem sqrt_nsq_add_ncSum_le {j : ℕ} {ω : Fin n → ℝ} (hω : IsNCSum ε j ω)
    (x : Fin n → ℝ) :
    √(nsq (x + ω)) ≤ √(nsq x) + √2 * j := by
  obtain ⟨γ, hγ, rfl⟩ := hω
  have hroot : ∀ a b : Fin n, a ≠ b → nsq (root a b) = 2 := by
    intro a b hne
    unfold nsq dot
    rw [Fintype.sum_eq_add a b hne]
    · norm_num [root, Pi.single_apply, hne, hne.symm]
    · intro c hc
      simp [root, Pi.single_apply, hc.1, hc.2]
  have hr : ∀ i, √(nsq (root (γ i).1 (γ i).2)) ≤ √2 := fun i => by
    have hne : (γ i).1 ≠ (γ i).2 := fun h => hγ i (congrArg ε h)
    exact le_of_eq (by rw [hroot _ _ hne])
  calc √(nsq (x + ∑ i, root (γ i).1 (γ i).2))
      ≤ √(nsq x) + √(nsq (∑ i, root (γ i).1 (γ i).2)) := sqrt_nsq_add_le _ _
    _ ≤ √(nsq x) + ∑ i, √(nsq (root (γ i).1 (γ i).2)) :=
        add_le_add le_rfl (sqrt_nsq_sum_le _ _)
    _ ≤ √(nsq x) + ∑ _i : Fin j, √2 := add_le_add le_rfl (Finset.sum_le_sum fun i _ => hr i)
    _ = √(nsq x) + √2 * j := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]

theorem weight_layer_le (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hVf : FiniteDimensional ℂ V)
    (hVK : IsKStableSub ε E V) {R : ℝ}
    (hR : ∀ v ∈ V, v ≠ 0 → ∀ ν : Fin n → ℝ, (∀ a, E a a v = (ν a : ℂ) • v) →
      √(nsq (ν + rhoC ε)) ≤ R)
    (k : ℕ) {w : M} (hw : w ∈ layer ε E V k) (hw0 : w ≠ 0) {μ : Fin n → ℝ}
    (hμ : ∀ a, E a a w = (μ a : ℂ) • w) :
    √(nsq (μ + rhoC ε)) ≤ R + √2 * k := by
  classical
  have hspan := layer_le_span hE hU hVf hVK k hw
  by_contra hcon
  have hP : ∀ s ∈ layerWtVecs ε E V k, (∀ a, ∃ l : ℂ, E a a s = l • s) ∧
      (s = 0 ∨ ∃ a, ∃ l : ℝ, l ≠ μ a ∧ E a a s = (l : ℂ) • s) := by
    intro s hs
    obtain ⟨ν, ω, j, hj, hω, ⟨v, hv, hv0, hνv⟩, hs'⟩ := hs
    refine ⟨fun a => ⟨_, hs' a⟩, ?_⟩
    by_cases hl : ν + ω = μ
    · exfalso
      subst hl
      apply hcon
      rw [add_right_comm]
      calc √(nsq (ν + rhoC ε + ω)) ≤ √(nsq (ν + rhoC ε)) + √2 * j := sqrt_nsq_add_ncSum_le hω _
        _ ≤ R + √2 * k := add_le_add (hR v hv hv0 ν hνv)
            (mul_le_mul_of_nonneg_left (Nat.cast_le.2 hj) (Real.sqrt_nonneg 2))
    · right
      obtain ⟨a, ha⟩ := Function.ne_iff.1 hl
      exact ⟨a, (ν + ω) a, ha, hs' a⟩
  have key : ∀ G : Finset M, (∀ s ∈ G, (∀ a, ∃ l : ℂ, E a a s = l • s) ∧
      (s = 0 ∨ ∃ a, ∃ l : ℝ, l ≠ μ a ∧ E a a s = (l : ℂ) • s)) →
      ∃ T : Module.End ℂ M, ∃ c : ℂ, c ≠ 0 ∧ T w = c • w ∧ ∀ s ∈ G, T s = 0 := by
    intro G
    refine Finset.induction_on G ?_ ?_
    · intro _
      exact ⟨1, 1, one_ne_zero, by simp, by simp⟩
    · intro s G hsG ih hG
      obtain ⟨T, c, hc, hTw, hTG⟩ := ih fun x hx => hG x (Finset.mem_insert_of_mem hx)
      rcases (hG s (Finset.mem_insert_self s G)).2 with h0 | ⟨a, l, hl, hs⟩
      · refine ⟨T, c, hc, hTw, fun x hx => ?_⟩
        rcases Finset.mem_insert.1 hx with rfl | hx
        · rw [h0, map_zero]
        · exact hTG x hx
      · refine ⟨T * (E a a - (l : ℂ) • 1), c * ((μ a : ℂ) - l),
          mul_ne_zero hc (sub_ne_zero.2 (by exact_mod_cast hl.symm)), ?_, ?_⟩
        · have h1 : (T * (E a a - (l : ℂ) • 1)) w = T (((μ a : ℂ) - l) • w) := by
            simp [hμ a, sub_smul]
          rw [h1, map_smul, hTw, smul_smul, mul_comm]
        · intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · simp [hs]
          · obtain ⟨l', hx'⟩ := (hG x (Finset.mem_insert_of_mem hx)).1 a
            have h2 : (T * (E a a - (l : ℂ) • 1)) x = T ((l' - l) • x) := by
              simp [hx', sub_smul]
            rw [h2, map_smul, hTG x hx, smul_zero]
  obtain ⟨F, hFS, hwF⟩ := Submodule.mem_span_finite_of_mem_span hspan
  obtain ⟨T, c, hc, hTw, hTF⟩ := key F fun s hs => hP s (hFS hs)
  have hle : Submodule.span ℂ (F : Set M) ≤ LinearMap.ker T :=
    Submodule.span_le.2 fun s hs => LinearMap.mem_ker.2 (hTF s hs)
  have h0 : T w = 0 := LinearMap.mem_ker.1 (hle hwF)
  rw [hTw] at h0
  exact hw0 ((smul_eq_zero.1 h0).resolve_left hc)

theorem exists_re_inner_casimirK_layer_le (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ k : ℕ, ∀ x ∈ layer ε E V k,
      RCLike.re (inner ℂ (casimirK ε E x) x) ≤ ((R + √2 * k) ^ 2 - nsq (rhoC ε)) * ‖x‖ ^ 2 := by
  obtain ⟨R, hR0, hR⟩ := exists_weight_bound hU hVf hVK
  refine ⟨R, hR0, fun k x hx => ?_⟩
  refine re_inner_casimirK_le hE (isKUnitary_of_isInfUnitary hU) (finiteDimensional_layer hVf k)
    (layer_kStable hE hVK k) _ (fun w hw hw0 μ hμ => ?_) x hx
  unfold casValK
  have h := weight_layer_le hE hU hVf hVK hR k hw hw0 hμ.1
  have h0 : 0 ≤ nsq (μ + rhoC ε) := nsq_nonneg' _
  have h1 : nsq (μ + rhoC ε) ≤ (R + √2 * k) ^ 2 := by
    rw [← Real.sq_sqrt h0]
    first
      | exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
      | exact pow_le_pow_left (Real.sqrt_nonneg _) h 2
      | gcongr
  linarith

end Unitary

end ReciprocityTheory.ChartRestriction.DS
