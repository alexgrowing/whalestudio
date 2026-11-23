import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPermOfOfFnPerm
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)

namespace GlobalTheory.ConvexCutOff

theorem exists_support {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {K : Set V} (hK : Convex ℝ K) (hne : K.Nonempty) {x : V} (hx : x ∉ interior K) :
    ∃ f : V →L[ℝ] ℝ, f ≠ 0 ∧ ∀ y ∈ K, f y ≤ f x := by
  by_cases hi : (interior K).Nonempty
  · obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hK.interior isOpen_interior hx
    refine ⟨f, ?_, ?_⟩
    · rintro rfl
      obtain ⟨a, ha⟩ := hi
      simpa using hf a ha
    · intro y hy
      have h1 : y ∈ closure (interior K) := by
        rw [hK.closure_interior_eq_closure_of_nonempty_interior hi]
        exact subset_closure hy
      have h2 : IsClosed {z | f z ≤ f x} := isClosed_le f.continuous continuous_const
      exact closure_minimal (fun a ha => (hf a ha).le) h2 h1
  · rw [hK.interior_nonempty_iff_affineSpan_eq_top] at hi
    obtain ⟨k, hk⟩ := hne
    have hd : (affineSpan ℝ K).direction < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro h
      exact hi ((AffineSubspace.direction_eq_top_iff_of_nonempty
        ⟨k, subset_affineSpan ℝ K hk⟩).1 h)
    obtain ⟨g, hg0, hg⟩ := Submodule.exists_le_ker_of_lt_top _ hd
    have hc : ∀ y ∈ K, g y = g k := by
      intro y hy
      have := hg (AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ K hy)
        (subset_affineSpan ℝ K hk))
      simpa [sub_eq_zero] using this
    have hg1 : LinearMap.toContinuousLinearMap g ≠ 0 := by
      intro h
      apply hg0
      ext z
      simpa using congrArg (fun φ : V →L[ℝ] ℝ => φ z) h
    rcases le_total (g k) (g x) with h | h
    · exact ⟨LinearMap.toContinuousLinearMap g, hg1, fun y hy => by simpa [hc y hy] using h⟩
    · exact ⟨-LinearMap.toContinuousLinearMap g, neg_ne_zero.2 hg1,
        fun y hy => by simpa [hc y hy] using h⟩

theorem uniqueDiffWithinAt_compl {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {K : Set V} (hK : Convex ℝ K) {x : V} (hx : x ∉ interior K) :
    UniqueDiffWithinAt ℝ Kᶜ x := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simpa using uniqueDiffWithinAt_univ
  obtain ⟨f, hf0, hf⟩ := exists_support hK hne hx
  obtain ⟨v, hv⟩ : ∃ v, 0 < f v := by
    obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
      by_contra h
      push_neg at h
      exact hf0 (ContinuousLinearMap.ext h)
    rcases lt_or_gt_of_ne hw with h | h
    · exact ⟨-w, by simpa using h⟩
    · exact ⟨w, h⟩
  have hH : Convex ℝ {y | f x < f y} := convex_halfSpace_gt f.toLinearMap.isLinear (f x)
  have hO : IsOpen {y | f x < f y} := isOpen_lt continuous_const f.continuous
  have hcl : x ∈ closure {y | f x < f y} := by
    have ht : Filter.Tendsto (fun t : ℝ => x + t • v) (nhdsWithin 0 (Set.Ioi 0)) (nhds x) := by
      have : Continuous (fun t : ℝ => x + t • v) := by fun_prop
      have h2 := this.tendsto 0
      simp only [zero_smul, add_zero] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := ht
    simp only [Set.mem_setOf_eq, map_add, map_smul, smul_eq_mul]
    nlinarith [mul_pos ht' hv]
  have hU := uniqueDiffWithinAt_convex hH (by
    rw [hO.interior_eq]
    exact ⟨x + v, by simpa using hv⟩) hcl
  exact hU.mono fun y hy hyK => absurd (hf y hyK) (not_le.2 hy)

theorem fderiv_eq_zero {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] {K : Set V} (hK : Convex ℝ K) {G : V → W}
    (hG : ∀ z, z ∉ K → G z = 0) {x : V} (hx : x ∉ interior K) : fderiv ℂ G x = 0 := by
  by_cases hd : DifferentiableAt ℂ G x
  swap
  · exact fderiv_zero_of_not_differentiableAt hd
  have hU := uniqueDiffWithinAt_compl hK hx
  have hx0 : G x = 0 := by
    have := hd.continuousAt.continuousWithinAt.mem_closure_image hU.mem_closure
    have hs : G '' Kᶜ ⊆ {0} := by
      rintro _ ⟨z, hz, rfl⟩
      exact hG z hz
    exact closure_minimal hs isClosed_singleton this
  have h1 : HasFDerivWithinAt G ((fderiv ℂ G x).restrictScalars ℝ) Kᶜ x :=
    (hd.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have h2 : HasFDerivWithinAt G (0 : V →L[ℝ] W) Kᶜ x :=
    (hasFDerivWithinAt_const (0 : W) x Kᶜ).congr (fun z hz => hG z hz) hx0
  have h3 := hU.eq h1 h2
  ext z
  simpa using congrArg (fun φ : V →L[ℝ] W => φ z) h3

theorem iteratedFDeriv_eq_zero_off {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {K : Set V} (hK : Convex ℝ K) {F : V → ℂ}
    (hF : ∀ z, z ∉ K → F z = 0) (n : ℕ) : ∀ z, z ∉ K → iteratedFDeriv ℂ n F z = 0 := by
  induction n with
  | zero =>
    intro z hz
    ext m
    simp [hF z hz]
  | succ n ih =>
    intro z hz
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,
      fderiv_eq_zero hK ih (fun h => hz (interior_subset h))]
    exact map_zero _

theorem iteratedFDeriv_symm {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {K : Set V} (hK : Convex ℝ K) {F : V → ℂ}
    (hF : ∀ z, z ∉ K → F z = 0) (hd : DifferentiableOn ℂ F (interior K)) (x : V) (n : ℕ)
    (v : Fin n → V) (σ : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℂ n F x (v ∘ σ) = iteratedFDeriv ℂ n F x v := by
  by_cases hx : x ∈ interior K
  · exact (GlobalTheory.SCV.analyticOnNhd_of_differentiableOn isOpen_interior hd x
      hx).contDiffAt.iteratedFDeriv_comp_perm v σ
  · cases n with
    | zero => simp
    | succ n =>
      have : iteratedFDeriv ℂ (n + 1) F x = 0 := by
        rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,
          fderiv_eq_zero hK (iteratedFDeriv_eq_zero_off hK hF n) hx]
        exact map_zero _
      simp [this]

theorem exists_perm_of_ofFn_perm {α : Type} {n : ℕ} (v w : Fin n → α)
    (h : (List.ofFn v).Perm (List.ofFn w)) : ∃ σ : Equiv.Perm (Fin n), v = w ∘ σ := by
  first
  | exact @_root_.GlobalTheory.FiberCardPermutation.exists_perm_of_ofFn_perm
  | exact _root_.GlobalTheory.FiberCardPermutation.exists_perm_of_ofFn_perm
  | (apply _root_.GlobalTheory.FiberCardPermutation.exists_perm_of_ofFn_perm <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiberCardPermutation.exists_perm_of_ofFn_perm <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiberCardPermutation.exists_perm_of_ofFn_perm <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiberCardPermutation.exists_perm_of_ofFn_perm ..)

theorem term_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {F : V → ℂ} {x : V}
    (hs : ∀ (n : ℕ) (v : Fin n → V) (σ : Equiv.Perm (Fin n)),
      iteratedFDeriv ℂ n F x (v ∘ σ) = iteratedFDeriv ℂ n F x v)
    {n m : ℕ} (v : Fin n → V) (w : Fin m → V) (h : (List.ofFn v).Perm (List.ofFn w)) :
    iteratedFDeriv ℂ n F x v = iteratedFDeriv ℂ m F x w := by
  have hnm : n = m := by simpa using h.length_eq
  subst hnm
  obtain ⟨σ, rfl⟩ := exists_perm_of_ofFn_perm v w h
  exact hs n w σ

theorem ofFn_get_cast {α β : Type} (l : List α) {n : ℕ} (u : α → β) (h : n = l.length) :
    List.ofFn (fun k : Fin n => u (l.get (Fin.cast h k))) = l.map u := by
  subst h
  apply List.ext_getElem <;> simp

theorem polyDeriv_rename_of_convex : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (K : Set V) (F : V → ℂ), Convex ℝ K → (∀ z, z ∉ K → F z = 0) → DifferentiableOn ℂ F (interior K) → ∀ (x : V) (ι κ : Type) (ρ : ι → κ), Function.Injective ρ → ∀ (Q : MvPolynomial ι ℂ) (u : κ → V), polyDeriv (MvPolynomial.rename ρ Q) u F x = polyDeriv Q (u ∘ ρ) F x := by
  intro V _ _ _ K F hK hF hd x ι κ ρ hρ Q u
  classical
  unfold polyDeriv
  rw [MvPolynomial.support_rename_of_injective hρ,
    Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hρ h)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_rename_mapDomain ρ hρ]
  congr 1
  apply term_eq (iteratedFDeriv_symm hK hF hd x)
  rw [ofFn_get_cast, ofFn_get_cast, ← List.map_map]
  apply List.Perm.map
  rw [← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList, Multiset.coe_toList,
    Finsupp.toMultiset_map]

end GlobalTheory.ConvexCutOff
