import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Metric.QuotHol

theorem differentiableOn_det {m n : ℕ} {A : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ}
    {V : Set (Fin n → ℂ)} (hA : ∀ i j, DifferentiableOn ℂ (fun t => A t i j) V) :
    DifferentiableOn ℂ (fun t => (A t).det) V := by
  simp only [Matrix.det_apply]
  refine DifferentiableOn.fun_sum fun σ _ => ?_
  refine DifferentiableOn.const_smul ?_ _
  have hs : ∀ s : Finset (Fin m), DifferentiableOn ℂ (fun t => ∏ i ∈ s, A t (σ i) i) V := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      exact differentiableOn_const _
    | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hA _ _).fun_mul ih
  exact hs Finset.univ

theorem exists_complement {k g' : ℕ} (v : Fin k → Fin (k + g') → ℂ)
    (hv : LinearIndependent ℂ v) :
    ∃ f : Fin g' → Fin (k + g') → ℂ,
      (Matrix.of fun i j => Sum.elim v f (finSumFinEquiv.symm j) i :
        Matrix (Fin (k + g')) (Fin (k + g')) ℂ).det ≠ 0 := by
  classical
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl (Submodule.span ℂ (Set.range v))
  have hfr : Module.finrank ℂ W' = g' := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hW'
    have h2 := finrank_span_eq_card hv
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1 h2
    omega
  let bW := Module.finBasisOfFinrankEq ℂ W' hfr
  let f : Fin g' → Fin (k + g') → ℂ := fun j => (bW j : Fin (k + g') → ℂ)
  have hf : LinearIndependent ℂ f :=
    bW.linearIndependent.map' W'.subtype (Submodule.ker_subtype W')
  have hdisj : Disjoint (Submodule.span ℂ (Set.range v)) (Submodule.span ℂ (Set.range f)) := by
    refine hW'.disjoint.mono_right ?_
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (bW j).2
  have hs : LinearIndependent ℂ (Sum.elim v f) := hv.sum_type hf hdisj
  have hc := hs.comp _ (finSumFinEquiv.symm.injective)
  refine ⟨f, ?_⟩
  have hu := Matrix.linearIndependent_cols_iff_isUnit
    (A := (Matrix.of fun i j => Sum.elim v f (finSumFinEquiv.symm j) i :
      Matrix (Fin (k + g')) (Fin (k + g')) ℂ)) |>.1 hc
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero

theorem exists_holomorphic_quotient (g' k g n : ℕ) (U : Set (Fin n → ℂ))
    (e : Fin k → (Fin n → ℂ) → Fin g → ℂ) (t₀ : Fin n → ℂ) (hU : IsOpen U) (ht₀ : t₀ ∈ U)
    (hg : k + g' = g) (he : ∀ i, DifferentiableOn ℂ (e i) U)
    (hli : LinearIndependent ℂ (fun i => e i t₀)) :
    ∃ V : Set (Fin n → ℂ), IsOpen V ∧ t₀ ∈ V ∧ V ⊆ U ∧
      ∃ q : (Fin n → ℂ) → (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ),
        (∀ x, DifferentiableOn ℂ (fun t => q t x) V) ∧
        ∀ t ∈ V, Function.Surjective (q t) ∧
          LinearMap.ker (q t) = Submodule.span ℂ (Set.range fun i => e i t) := by
  classical
  subst hg
  obtain ⟨f, hf⟩ := exists_complement (fun i => e i t₀) hli
  let M : (Fin n → ℂ) → Matrix (Fin (k + g')) (Fin (k + g')) ℂ := fun t =>
    Matrix.of fun i j => Sum.elim (fun a => e a t) f (finSumFinEquiv.symm j) i
  have hMc : ∀ t a i, M t i (Fin.castAdd g' a) = e a t i := by
    intro t a i
    simp [M]
  have hMn : ∀ t b i, M t i (Fin.natAdd k b) = f b i := by
    intro t b i
    simp [M]
  have hMent : ∀ i j, DifferentiableOn ℂ (fun t => M t i j) U := by
    intro i j
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
    rcases s with a | c
    · simp only [finSumFinEquiv_apply_left, hMc]
      exact (differentiableOn_pi.1 (he a)) i
    · simp only [finSumFinEquiv_apply_right, hMn]
      exact differentiableOn_const _
  have hdet : DifferentiableOn ℂ (fun t => (M t).det) U := differentiableOn_det hMent
  let V : Set (Fin n → ℂ) := U ∩ (fun t => (M t).det) ⁻¹' {0}ᶜ
  have hVo : IsOpen V := hdet.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
  have hVU : V ⊆ U := Set.inter_subset_left
  have hinv : ∀ i j, DifferentiableOn ℂ (fun t => (M t)⁻¹ i j) V := by
    intro i j
    have h1 : DifferentiableOn ℂ (fun t => ((M t).det)⁻¹) V :=
      (hdet.mono hVU).inv (fun t ht => ht.2)
    have h2 : DifferentiableOn ℂ (fun t => (M t).adjugate i j) V := by
      simp only [Matrix.adjugate_apply]
      refine differentiableOn_det fun a b => ?_
      by_cases h : a = j
      · subst h
        simp only [Matrix.updateRow_self]
        exact differentiableOn_const _
      · simp only [Matrix.updateRow_ne h]
        exact (hMent a b).mono hVU
    simpa [Matrix.inv_def, Ring.inverse_eq_inv'] using h1.fun_mul h2
  let q : (Fin n → ℂ) → (Fin (k + g') → ℂ) →ₗ[ℂ] (Fin g' → ℂ) := fun t =>
    LinearMap.funLeft ℂ ℂ (Fin.natAdd k) ∘ₗ ((M t)⁻¹).mulVecLin
  have hq : ∀ t x j, q t x j = ((M t)⁻¹ *ᵥ x) (Fin.natAdd k j) := by
    intro t x j
    simp [q, LinearMap.funLeft_apply]
  refine ⟨V, hVo, ⟨ht₀, hf⟩, hVU, q, ?_, ?_⟩
  · intro x
    refine differentiableOn_pi.2 fun j => ?_
    simp only [hq, Matrix.mulVec, dotProduct]
    exact DifferentiableOn.fun_sum fun l _ => (hinv _ l).mul_const _
  · intro t ht
    have hu : IsUnit (M t).det := isUnit_iff_ne_zero.2 ht.2
    have hMi : M t * (M t)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
    have hiM : (M t)⁻¹ * M t = 1 := Matrix.nonsing_inv_mul _ hu
    refine ⟨fun y => ?_, ?_⟩
    · refine ⟨M t *ᵥ (fun j => Sum.elim 0 y (finSumFinEquiv.symm j)), ?_⟩
      ext j
      rw [hq, Matrix.mulVec_mulVec, hiM, Matrix.one_mulVec]
      simp
    · apply le_antisymm
      · intro x hx
        have hx0 : ∀ j, ((M t)⁻¹ *ᵥ x) (Fin.natAdd k j) = 0 := by
          intro j
          rw [← hq, LinearMap.mem_ker.1 hx]
          rfl
        have hxc : x = M t *ᵥ ((M t)⁻¹ *ᵥ x) := by
          rw [Matrix.mulVec_mulVec, hMi, Matrix.one_mulVec]
        obtain ⟨c, hc⟩ : ∃ c, c = (M t)⁻¹ *ᵥ x := ⟨_, rfl⟩
        rw [← hc] at hx0 hxc
        have hsum : x = ∑ a, c (Fin.castAdd g' a) • e a t := by
          conv_lhs => rw [hxc]
          ext i
          simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, hx0, mul_zero,
            Finset.sum_const_zero, add_zero, hMc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          exact Finset.sum_congr rfl fun a _ => mul_comm _ _
        rw [hsum]
        exact Submodule.sum_mem _ fun a _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
      · rw [Submodule.span_le]
        rintro _ ⟨a, rfl⟩
        have hcol : e a t = M t *ᵥ Pi.single (Fin.castAdd g' a) 1 := by
          ext i
          simp [hMc]
        refine LinearMap.mem_ker.2 ?_
        ext j
        rw [hq]
        show ((M t)⁻¹ *ᵥ e a t) (Fin.natAdd k j) = 0
        rw [hcol, Matrix.mulVec_mulVec, hiM, Matrix.one_mulVec]
        refine Pi.single_eq_of_ne ?_ _
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at this
        have := a.2
        omega

end GlobalTheory.CompanionTheory.Metric.QuotHol
