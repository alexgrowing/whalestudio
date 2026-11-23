import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.coefBd :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (φ : S4 F) (C : Set (G1 F)) (U : Submodule ℂ (S4 F)), IsCompact C → FiniteDimensional ℂ U → (∀ k ∈ C, W.Om k φ ∈ U) →
    ∃ (n : ℕ) (b : Fin n → S4 F) (c : Fin n → G1 F → ℂ) (B : ℝ), (∀ i, b i ∈ U) ∧ (∀ i, ContinuousOn (c i) C) ∧
    ∀ k ∈ C, (∀ i, ‖c i k‖ ≤ B) ∧ W.Om k φ = ∑ i, c i k • b i := by
  intro F E _ _ _ _ _ _ _ D W φ C U hC hU hmem
  haveI := hU
  let b := Module.finBasis ℂ U
  let ev : V4 F → Module.Dual ℂ U := fun v =>
    { toFun := fun u => (u.1).1 v, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have htop : Submodule.span ℂ (Set.range ev) = ⊤ := by
    have hb : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      rw [Submodule.mem_dualCoannihilator] at hu
      have : u = 0 := by
        apply Subtype.ext
        apply Subtype.ext
        funext v
        exact hu (ev v) (Submodule.subset_span ⟨v, rfl⟩)
      simpa using this
    have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev))
    rw [← h2, hb]
    simp
  have hco : ∀ i, ∃ a : V4 F →₀ ℂ, a.sum (fun v x => x • ev v) = b.coord i := by
    intro i
    have h3 : b.coord i ∈ Submodule.span ℂ (Set.range ev) := by
      rw [htop]
      trivial
    exact (Finsupp.mem_span_range_iff_exists_finsupp).1 h3
  choose a ha using hco
  let c : Fin (Module.finrank ℂ U) → G1 F → ℂ := fun i k => ∑ v ∈ (a i).support, a i v * (W.Om k φ).1 v
  have hc : ∀ i, Continuous (c i) := by
    intro i
    refine continuous_finset_sum _ fun v _ => continuous_const.mul ?_
    exact (W.cont φ).comp (continuous_id.prodMk continuous_const)
  have hB : ∀ i, ∃ B : ℝ, ∀ k ∈ C, ‖c i k‖ ≤ B := fun i =>
    hC.exists_bound_of_continuousOn (hc i).continuousOn
  choose B hB using hB
  refine ⟨Module.finrank ℂ U, fun i => (b i).1, c, ∑ i, |B i|, fun i => (b i).2,
    fun i => (hc i).continuousOn, ?_⟩
  intro k hk
  refine ⟨fun i => ?_, ?_⟩
  · calc ‖c i k‖ ≤ B i := hB i k hk
      _ ≤ |B i| := le_abs_self _
      _ ≤ ∑ i, |B i| := Finset.single_le_sum (f := fun i => |B i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  · have hck : ∀ i, b.repr ⟨W.Om k φ, hmem k hk⟩ i = c i k := by
      intro i
      have h4 : b.coord i ⟨W.Om k φ, hmem k hk⟩ = c i k := by
        rw [← ha i, Finsupp.sum, LinearMap.sum_apply]
        rfl
      simpa using h4
    have h5 := b.sum_repr ⟨W.Om k φ, hmem k hk⟩
    have h6 := congrArg Subtype.val h5
    simp only [hck, Submodule.coe_sum, Submodule.coe_smul] at h6
    exact h6.symm
