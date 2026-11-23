import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommutantScalar

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.HilbTensorUnitary

open GlobalTheory.HilbTensorRep

theorem isURep_tensor {ι : Type} [Fintype ι] {H : ι → Type} [∀ i, NormedAddCommGroup (H i)]
    [∀ i, InnerProductSpace ℂ (H i)] {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    {tens : (∀ i, H i) → Hs} {G : ι → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    {π : ∀ i, G i →* (H i →L[ℂ] H i)} {σs : (∀ i, G i) → (Hs →L[ℂ] Hs)}
    (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (hd : Dense (Submodule.span ℂ (Set.range tens) : Set Hs))
    (hs : ∀ g x, σs g (tens x) = tens fun i => π i (g i) (x i))
    (hn : ∀ i g a, ‖π i g a‖ = ‖a‖) (hc : ∀ i a, Continuous fun g => π i g a) :
    IsURep σs := by
  classical
  have h1 : σs 1 = 1 := by
    apply ext_op hd
    intro x
    rw [hs]
    simp
  have hmul : ∀ a b, σs (a * b) = (σs a).comp (σs b) := by
    intro a b
    apply ext_op hd
    intro x
    rw [ContinuousLinearMap.comp_apply, hs, hs, hs]
    simp [Pi.mul_apply, map_mul, ContinuousLinearMap.mul_apply]
  have hnorm : ∀ g u, ‖σs g u‖ = ‖u‖ := by
    intro g u
    have key : ⟪σs g u, σs g u⟫_ℂ = ⟪u, u⟫_ℂ := by
      rw [← inner_inv hi hd hs hn g (σs g u) u, ← ContinuousLinearMap.comp_apply, ← hmul,
        inv_mul_cancel, h1, ContinuousLinearMap.one_apply]
    have h2 : ‖σs g u‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), key]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  let S : Submodule ℂ Hs :=
    { carrier := {u | Continuous fun g => σs g u}
      add_mem' := fun {a b} ha hb => by
        show Continuous fun g => σs g (a + b)
        simp only [map_add]
        exact ha.add hb
      zero_mem' := by
        show Continuous fun g => σs g 0
        simp only [map_zero]
        exact continuous_const
      smul_mem' := fun c a ha => by
        show Continuous fun g => σs g (c • a)
        simp only [map_smul]
        exact ha.const_smul c }
  have hmemS : ∀ u, u ∈ S ↔ Continuous fun g => σs g u := fun u => Iff.rfl
  have htens : ∀ x, tens x ∈ S := by
    intro x
    rw [hmemS]
    have e : (fun g => σs g (tens x)) = fun g => tens fun i => π i (g i) (x i) := by
      funext g
      exact hs g x
    rw [e]
    exact (continuous_tens hi).comp (continuous_pi fun i => (hc i (x i)).comp (continuous_apply i))
  have hclosed : IsClosed (S : Set Hs) := by
    apply isClosed_of_closure_subset
    intro u hu
    show Continuous fun g => σs g u
    rw [continuous_iff_continuousAt]
    intro g0
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨b, hb, hub⟩ := Metric.mem_closure_iff.1 hu (ε / 3) (by positivity)
    have hbc : Continuous fun g => σs g b := hb
    filter_upwards [Metric.tendsto_nhds.1 hbc.continuousAt (ε / 3) (by positivity)] with g hg
    have d1 : dist (σs g u) (σs g b) = dist u b := by
      rw [dist_eq_norm, ← map_sub, hnorm, ← dist_eq_norm]
    have d2 : dist (σs g0 b) (σs g0 u) = dist u b := by
      rw [dist_eq_norm, ← map_sub, hnorm, ← dist_eq_norm, dist_comm]
    calc dist (σs g u) (σs g0 u)
        ≤ dist (σs g u) (σs g b) + dist (σs g b) (σs g0 b) + dist (σs g0 b) (σs g0 u) :=
          dist_triangle4 _ _ _ _
      _ < ε / 3 + ε / 3 + ε / 3 := by rw [d1, d2]; linarith
      _ = ε := by ring
  have hall : ∀ u, u ∈ S := by
    intro u
    have hle : (Submodule.span ℂ (Set.range tens) : Set Hs) ⊆ S :=
      Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact htens x)
    have hcl := closure_minimal hle hclosed
    rw [hd.closure_eq] at hcl
    exact hcl (Set.mem_univ u)
  exact ⟨h1, hmul, hnorm, fun u => hall u⟩

theorem isURep_rows :
    ∀ B : RowsAut, (∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v)) → IsURep B.σs := by
  intro B hB
  have hmem : ∀ v (g : Formalism.REAL.UJ (B.I.ε v)), uMat g ∈ UJset (B.I.ε v) := fun v g => g.2
  have hcu : ∀ v, Continuous fun g : Formalism.REAL.UJ (B.I.ε v) => uMat g :=
    fun v => Units.continuous_val.comp continuous_subtype_val
  exact isURep_tensor (H := B.H) (tens := B.tens)
    (π := fun v =>
      { toFun := fun g => B.σ v (uMat g)
        map_one' := (hB v).1.1
        map_mul' := fun a b => (hB v).1.2 _ (hmem v a) _ (hmem v b) })
    B.tens_spec.1 B.tens_spec.2.2 (fun g x => B.tens_spec.2.1 g x)
    (fun v g a => (hB v).2.1 _ (hmem v g) a)
    (fun v a => ((hB v).2.2 a).comp_continuous (hcu v) (hmem v))

end GlobalTheory.HilbTensorUnitary
