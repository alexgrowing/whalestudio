import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasWitness
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws

open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv

theorem dense_of_rat_of_span {V : Type} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V]
    [ContinuousSMul ℝ V] (S : Set V) (h0 : (0 : V) ∈ S) (ha : ∀ u ∈ S, ∀ v ∈ S, u + v ∈ S)
    (hq : ∀ q : ℚ, ∀ u ∈ S, (q : ℝ) • u ∈ S) (hS : Submodule.span ℝ S = ⊤) : Dense S := by
  let P : Submodule ℝ V :=
    { carrier := closure S
      zero_mem' := subset_closure h0
      add_mem' := fun {a b} h1 h2 => map_mem_closure₂ continuous_add h1 h2 ha
      smul_mem' := fun t a h1 => by
        have ht : t ∈ closure (Set.range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast t
        refine map_mem_closure₂ (f := fun (s : ℝ) (v : V) => s • v) continuous_smul ht h1 ?_
        rintro _ ⟨q, rfl⟩ u hu
        exact hq q u hu }
  have hP : Submodule.span ℝ S ≤ P := Submodule.span_le.2 subset_closure
  intro z
  exact hP (hS ▸ Submodule.mem_top)

theorem denseRange_pv {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {g : ℕ}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) : DenseRange (pv X idx x) := by
  have hq (q : ℚ) (v : Fin r → E) : pv X idx x ((q : E) • v) = (q : ℝ) • pv X idx x v := by
    rw [pv_smul]
    funext j
    simp
  refine dense_of_rat_of_span _ ⟨0, ?_⟩ ?_ ?_ (span_range_pv idx hs hx)
  · simpa using hq 0 0
  · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    refine ⟨u + v, ?_⟩
    rw [pv, pv, pv, per_add]
    rfl
  · rintro q _ ⟨u, rfl⟩
    exact ⟨_, hq q u⟩

theorem exists_apply_pv_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → ∀ x ∈ X.dom, ∀ θ : (Fin g → ℂ) → ℂ, Continuous θ → θ ≠ 0 → ∃ v : Fin r → E, θ (pv X idx x v) ≠ 0 := by
  intro E _ _ _ r X g bas idx hs x hx θ hθ h0
  by_contra h
  push Not at h
  exact h0 ((denseRange_pv idx hs hx).equalizer hθ continuous_const (funext h))

end GlobalTheory.FrameEquiv
