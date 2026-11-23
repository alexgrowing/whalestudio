import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

noncomputable def holUnifReparam {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (e : (Fin g → ℂ) → ℂ) (he : Differentiable ℂ e) (hne : ∀ z, e z ≠ 0) :
    HolUnif A L g where
  ex z := u.ex (φ z)
  ex_add z w := by rw [map_add, u.ex_add]
  ex_onto := u.ex_onto.comp φ.surjective
  Λ := u.Λ.comap (φ.toLinearMap.restrictScalars ℤ)
  ker z := u.ker (φ z)
  discrete := by
    haveI := u.discrete
    have hc : Continuous (fun z : Fin g → ℂ => φ z) := φ.toContinuousLinearEquiv.continuous
    refine DiscreteTopology.of_continuous_injective
      (f := fun x : u.Λ.comap (φ.toLinearMap.restrictScalars ℤ) => (⟨φ x.1, x.2⟩ : u.Λ))
      ((hc.comp continuous_subtype_val).subtype_mk _) ?_
    intro x y h
    exact Subtype.ext (φ.injective (congrArg Subtype.val h))
  full := by
    have h1 : ((u.Λ.comap (φ.toLinearMap.restrictScalars ℤ) : Submodule ℤ (Fin g → ℂ)) : Set (Fin g → ℂ)) =
        (φ.symm.toLinearMap.restrictScalars ℝ) '' (u.Λ : Set (Fin g → ℂ)) := by
      ext z
      constructor
      · intro hz
        exact ⟨φ z, hz, φ.symm_apply_apply z⟩
      · rintro ⟨w, hw, rfl⟩
        show φ (φ.symm w) ∈ u.Λ
        rwa [φ.apply_symm_apply]
    rw [h1, ← Submodule.map_span, u.full, Submodule.map_top, LinearMap.range_eq_top]
    exact φ.symm.surjective
  hol U f := by
    have hc : Differentiable ℂ (fun z : Fin g → ℂ => φ z) := φ.toContinuousLinearEquiv.differentiable
    exact ⟨(u.hol U f).1.preimage hc.continuous, (u.hol U f).2.comp hc.differentiableOn (fun _ hz => hz)⟩
  fr i z := u.fr i (φ z) / e z
  fr_hol i := by
    have hc : Differentiable ℂ (fun z : Fin g → ℂ => φ z) := φ.toContinuousLinearEquiv.differentiable
    have h1 : DifferentiableOn ℂ (fun z => u.fr i (φ z)) {z | ⊤ ≤ (u.ex (φ z)).left ⁻¹ᵁ L.U i} :=
      (u.fr_hol i).comp hc.differentiableOn (fun _ hz => hz)
    have h2 : Differentiable ℂ (fun z => (e z)⁻¹) := he.inv hne
    simp only [div_eq_mul_inv]
    exact h1.mul h2.differentiableOn
  fr_ne i z hz := div_ne_zero (u.fr_ne i _ hz) (hne z)
  fr_compat i j z hz := by
    rw [u.fr_compat i j _ hz, mul_div_assoc]

theorem exists_holUnif_reparam :
    ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (e : (Fin g → ℂ) → ℂ), Differentiable ℂ e → (∀ z, e z ≠ 0) → e 0 = 1 → ∃ u' : HolUnif A L g, (∀ z, u'.ex z = u.ex (φ z)) ∧ (∀ z, z ∈ u'.Λ ↔ φ z ∈ u.Λ) ∧ (∀ rig, u.IsRig rig → u'.IsRig rig) ∧ (∀ s θ, u.IsFn s θ → u'.IsFn s (fun z => e z * θ (φ z))) ∧ ∀ w v, u.IsDiff (φ w) v → u'.IsDiff w v := by
  intro A _ L g u φ e he hne h0
  refine ⟨holUnifReparam u φ e he hne, fun _ => rfl, fun _ => Iff.rfl, ?_, ?_, ?_⟩
  · intro rig hr j hj
    show u.fr _ (φ 0) / e 0 = _
    rw [map_zero, h0, div_one]
    exact hr j hj
  · intro s θ hs i z hz
    have h := hs i (φ z) hz
    show valAt' (u.ex (φ z)).left _ _ = e z * θ (φ z) * (u.fr i (φ z) / e z)
    rw [h]
    have := hne z
    field_simp
  · intro w v hv U h f
    rw [hv U h f]
    have key := φ.toContinuousLinearEquiv.comp_right_fderiv
      (f := fun z => valAt' (u.ex z).left U f) (x := 0)
    have h2 := congrArg (fun T => T w) key
    simp only [map_zero] at h2
    exact h2.symm

end GlobalTheory
