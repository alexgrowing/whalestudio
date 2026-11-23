import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfCommuteOfSeparable

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.NilChangeVar

namespace GlobalTheory.CompanionTheory.LocVan

theorem nilChange_of_flag : NilChange := by
  intro n d W₁ W₂ hreg _ hle h1 h2
  let L : nilrad W₁ W₂ ≃ₗ[ℝ] nilrad W₁ W₂ :=
    LinearEquiv.ofInjectiveEndo (slinN d h1 h2 - LinearMap.id) (slinN_injective d h1 h2 hreg)
  have hLval : ∀ X, (L X).1 = slin d X.1 - X.1 := fun X => by
    simp [L, slinN]
  have hLc : Continuous L := by
    refine Continuous.subtype_mk (f := fun X : nilrad W₁ W₂ => (L X).1) ?_ _ |>.congr fun X => rfl
    have e : (fun X : nilrad W₁ W₂ => (L X).1) = fun X => slin d X.1 - X.1 := funext hLval
    rw [e]
    exact ((continuous_slin d).comp continuous_subtype_val).sub continuous_subtype_val
  let Q : nilrad W₁ W₂ → nilrad W₁ W₂ := fun X =>
    ⟨quad d X.1, two_mem hle (quadratic_term_nilradical_mem d h1 h2 X.2).1 (quadratic_term_nilradical_mem d h1 h2 X.2).2⟩
  have hQc : Continuous Q :=
    Continuous.subtype_mk ((continuous_quad d).comp continuous_subtype_val) _
  have hLF : ∀ y ∈ nilrad2 W₁ W₂, L y ∈ nilrad2 W₁ W₂ := fun y hy => by
    obtain ⟨hT, hT'⟩ := semilinear_term_nilradical_mem d h1 h2 hy.1 hy.2
    refine ⟨fun z => ?_, fun z hz => ?_⟩
    · rw [hLval, Matrix.sub_mulVec]; exact W₁.sub_mem (hT z) (hy.1 z)
    · rw [hLval, Matrix.sub_mulVec, hT' z hz, hy.2 z hz, sub_zero]
  have hQF : ∀ X, Q X ∈ nilrad2 W₁ W₂ := fun X => quadratic_term_nilradical_mem d h1 h2 X.2
  have hQinv : ∀ X, ∀ Y ∈ nilrad2 W₁ W₂, Q (X + Y) = Q X := fun X Y hY =>
    Subtype.ext (quad_add d h1 h2 X.2 hle hY.1 hY.2)
  refine ⟨fun X => L X + Q X, hLc.add hQc, fun X => ?_, ?_⟩
  · rw [eq_inv_mul_iff_mul_eq]
    refine Units.ext ?_
    have e : (uOf (L X + Q X)).val = 1 + (slin d X.1 - X.1 + quad d X.1) := by
      rw [uOf_val, Submodule.coe_add, hLval]
    rw [Units.val_mul, e]
    exact twist_val d h1 h2 (uOf X) X.1 X.2 rfl
  · intro _ _ ν _
    obtain ⟨Φ, c, _, hΦ, hmap⟩ := exists_homeo_map_eq_smul ν (nilrad2 W₁ W₂) L hLF Q hQc hQF hQinv
    refine ⟨c, ?_⟩
    have e : (fun X => L X + Q X) = Φ := funext fun X => (hΦ X).symm
    rw [e]
    exact hmap

end GlobalTheory.CompanionTheory.LocVan
