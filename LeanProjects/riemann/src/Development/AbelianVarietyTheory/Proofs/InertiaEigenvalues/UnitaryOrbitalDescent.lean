import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulMatMemUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitaryGroupTorusCutoffStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrbitalIntegralDescendedEqUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportDescendedFunctionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierDescendedFunctionEqPartialFourierStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierPreservesTestFixesUnitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisInvKRegularIffIsUnitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianBlockInvariantsIffIsometryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisOrbitalIntegrandIsLocallyConstantCoStatement

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem unitary_orbital_descent : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (m : A.Meas ψ) (r : ℕ) (M : Meas r F E) (τ : A.K) (p : Fin r → F) (lam : F), A.IsGen τ p → ∀ (x : A.Kˣ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ Ax : selfAdjoint (Matrix (Fin r) (Fin r) E), (∀ z, j (algebraMap A.K A.L τ * z) = Ax.1 *ᵥ j z) → ∀ f : Hn r F E → ℂ, IsTest f → ∃ φ : A.L → ℂ, IsTest φ ∧ ∀ y : A.L, IsUnit y → orbU M f (Ax, j y, lam) = A.orbL m.ν φ y ∧ orbU M (fourU M ψ f) (Ax, j y, lam) = A.orbL m.ν (fourB (m.μL x) (A.kerL ψ x) φ) y := by
  intro F E _ _ _ _ _ A ψ hψ m r M τ p lam hgen x j hx Ax hAx f hf
  have hν : m.ν.IsHaarMeasure := m.nat.1
  set Z : Set (Matrix (Fin r) (Fin r) E) := (fun X : Hn r F E => X.1.1) '' tsupport f with hZdef
  have hZ : IsCompact Z := hf.2.image (continuous_subtype_val.comp continuous_fst)
  obtain ⟨α, hαlc, hαcs, hα0, hα1⟩ := GlobalTheory.T.exists_unitary_group_torus_cutoff F E A r τ p hgen (x : A.K) j hx Ax hAx m.ν hν Z hZ
  have hsuppf : ∀ X, f X ≠ 0 → X.1.1 ∈ Z := fun X hX => ⟨X, subset_tsupport f hX, rfl⟩
  have hsuppF : ∀ X, fourU M ψ f X ≠ 0 → X.1.1 ∈ Z := by
    intro X hX
    by_contra hZ'
    apply hX
    have h0 : ∀ c, f (X.1, c, X.2.2) = 0 := fun c => by
      by_contra hc
      exact hZ' (hsuppf (X.1, c, X.2.2) hc)
    simp [fourU, h0]
  have hFtest : IsTest (fourU M ψ f) := (GlobalTheory.T.partialFourier_preserves_test_fixes_unit F E r M ψ hψ).2.1 f hf
  have hint : ∀ f₀ : Hn r F E → ℂ, IsTest f₀ → ∀ y : A.L, IsUnit y →
      (letI := M.mU; Integrable (fun g => f₀ (actU g (Ax, j y, lam))) M.μU) := by
    intro f₀ hf₀ y hy
    letI := M.mU
    haveI := M.bU
    haveI := M.haarU
    have ha : IsUnit ((x : A.K) * A.NL y) := x.isUnit.mul (hy.map (Algebra.norm A.K))
    have hD := ((GlobalTheory.T.jacquetRallis_invK_regular_iff_isUnit F E A r τ p lam hgen).2 ((x : A.K) * A.NL y)).2.mpr ha
    obtain ⟨Ax', hAx', hinv⟩ := (GlobalTheory.T.hermitianBlock_invariants_iff_isometry F E A r τ p lam hgen).2 x j hx
    have hAA : Ax' = Ax := by
      apply Subtype.ext
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      obtain ⟨z, rfl⟩ := j.surjective v
      simp only [Matrix.toLin'_apply, ← hAx', ← hAx]
    subst hAA
    have ht := (GlobalTheory.T.jacquetRallis_orbitalIntegrand_isLocallyConstantCompactSupport F E r M).2 f₀ hf₀ _ _ hD (hinv y)
    exact ht.1.continuous.integrable_of_hasCompactSupport ht.2
  refine ⟨A.descFn M Ax j lam α f, GlobalTheory.T.isLocallyConstantCompactSupport_descendedFunction F E A r M Ax j lam α hαlc hαcs f hf, fun y hy => ⟨?_, ?_⟩⟩
  · exact (GlobalTheory.T.orbitalIntegral_descended_eq_unitary F E A r M τ x j hx Ax hAx lam m.ν hν α hαlc hα0 Z hα1 f hf.1.continuous hsuppf y
      (hint f hf y hy)).symm
  · rw [GlobalTheory.T.fourier_descendedFunction_eq_partialFourier F E A ψ hψ r M x j hx (m.μL x) (m.sdL x) Ax lam α hαlc hαcs f hf]
    exact (GlobalTheory.T.orbitalIntegral_descended_eq_unitary F E A r M τ x j hx Ax hAx lam m.ν hν α hαlc hα0 Z hα1 _ hFtest.1.continuous hsuppF y
      (hint _ hFtest y hy)).symm

end GlobalTheory.JR
