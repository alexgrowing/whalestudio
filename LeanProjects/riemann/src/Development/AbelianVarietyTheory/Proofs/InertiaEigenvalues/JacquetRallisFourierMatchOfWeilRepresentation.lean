import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianBlockInvariantsIffIsometryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOrbitalDescentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryActionHermitianInvariantsTransitiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisOrbitalIntegralsInvariantLocallyConStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisMatchOfDenseSeparableStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisLinearOrbitalIntegralDescentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierPreservesTestFixesUnitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSelfDualMeasuresAndAbsKScaleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleHermitianPairIsGenCompanionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisInvKRegularIffIsUnitStatement

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem fourierMatchAt_of_weil (hW : WeilEt) (hR : RankOne) (hG : GammaOne) {r : ℕ} {F E : Type}
    [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E]
    (M : Meas r F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (f' : Gl r F → ℂ) (f : Hn r F E → ℂ)
    (hf' : IsTest f') (hf : IsTest f) (hm : Match M f' f) (a : Inv r F) (ha : Delta a ≠ 0)
    (hsep : (companion a.1).charpoly.Separable) :
    MatchAt M (fourG M ψ f') (fourU M ψ f) a := by
  obtain ⟨A, τ, hτ⟩ := GlobalTheory.T.exists_etaleHermitianPair_isGen_companion F E r a.1 hsep
  obtain ⟨hbij, hmom⟩ := GlobalTheory.T.jacquetRallis_invK_regular_iff_isUnit F E A r τ a.1 a.2.2 hτ
  obtain ⟨a₀, ha₀⟩ := hbij.2 a.2.1
  have ha₀' : (fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * a₀)) = a.2.1 := ha₀
  have hinv : A.invK τ a.1 a.2.2 a₀ = a := by
    simp only [Et.invK, ha₀']
  have hu₀ : IsUnit a₀ := (hmom a₀).2.mp (by rw [hinv]; exact ha)
  obtain ⟨⟨m⟩, -⟩ := GlobalTheory.T.exists_selfDual_measures_and_absK_scale F E A ψ hψ
  obtain ⟨-, -, -, -, -, -, ⟨S, -, hS⟩, -⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  obtain ⟨φ', κ, hφ', hlin⟩ := GlobalTheory.T.jacquetRallis_linear_orbitalIntegral_descent F E A ψ hψ m r M τ a.1 a.2.2 hτ f' hf'
  obtain ⟨-, -, huniq, -⟩ := GlobalTheory.T.unitary_action_hermitian_invariants_transitive F E r
  obtain ⟨-, horbU, -, -⟩ := GlobalTheory.T.jacquetRallisOrbitalIntegrals_invariant_locallyConstant F E r M
  obtain ⟨hL11a, hL11b⟩ := GlobalTheory.T.hermitianBlock_invariants_iff_isometry F E A r τ a.1 a.2.2 hτ
  have key : ∀ x : A.Kˣ, ∃ φx : A.L → ℂ, IsTest φx ∧
      ((∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom (x : A.K) j) →
        ∃ (j : A.L ≃ₗ[E] (Fin r → E)) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)), A.IsIsom (x : A.K) j ∧
          (∀ y, HasInv ((Ax, j y, a.2.2) : Hn r F E) (A.invK τ a.1 a.2.2 ((x : A.K) * A.NL y))) ∧
          ∀ y : A.L, IsUnit y → orbU M f (Ax, j y, a.2.2) = A.orbL m.ν φx y ∧
            orbU M (fourU M ψ f) (Ax, j y, a.2.2) = A.orbL m.ν (fourB (m.μL x) (A.kerL ψ x) φx) y) ∧
      ((¬ ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom (x : A.K) j) → φx = 0) := by
    intro x
    by_cases hx : ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom (x : A.K) j
    · obtain ⟨j, hj⟩ := hx
      obtain ⟨Ax, hAx, hinvAx⟩ := hL11b (x : A.K) j hj
      obtain ⟨φx, hφx, hrel⟩ := GlobalTheory.T.exists_test_orbU_eq_orbL F E A ψ hψ m r M τ a.1 a.2.2 hτ x j hj Ax hAx f hf
      exact ⟨φx, hφx, fun _ => ⟨j, Ax, hj, hinvAx, hrel⟩, fun h => absurd ⟨j, hj⟩ h⟩
    · exact ⟨0, ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩, fun h => absurd h hx, fun _ => rfl⟩
  choose φ hφt hφi hφ0 using key
  choose γ Wr hWr using fun x : A.Kˣ => hW F E A ψ hψ x (m.μL x) (m.sdL x)
  have hunit : ∀ (x : A.Kˣ) (y : A.L), IsUnit y → IsUnit ((x : A.K) * A.NL y) := fun x y hy =>
    x.isUnit.mul (hy.map (Algebra.norm A.K))
  have hyp : ∀ x ∈ S, ∀ y : A.L, IsUnit y → κ * A.orbK m.μK φ' (x * A.NL y) = A.orbL m.ν (φ x) y := by
    intro x _ y hy
    have hb := hunit x y hy
    rw [← (hlin _ hb).1]
    by_cases hx : ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom (x : A.K) j
    · obtain ⟨j, Ax, -, hinvAx, hrel⟩ := hφi x hx
      rw [← (hrel y hy).1]
      exact (hm _ ((hmom _).2.mpr hb)).1 _ (hinvAx y)
    · rw [hφ0 x hx]
      have h0 : orbG M f' (sec (A.invK τ a.1 a.2.2 ((x : A.K) * A.NL y))) = 0 := by
        apply (hm _ ((hmom _).2.mpr hb)).2
        rintro ⟨X, hX⟩
        obtain ⟨j, hj, -⟩ := hL11a _ X hb hX (x : A.K) y hy rfl
        exact hx ⟨j, hj⟩
      rw [h0]
      simp [Et.orbL]
  have hRk := hR F E A ψ hψ m S hS γ Wr (fun x _ => hWr x) φ' φ κ hφ' (fun x _ => hφt x) hyp
  have hG1 : ∀ (x : A.Kˣ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom (x : A.K) j → γ x = 1 :=
    fun x j hj => hG F E A ψ hψ x (m.μL x) (m.sdL x) A.etaK (γ x) (Wr x) (hWr x) r j hj
  obtain ⟨x, ⟨hxS, y, hy, hxy⟩, -⟩ := hS hu₀.unit
  have hxy' : a₀ = x * A.NL y := by simpa using hxy
  have hb := hunit x y hy
  have hlhs : orbG M (fourG M ψ f') (sec a) =
      γ x * A.orbL m.ν (fourB (m.μL x) (A.kerL ψ x) (φ x)) y := by
    calc orbG M (fourG M ψ f') (sec a)
        = orbG M (fourG M ψ f') (sec (A.invK τ a.1 a.2.2 ((x : A.K) * A.NL y))) := by rw [← hxy', hinv]
      _ = κ * A.orbK m.μK (A.fourK m.μK ψ φ') ((x : A.K) * A.NL y) := (hlin _ hb).2
      _ = _ := hRk x hxS y hy
  constructor
  · intro X hX
    have hX' : HasInv X (A.invK τ a.1 a.2.2 a₀) := by rw [hinv]; exact hX
    obtain ⟨j₁, hj₁, -⟩ := hL11a a₀ X hu₀ hX' (x : A.K) y hy hxy'
    obtain ⟨j, Ax, hj, hinvAx, hrel⟩ := hφi x ⟨j₁, hj₁⟩
    have hXa : HasInv ((Ax, j y, a.2.2) : Hn r F E) a := by
      have := hinvAx y
      rw [← hxy', hinv] at this
      exact this
    obtain ⟨g, hg, -⟩ := huniq _ X a ha hXa hX
    rw [hlhs, hG1 x j hj, one_mul, ← (hrel y hy).2, ← hg, horbU]
  · intro hno
    have hx : ¬ ∃ j : A.L ≃ₗ[E] (Fin r → E), A.IsIsom (x : A.K) j := by
      intro hx
      obtain ⟨j, Ax, -, hinvAx, -⟩ := hφi x hx
      have := hinvAx y
      rw [← hxy', hinv] at this
      exact hno ⟨_, this⟩
    rw [hlhs, hφ0 x hx]
    simp [fourB, Et.orbL]

theorem fourierMatch_of_weil : WeilEt → RankOne → GammaOne → ∀ r, FourierMatch r := by
  intro hW hR hG r F E _ _ _ _ _ M ψ hψ f' f hf' hf hm
  obtain ⟨h4G, h4U, -⟩ := GlobalTheory.T.partialFourier_preserves_test_fixes_unit F E r M ψ hψ
  exact (GlobalTheory.T.jacquetRallis_match_of_dense_separable F E r M _ _ (h4G f' hf') (h4U f hf)).1
    (fun a ha hsep => fourierMatchAt_of_weil hW hR hG M ψ hψ f' f hf' hf hm a ha hsep)

end GlobalTheory.JR
