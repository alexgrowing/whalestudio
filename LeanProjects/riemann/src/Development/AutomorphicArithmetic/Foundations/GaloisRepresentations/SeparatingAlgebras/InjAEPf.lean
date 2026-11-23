import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.injAE_pf :
    UpperTheory.Gal.Gen.NullZero → UpperTheory.Gal.Gen.InjAE := by
  intro hN n
  have h : ∀ i j : Fin n, ∀ᵐ θ : Fin n → UnitAddCircle, i ≠ j → pt θ i ≠ pt θ j := by
    intro i j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun θ h => absurd hij h)
    · have hp : (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin n) ℂ) ≠ 0 :=
        sub_ne_zero.mpr (fun e => hij (MvPolynomial.X_injective e))
      filter_upwards [hN n _ hp] with θ hθ _ e
      apply hθ
      simp [e]
  have h2 : ∀ᵐ θ : Fin n → UnitAddCircle, ∀ i j : Fin n, i ≠ j → pt θ i ≠ pt θ j :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun j => h i j
  filter_upwards [h2] with θ hθ i j e
  by_contra hne
  exact hθ i j hne e
