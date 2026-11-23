import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.Obj

theorem exists_detGen_away : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (B : Type) [CommRing B] [Algebra ℂ B]
    [Algebra.Smooth ℂ B] (R : Type) [CommRing R] [Algebra ℂ R] [IsLocalRing R] (j : B →ₐ[ℂ] R) (X : Obj F 𝔠 (Sp B)),
    ∃ (B' : Type) (_ : CommRing B') (_ : Algebra ℂ B') (_ : Algebra.Smooth ℂ B') (X₁ : Obj F 𝔠 (Sp B'))
      (_ : X₁.DetGen) (k : B →ₐ[ℂ] B') (j' : B' →ₐ[ℂ] R) (q : X₁.A.left ⟶ X.A.left),
      X₁.IsPullBy X (spMap (k : B →+* B')) q ∧ j'.comp k = j := by
  intro F _ _ 𝔠 B _ _ _ R _ _ _ j X
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.T.lie_algebra_finite_projective_rank X
  let p : Ideal B := (IsLocalRing.maximalIdeal R).comap j
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  haveI : Module.FinitePresentation B X.Lie := Module.finitePresentation_of_projective B X.Lie
  haveI : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl X.Lie) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨f, hf, hfree, hfr⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl X.Lie) (Localization.AtPrime p)
  have hju : IsUnit (j f) := by
    by_contra h
    exact hf ((IsLocalRing.mem_maximalIdeal _).2 h)
  let B' := Localization.Away f
  let k : B →ₐ[ℂ] B' := IsScalarTower.toAlgHom ℂ B B'
  let j' : B' →ₐ[ℂ] R := IsLocalization.liftAlgHom (M := Submonoid.powers f) (f := j) (by
    rintro ⟨_, n, rfl⟩
    simpa using hju.pow n)
  have hjk : j'.comp k = j := AlgHom.ext fun x ↦ by
    simp [j', k, IsLocalization.liftAlgHom, IsLocalization.lift_eq]
  haveI : Nontrivial B' := (j' : B' →+* R).domain_nontrivial
  haveI : Algebra.Smooth B B' := Algebra.Smooth.of_isLocalization_Away f
  haveI : Algebra.Smooth ℂ B' := Algebra.Smooth.comp ℂ B B'
  obtain ⟨X₁, q, hq⟩ := exists_isPullBy X (spMap (algebraMap B B'))
  obtain ⟨e, -, -⟩ := exists_lieEquiv (R' := B') hq
  haveI : Module.Finite B' (LocalizedModule.Away f X.Lie) :=
    Module.Finite.of_isLocalizedModule (Submonoid.powers f) (LocalizedModule.mkLinearMap (Submonoid.powers f) X.Lie)
  have hd : Module.finrank B' (LocalizedModule.Away f X.Lie) = Module.finrank ℚ F := by
    rw [hfr]
    exact hrk ⟨p, inferInstance⟩
  let b₀ := Module.finBasisOfFinrankEq B' (LocalizedModule.Away f X.Lie) hd
  let hbc := IsLocalizedModule.isBaseChange (Submonoid.powers f) B'
    (LocalizedModule.mkLinearMap (Submonoid.powers f) X.Lie)
  let b₁ : Module.Basis (Fin (Module.finrank ℚ F)) B' X₁.Lie := b₀.map (hbc.equiv.symm ≪≫ₗ e)
  exact ⟨B', inferInstance, inferInstance, inferInstance, X₁, DetGen.ofBasis X₁ b₁, k, j', q, hq, hjk⟩

end GlobalTheory.RealMult.Obj
