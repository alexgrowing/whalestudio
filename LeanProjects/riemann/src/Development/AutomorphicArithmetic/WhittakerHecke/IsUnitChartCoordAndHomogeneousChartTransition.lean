import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjSpaceHom
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupUniversal

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor FunctorialResolution.Blowup
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem projective_chart_overlap {R : Type} [CommRing R] {N : ℕ} {W : Scheme.{0}} (h : W ⟶ PSpace R N)
    (O : W.Opens) (a b : Fin (N + 1))
    (ha : O ≤ h ⁻¹ᵁ Proj.basicOpen (grading R N) (X a))
    (hb : O ≤ h ⁻¹ᵁ Proj.basicOpen (grading R N) (X b))
    (n : ℕ) (F : MvPolynomial (Fin (N + 1)) R) (hF : F ∈ grading R N (n • 1)) :
    h.appLE _ O ha (chartHom a F) *
        h.appLE _ O hb (chartHom b (X a : MvPolynomial (Fin (N + 1)) R)) ^ n =
      h.appLE _ O hb (chartHom b F) := by
  have hO : O ≤ h ⁻¹ᵁ Proj.basicOpen (grading R N) (X b * X a) := by
    rw [Proj.basicOpen_mul]
    exact fun x hx => ⟨hb hx, ha hx⟩
  have e1 : h.appLE _ O ha =
      (PSpace R N).presheaf.map (homOfLE (basicOpen_mul_le_right a b)).op ≫ h.appLE _ O hO :=
    (Scheme.Hom.map_appLE h hO _).symm
  have e2 : h.appLE _ O hb =
      (PSpace R N).presheaf.map (homOfLE (basicOpen_mul_le_left a b)).op ≫ h.appLE _ O hO :=
    (Scheme.Hom.map_appLE h hO _).symm
  have hF' : F ∈ grading R N n := by simpa using hF
  rw [e1, e2]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  rw [chartHom_of_mem a hF']
  exact map_mul_pow_eq _ _ (chart_identity a b hF)

theorem UpperTheory.isUnit_chart_coord_and_homogeneous_chart_transition :
    ∀ {R : Type} [CommRing R] {N : ℕ} {W : Scheme.{0}} (h : W ⟶ PSpace R N) (O : W.Opens) (a b : Fin (N + 1))
        (ha : O ≤ h ⁻¹ᵁ Proj.basicOpen (grading R N) (X a)) (hb : O ≤ h ⁻¹ᵁ Proj.basicOpen (grading R N) (X b)),
        IsUnit (h.appLE _ O hb (chartHom b (X a : MvPolynomial (Fin (N + 1)) R))) ∧
        ∀ (n : ℕ) (F : MvPolynomial (Fin (N + 1)) R), F.IsHomogeneous n →
          h.appLE _ O ha (chartHom a F) * h.appLE _ O hb (chartHom b (X a : MvPolynomial (Fin (N + 1)) R)) ^ n =
            h.appLE _ O hb (chartHom b F) := by
  intro R _ N W h O a b ha hb
  refine ⟨?_, fun n F hF => projective_chart_overlap h O a b ha hb n F ?_⟩
  · have key := projective_chart_overlap h O a b ha hb 1 (X b) (by simpa using X_mem b)
    rw [pow_one, chartHom_X_self, map_one] at key
    exact IsUnit.of_mul_eq_one_right _ key
  · have : F ∈ grading R N n := hF
    simpa using this
