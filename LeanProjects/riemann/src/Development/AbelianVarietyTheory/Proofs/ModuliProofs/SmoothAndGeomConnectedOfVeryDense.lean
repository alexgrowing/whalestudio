import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmoothOfRelDimOfIsUnitProperFlatStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeometricallyConnectedOpenConditionSmoothProjectStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem of_local_near_veryDense (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q]
    (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (P : Set (Ideal R))
    (hP : ∀ (q : Ideal R) (f : R), q.IsPrime → f ∉ q → ∃ p ∈ P, p.IsPrime ∧ q ≤ p ∧ f ∉ p)
    (h : ∀ q ∈ P, ∃ f : R, f ∉ q ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
      Q (pullback.snd s (spMap φ))) : Q s := by
  let S : Set R := {f | ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
      Q (pullback.snd s (spMap φ))}
  have hS : Ideal.span S = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨p, hp, -, hmp, -⟩ := hP m 1 hm.isPrime ((Ideal.ne_top_iff_one m).1 hm.ne_top)
    obtain ⟨f, hf, hfS⟩ := h p hp
    exact hf (hmp (hle (Ideal.subset_span hfS)))
  have hS' : Ideal.span (Set.range (fun f : S => (f : R))) = ⊤ := by
    rw [Subtype.range_coe]; exact hS
  refine IsZariskiLocalAtTarget.of_openCover (P := Q)
    (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of R) (fun f : S => (f : R)) hS').openCover ?_
  intro i
  exact (show S from i).2 (Localization.Away ((show S from i) : R)) (algebraMap R _)
    (IsLocalization.Away.algebraMap_isUnit _)

theorem smooth_and_geomConnected_of_veryDense : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (g : ℕ) (P : Set (Ideal R)), (∀ (q : Ideal R) (f : R), q.IsPrime → f ∉ q → ∃ p ∈ P, p.IsPrime ∧ q ≤ p ∧ f ∉ p) → IsProjOver s → Flat s → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K), RingHom.ker x = q ∧ SmoothOfRelativeDimension g (pullback.snd s (spMap x)) ∧ GeometricallyConnected (pullback.snd s (spMap x))) → SmoothOfRelativeDimension g s ∧ GeometricallyConnected s := by
  intro R _ _ Z s g P hP hproj hflat h
  have hsm : SmoothOfRelativeDimension g s := by
    have : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension.{0} g) := HasRingHomProperty.instIsZariskiLocalAtTarget _
    refine of_local_near_veryDense (@SmoothOfRelativeDimension.{0} g) R Z s P hP ?_
    intro q hq
    obtain ⟨K, _, x, hx, h1, -⟩ := h q hq
    obtain ⟨f, hf, H⟩ := GlobalTheory.T.exists_smoothOfRelDim_of_isUnit_proper_flat R Z s g K x (projProper R Z s hproj) hflat h1
    exact ⟨f, by rw [← hx]; exact hf, H⟩
  refine ⟨hsm, ?_⟩
  have : IsZariskiLocalAtTarget (@GeometricallyConnected.{0}) := by
    rw [GeometricallyConnected.eq_geometrically]; infer_instance
  refine of_local_near_veryDense (@GeometricallyConnected.{0}) R Z s P hP ?_
  intro q hq
  obtain ⟨K, _, x, hx, -, h2⟩ := h q hq
  obtain ⟨f, hf, H⟩ := GlobalTheory.T.geometricallyConnected_open_condition_smooth_projective R Z s K x hproj (SmoothOfRelativeDimension.smooth g s) h2
  exact ⟨f, by rw [← hx]; exact hf, H⟩

end GlobalTheory
