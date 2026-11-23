import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAwayProjectiveFormsThroughPointsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsProjCoordRepresentationHomogeneousIdealFlaStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoOfProjectiveCoordinateRepresentationStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinatesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

namespace GlobalTheory.ZM.NearCut

open MvPolynomial in

theorem homogeneousComponent_mem_vanIdeal {R σ Hh : Type} [CommRing R] (d : ℕ) (p : Hh → σ → R)
    (F : MvPolynomial σ R) (hF : F ∈ vanIdeal d p) (e : ℕ) : homogeneousComponent e F ∈ vanIdeal d p := by
  classical
  letI := (MvPolynomial.gradedAlgebra : GradedAlgebra (homogeneousSubmodule σ R))
  have h : (vanIdeal d p).IsHomogeneous (homogeneousSubmodule σ R) :=
    Ideal.homogeneous_span _ _ fun x hx => ⟨d, hx.1⟩
  have := h e hF
  rwa [show ((DirectSum.decompose (homogeneousSubmodule σ R) F e : homogeneousSubmodule σ R e) : MvPolynomial σ R)
    = homogeneousComponent e F from MvPolynomial.decomposition.decompose'_apply F e] at this

open MvPolynomial in

theorem eval₂_eq_zero_of_forms_le {K σ : Type} [CommRing K] {I J : Ideal (MvPolynomial σ K)} {d : ℕ}
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I)
    (hle : ∀ e ≥ d, ∀ F : MvPolynomial σ K, F.IsHomogeneous e → F ∈ I → F ∈ J)
    {T : Type} [CommRing T] (β : K →+* T) (v : σ → T) (hv : Ideal.span (Set.range v) = ⊤)
    (hJ : ∀ F ∈ J, eval₂ β v F = 0) : ∀ F ∈ I, eval₂ β v F = 0 := by
  intro F hF
  have key : ∀ e, eval₂ β v (homogeneousComponent e F) = 0 := by
    intro e
    have h1 : ∀ i, v i ^ d * eval₂ β v (homogeneousComponent e F) = 0 := by
      intro i
      have := hJ _ (hle (d + e) (by omega) (X i ^ d * homogeneousComponent e F)
        ((isHomogeneous_X_pow i d).mul (homogeneousComponent_isHomogeneous e F)) (I.mul_mem_left _ (hI F hF e)))
      rwa [eval₂_mul, eval₂_pow, eval₂_X] at this
    have h2 := Ideal.span_pow_eq_top _ hv d
    have h3 : Ideal.span ((fun x => x ^ d) '' Set.range v) ≤
        LinearMap.ker (LinearMap.toSpanSingleton T T (eval₂ β v (homogeneousComponent e F))) := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact h1 i
    rw [h2] at h3
    simpa using h3 (Submodule.mem_top (x := (1 : T)))
  rw [← sum_homogeneousComponent F, eval₂_sum]
  exact Finset.sum_eq_zero fun e _ => key e

theorem exists_away_flat_projRep : ∀ (R σ Hh : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] [Finite σ] [Finite Hh] (p : Hh → σ → R) (Q : Polynomial ℚ) (d : ℕ) (P : Set (Ideal R)), DenseP P → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K) (I : Ideal (MvPolynomial σ K)), RingHom.ker x = q ∧ CutBy I Q d (fun h i => x (p h i))) → ∀ q₀ ∈ P, ∃ f : R, f ∉ q₀ ∧ ∃ (Z : Over (Sp (Localization.Away f))) (M : LB Z.left) (th : σ → M.Sec), ProjRep (vanIdeal d (fun h i => loc f (p h i))) Z.hom M th ∧ Flat Z.hom ∧ ∀ (K : Type) [Field K] (x : Localization.Away f →+* K) (I : Ideal (MvPolynomial σ K)) (X : Scheme.{0}) (s : X ⟶ Sp K) (M' : LB X) (th' : σ → M'.Sec), (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → CutBy I Q d (fun h i => x (loc f (p h i))) → ProjRep I s M' th' → ∃ φ : X ⟶ Z.left, IsPullback φ s Z.hom (spMap x) ∧ LBIso M' (M.pull φ) ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ X) (w : σ → T), SecCoord M' th' y w ↔ SecCoord M th (y ≫ φ) w := by
  intro R σ Hh _ _ _ _ _ p Q d P hP hcutP q₀ hq₀
  obtain ⟨f, hf, hproj, hmap⟩ := GlobalTheory.T.exists_away_projective_forms_through_points R σ Hh p Q d P hP hcutP q₀ hq₀
  obtain ⟨Z, s, M, th, -, hrep, -, hflat⟩ := GlobalTheory.T.exists_projCoordRepresentation_homogeneousIdeal_flat (Localization.Away f) σ
    (vanIdeal d (fun h i => loc f (p h i))) d (homogeneousComponent_mem_vanIdeal d _)
  refine ⟨f, hf, Over.mk s, M, th, hrep, hflat fun e he => by have := hproj e he; infer_instance, ?_⟩
  intro K _ x I X s' M' th' hI hcut hrep'
  have hpb := IsPullback.of_hasPullback s (spMap x)
  obtain ⟨th₁, hrep₁, hc₁⟩ := GlobalTheory.T.projective_representation_pullback_coordinates _ K σ x _ Z _ s _ _ M th hrep hpb
  rw [hmap K x] at hrep₁
  obtain ⟨e, he, hiso, hc⟩ := GlobalTheory.T.exists_iso_of_projectiveCoordinateRepresentation K σ I _ X _ s' _ M' _ th' th₁ hrep' hrep₁ fun T _ β v hv =>
    ⟨eval₂_eq_zero_of_forms_le (homogeneousComponent_mem_vanIdeal d _) (fun e he F hF h => ((hcut e he).2 F hF).2 h) β v hv,
      eval₂_eq_zero_of_forms_le hI (fun e he F hF h => ((hcut e he).2 F hF).1 h) β v hv⟩
  refine ⟨e.hom ≫ pullback.fst s (spMap x), ?_, ?_, fun T _ y w => ?_⟩
  · have h0 : IsPullback e.hom s' (pullback.snd s (spMap x)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩
    simpa using h0.paste_horiz hpb
  · exact LBIso.trans hrep'.1 (pull_isLB hrep₁.1 _) (pull_isLB hrep.1 _) hiso
      (LBIso.chartPull (chartPullPull _ e.hom e.hom rfl) (chartPullSame M _ _ _ e.hom fun _ => rfl)
        ⟨_, idIso_isGen hrep₁.1⟩)
  · rw [hc T y w, hc₁ T _ w, Category.assoc]

end GlobalTheory.ZM.NearCut
