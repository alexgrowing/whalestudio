import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateQuotient
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinatePolynomialRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem germ_mem_maximalIdeal_iff {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) (s : Γ(X, U)) :
    X.presheaf.germ U x hx s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ↔
      s ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  let instSt : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hx).hom.toAlgebra
  have instLoc : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal s

variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}

theorem exists_sections_span_eq_maximalIdeal_with_coords (hU : IsAffineOpen U)
    (c : EtaleChart p U m) (x : X) (hx : x ∈ U) (J₀ : Finset (Fin m))
    (hJ₀ : ∀ j ∈ J₀, X.presheaf.germ U x hx (c.coord j) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    ∃ (d : ℕ) (f : Fin d → Γ(X, U)),
      (∀ i, X.presheaf.germ U x hx (f i) ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ∧
      (∀ j ∈ J₀, ∃ i, f i = c.coord j) ∧
      Ideal.span (Set.range fun i => X.presheaf.germ U x hx (f i)) =
          IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
      (d : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x) := by
  let instAlg : Algebra (CoordPolynomialRing k m) Γ(X, U) := c.algebra
  have instEt : Algebra.Etale (CoordPolynomialRing k m) Γ(X, U) := c.algebra_etale hU
  let instSt : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hx).hom.toAlgebra
  have instLoc : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  have halg : ∀ t : Γ(X, U),
      algebraMap Γ(X, U) (X.presheaf.stalk x) t = X.presheaf.germ U x hx t := fun _ => rfl
  have hcoord : ∀ j : Fin m, etaleChartCoord k m Γ(X, U) j = c.coord j := by
    intro j
    show c.coordRingHom (MvPolynomial.X (ULift.up j : ULift.{u} (Fin m))) = c.coord j
    exact c.coordRingHom_X j
  have hq : ∀ j ∈ J₀, etaleChartCoord k m Γ(X, U) j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
    intro j hj
    rw [hcoord j]
    exact (germ_mem_maximalIdeal_iff hU x hx (c.coord j)).mp (hJ₀ j hj)
  obtain ⟨d, f, hf1, hf2, hf3, hf4⟩ :=
    exists_regularSystemOfParameters_containing_etaleChartCoords k m Γ(X, U)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal (X.presheaf.stalk x) J₀ hq
  refine ⟨d, f, ?_, ?_, ?_, hf4⟩
  · intro i
    exact (germ_mem_maximalIdeal_iff hU x hx (f i)).mpr (hf1 i)
  · intro j hj
    obtain ⟨i, hi⟩ := hf2 j hj
    exact ⟨i, by rw [hi, hcoord j]⟩
  · simpa only [halg] using hf3

theorem exists_isRegularParameterSystem_with_coords_of_mem_prime (hU : IsAffineOpen U)
    (c : EtaleChart p U m) (x : X) (hx : x ∈ U) (J₀ : Finset (Fin m))
    (hJ₀ : ∀ j ∈ J₀, c.coord j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :
    ∃ (n : ℕ) (f : Fin n → Γ(X, U)),
      (∀ j ∈ J₀, ∃ i, f i = c.coord j) ∧
      IsRegularParameterSystem (X.presheaf.stalk x) n
        (fun i => X.presheaf.germ U x hx (f i)) := by
  obtain ⟨d, f, -, h2, h3, h4⟩ :=
    exists_sections_span_eq_maximalIdeal_with_coords hU c x hx J₀
      (fun j hj => (germ_mem_maximalIdeal_iff hU x hx (c.coord j)).mpr (hJ₀ j hj))
  exact ⟨d, f, h2, h3, h4⟩

theorem exists_isRegularParameterSystem_with_coords_of_germ_mem
    (hU : IsAffineOpen U) (c : EtaleChart p U m) (x : X) (hx : x ∈ U) (J₀ : Finset (Fin m))
    (hJ₀ : ∀ j ∈ J₀, X.presheaf.germ U x hx (c.coord j) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    ∃ (n : ℕ) (f : Fin n → Γ(X, U)),
      (∀ j ∈ J₀, ∃ i, f i = c.coord j) ∧
      IsRegularParameterSystem (X.presheaf.stalk x) n
        (fun i => X.presheaf.germ U x hx (f i)) :=
  exists_isRegularParameterSystem_with_coords_of_mem_prime hU c x hx J₀
    (fun j hj => (germ_mem_maximalIdeal_iff hU x hx (c.coord j)).mp (hJ₀ j hj))

end FunctorialResolution.EmbeddedResolution
