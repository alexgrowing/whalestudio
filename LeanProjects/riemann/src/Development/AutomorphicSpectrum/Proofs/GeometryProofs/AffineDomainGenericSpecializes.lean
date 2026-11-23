import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFrames

theorem mem_prime_germ_eq_zero {X : Scheme.{0}} {A : X.Opens} (hA : IsAffineOpen A) (x : A)
    (hF : IsField (X.presheaf.stalk x.1)) (f : Γ(X, A)) (hf : f ∈ (hA.primeIdealOf x).asIdeal) :
    X.presheaf.germ A x.1 x.2 f = 0 := by
  have hl := hA.isLocalization_stalk x
  have h1 : algebraMap Γ(X, A) (X.presheaf.stalk x.1) f ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x.1) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk x.1)
      (hA.primeIdealOf x).asIdeal f).2 hf
  have h2 : ¬ IsUnit (algebraMap Γ(X, A) (X.presheaf.stalk x.1) f) := h1
  by_contra h0
  exact h2 (by
    let _ := hF.toField
    exact IsUnit.mk0 _ h0)

theorem germ_injective {X : Scheme.{0}} {A : X.Opens} (hA : IsAffineOpen A) [IsDomain Γ(X, A)] (x : A) :
    Function.Injective (X.presheaf.germ A x.1 x.2) := by
  have hl := hA.isLocalization_stalk x
  exact IsLocalization.injective (X.presheaf.stalk x.1)
    (M := (hA.primeIdealOf x).asIdeal.primeCompl)
    ((hA.primeIdealOf x).asIdeal.primeCompl_le_nonZeroDivisors)

theorem genPt_specializes_of_isDomain : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (A : X.Opens) (hA : IsAffineOpen A) (p : Cpt ξ), IsCptGen ξ → IsDomain Γ(X, A) → p.1 ∈ A → ∀ z ∈ A, genPt ξ ⤳ z := by
  intro X Ω _ ξ A hA p hgen hdom hp z hz
  have hx : genPt ξ ∈ A := p.2.mem_open A.2 hp
  let x : A := ⟨genPt ξ, hx⟩
  let q : A := ⟨p.1, hp⟩
  have hF : IsField (X.presheaf.stalk x.1) :=
    MulEquiv.isField (Field.toIsField Ω) (RingEquiv.ofBijective _ hgen.bij).toMulEquiv
  have hbot : (hA.primeIdealOf x).asIdeal = ⊥ := by
    refine le_antisymm (fun f hf => ?_) bot_le
    have h0 := mem_prime_germ_eq_zero hA x hF f hf
    have h1 : X.presheaf.germ A p.1 hp f = 0 := by
      apply hgen.inj p
      have h2 : X.presheaf.stalkSpecializes p.2 (X.presheaf.germ A p.1 hp f) =
          X.presheaf.germ A (genPt ξ) hx f := by
        exact congr($(X.presheaf.germ_stalkSpecializes hp p.2).hom f)
      rw [map_zero]
      change (Scheme.stalkClosedPointTo ξ).hom
        (X.presheaf.stalkSpecializes p.2 (X.presheaf.germ A p.1 hp f)) = 0
      rw [h2]
      have h3 : X.presheaf.germ A (genPt ξ) hx f = 0 := h0
      rw [h3]
      exact map_zero (Scheme.stalkClosedPointTo ξ).hom
    exact germ_injective hA q (h1.trans (map_zero _).symm)
  obtain ⟨t, rfl⟩ : z ∈ Set.range hA.fromSpec := by rwa [hA.range_fromSpec]
  have hs : hA.primeIdealOf x ⤳ t := by
    refine (PrimeSpectrum.le_iff_specializes (hA.primeIdealOf x) t).1 ?_
    change (hA.primeIdealOf x).asIdeal ≤ _
    rw [hbot]
    exact bot_le
  have := hs.map hA.fromSpec.continuous
  rwa [hA.fromSpec_primeIdealOf] at this

end GlobalTheory.CompanionTheory.Ar.LocFrames
