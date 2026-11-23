import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

namespace GlobalTheory.Frames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem exists_factor_openImmersion {X : Scheme.{0}} {R S : Type} [CommRing R] [CommRing S] (j : Sp R ⟶ X)
    [IsOpenImmersion j] (x : Sp S ⟶ X) (p : Sp S) (hp : x p ∈ Set.range j) :
    ∃ g : S, g ∉ p.asIdeal ∧ ∀ (T : Type) [CommRing T] (lam : S →+* T), IsUnit (lam g) →
      ∃ ψ : R →+* T, spMap lam ≫ x = spMap ψ ≫ j := by
  have hU : IsOpen ((fun q : PrimeSpectrum S => x q) ⁻¹' Set.range j) :=
    j.isOpenEmbedding.isOpen_range.preimage x.continuous
  obtain ⟨_, ⟨g, rfl⟩, hpg, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := p) hp hU
  refine ⟨g, hpg, fun T _ lam hu => ?_⟩
  have hr : Set.range (spMap lam ≫ x) ⊆ Set.range j := by
    rintro _ ⟨q, rfl⟩
    have hq : PrimeSpectrum.comap lam q ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) := by
      intro h
      exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
    exact hsub hq
  refine ⟨(Spec.preimage (IsOpenImmersion.lift j (spMap lam ≫ x) hr)).hom, ?_⟩
  simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem openChart_factor_near_prime :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [Algebra c.F R] (j : Sp R ⟶ Xo.XF c) (y₀ : FrPt Xo c R), OpenChart j y₀ → ∀ (S : Type) [CommRing S] [Algebra c.F S] (xF : Sp S ⟶ Xo.XF c), xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S) → ∀ p : Sp S, xF p ∈ Set.range j → ∃ g : S, g ∉ p.asIdeal ∧ ∀ (T : Type) [CommRing T] [Algebra c.F T] (lam : S →ₐ[c.F] T), IsUnit (lam g) → ∃ ψ : R →ₐ[c.F] T, spMap lam.toRingHom ≫ xF = spMap ψ.toRingHom ≫ j := by
  intro E _ _ _ H Dw l Xo c R _ _ j y₀ hj S _ _ xF hx p hp
  haveI := hj.1
  obtain ⟨g, hg, h⟩ := exists_factor_openImmersion j xF p hp
  refine ⟨g, hg, fun T _ _ lam hu => ?_⟩
  obtain ⟨ψ, hψ⟩ := h T lam.toRingHom hu
  have h2 := congrArg (· ≫ pullback.snd _ _) hψ
  simp only [Category.assoc] at h2
  rw [hx, hj.2.2, ← Spec.map_comp, ← Spec.map_comp] at h2
  have h3 := congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
  refine ⟨{ ψ with commutes' := fun a => ?_ }, hψ⟩
  have h4 := RingHom.congr_fun h3 a
  exact h4.symm.trans (lam.commutes a)

end GlobalTheory.Frames
