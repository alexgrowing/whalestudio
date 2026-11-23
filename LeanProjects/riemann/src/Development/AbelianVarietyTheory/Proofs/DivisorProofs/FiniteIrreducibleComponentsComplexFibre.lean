import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapCompSpMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

namespace GlobalTheory.HorComp

theorem isNoetherian_cxFib {k F : Type} [CommRing k] [CommRing F] (β : k →+* F) {Y : Scheme.{0}} {q : Y ⟶ Sp k}
    (σ : F →+* ℂ) (hq : IsProjOver q) : IsNoetherian (cxFib β q σ) := by
  obtain ⟨N, i, hi, rfl⟩ := hq
  have : IsProper (PSpace.str k N) := isProper_str k N
  have hp : IsProper (pullback.snd (i ≫ PSpace.str k N) (spMap (σ.comp β))) := inferInstance
  have h1 : IsLocallyNoetherian (cxFib β (i ≫ PSpace.str k N) σ) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd (i ≫ PSpace.str k N) (spMap (σ.comp β)))
  have h2 : CompactSpace (cxFib β (i ≫ PSpace.str k N) σ) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd (i ≫ PSpace.str k N) (spMap (σ.comp β)))
  exact {}

theorem finite_irreducibleComponents_cxFib : ∀ (k F : Type) [CommRing k] [CommRing F] (β : k →+* F) (Y : Scheme.{0})
    (q : Y ⟶ Sp k) (σ : F →+* ℂ) (n : ℕ), IsArithVar q n → (irreducibleComponents (cxFib β q σ)).Finite := by
  intro k F _ _ β Y q σ n h
  have := isNoetherian_cxFib β σ h.isProjOver
  exact NoetherianSpace.finite_irreducibleComponents

end GlobalTheory.HorComp
