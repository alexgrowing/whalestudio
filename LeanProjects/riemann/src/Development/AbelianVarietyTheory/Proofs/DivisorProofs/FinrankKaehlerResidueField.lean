import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineOpenFinitePresentationStalkKaehlerFr
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LogPair
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.SmoothStalk

theorem finrank_baseChange_kaehler_of_formallyEtale {k B A K : Type} [Field k] [CommRing B] [CommRing A] [Field K]
    [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A] [Algebra A K] [Algebra B K]
    [IsScalarTower B A K] [Algebra.FormallyEtale B A] [Module.Free A Ω[A⁄k]] [Module.Finite A Ω[A⁄k]] [Nontrivial A] :
    Module.finrank K (K ⊗[B] Ω[B⁄k]) = Module.finrank A Ω[A⁄k] := by
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale k B A
  have hbc2 := TensorProduct.isBaseChange A Ω[A⁄k] K
  have hcomp := hbc.comp hbc2
  rw [hcomp.equiv.finrank_eq, Module.finrank_baseChange]

theorem finrank_residue_kaehler : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d f] (U : X.Opens) (x : X) (hxU : x ∈ U), IsAffineOpen U → letI : Algebra k Γ(X, U) := (cstOn f U).toAlgebra; letI : Algebra Γ(X, U) (IsLocalRing.ResidueField (X.presheaf.stalk x)) := ((IsLocalRing.residue (X.presheaf.stalk x)).comp (X.presheaf.germ U x hxU).hom).toAlgebra; Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x)) (IsLocalRing.ResidueField (X.presheaf.stalk x) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄k]) = d := by
  intro k _ X f d _ U x hxU hU
  letI iB : Algebra k Γ(X, U) := (cstOn f U).toAlgebra
  letI iBK : Algebra Γ(X, U) (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    ((IsLocalRing.residue (X.presheaf.stalk x)).comp (X.presheaf.germ U x hxU).hom).toAlgebra
  letI iBA : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  letI iA : Algebra k (X.presheaf.stalk x) := ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)).toAlgebra
  obtain ⟨-, hfree, hfin, hrank⟩ := GlobalTheory.SmoothStalk.smooth_stalk k X f d ⟨U, hU⟩ x hxU
  haveI : Module.Free (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] := hfree
  haveI : Module.Finite (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] := hfin
  have hrank' : Module.finrank (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] = d := hrank
  haveI : IsScalarTower k Γ(X, U) (X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq' rfl
  haveI hsc : @IsScalarTower Γ(X, U) (X.presheaf.stalk x) (IsLocalRing.ResidueField (X.presheaf.stalk x)) _ _
      iBK.toSMul := IsScalarTower.of_algebraMap_eq' rfl
  haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  haveI : Algebra.FormallyEtale Γ(X, U) (X.presheaf.stalk x) :=
    Algebra.FormallyEtale.of_isLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  rw [← hrank']
  exact @finrank_baseChange_kaehler_of_formallyEtale k Γ(X, U) (X.presheaf.stalk x)
    (IsLocalRing.ResidueField (X.presheaf.stalk x)) _ _ _ _ iB iA iBA _ _ iBK hsc _ _ _ _

end GlobalTheory.SmoothStalk
