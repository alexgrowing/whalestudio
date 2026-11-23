import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenImmersionGenericFibre
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem isOpenImmersion_dense_genericFibre_normalization : ∀ (o F : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field F] [CharZero F] (b : o →+* F) (n : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp F) (f : X ⟶ PSpace o n) [QuasiCompact f] [QuasiSeparated f], Function.Injective b → (∀ x : F, ∃ a d : o, b d ≠ 0 ∧ x * b d = b a) → Geo.Tor.IsNormalScheme X → IsSeparated s → LocallyOfFiniteType s → QuasiCompact s → f ≫ PSpace.str o n = s ≫ spMap b → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), Set.Finite {y : Sp K ⟶ X | y ≫ s = x ≫ s ∧ y ≫ f = x ≫ f}) → ∀ iF : X ⟶ pullback (f.fromNormalization ≫ PSpace.str o n) (spMap b), iF ≫ pullback.fst _ _ = f.toNormalization → iF ≫ pullback.snd _ _ = s → IsOpenImmersion iF ∧ Dense (Set.range iF) := by
  intro o F _ _ _ _ _ _ b n X s f _ _ hb hfrac hN _ _ _ hfs hfib iF h1 h2
  letI : Algebra o F := b.toAlgebra
  haveI : FaithfulSMul o F := (faithfulSMul_iff_algebraMap_injective _ _).mpr hb
  haveI : IsFractionRing o F := IsFractionRing.of_field o F fun x => by
    obtain ⟨a, d, hd, e⟩ := hfrac x
    exact ⟨a, d, (eq_div_iff hd).mpr e⟩
  haveI : GlobalTheory.IsNormalScheme X := GlobalTheory.IsNormalScheme.of_pred hN
  haveI : IsReduced X := inferInstance
  obtain ⟨-, i₀, hoi, hd, hsnd, hfst⟩ :=
    GlobalTheory.SecCompact.exists_openImmersion_genericFibre F o n X s f hfs hfib
  have e : iF = i₀ := by
    apply pullback.hom_ext
    · rw [h1, hfst]
    · rw [h2, hsnd]
  subst e
  exact ⟨hoi, hd⟩

end GlobalTheory.UMin
