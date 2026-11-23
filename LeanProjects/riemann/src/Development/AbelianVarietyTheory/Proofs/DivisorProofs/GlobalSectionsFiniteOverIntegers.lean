import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdEqZeroOfUnderEqBot
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArithmeticVarietyDimZeroFinite
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

namespace GlobalTheory.GlobalFunFinite

theorem moduleFinite_int : ∀ (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) (p : X ⟶ Sp (𝓞 F)),
    IsArithVar (spMap (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤)) 0 → Module.Finite ℤ Γ(X, ⊤) := by
  intro F _ _ X p hX
  have hq : IsFinite (spMap (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤)) := GlobalTheory.ArithCurveFinite.isFinite _ _ _ hX
  have hz : IsFinite (spMap (Int.castRingHom (𝓞 F))) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  have hf : IsFinite (spMap (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤) ≫ spMap (Int.castRingHom (𝓞 F))) := inferInstance
  rw [← Spec.map_preimage (spMap (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤) ≫ _), IsFinite.SpecMap_iff,
    RingHom.ext_int (Spec.preimage (spMap (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤) ≫ spMap (Int.castRingHom (𝓞 F)))).hom
      (algebraMap ℤ Γ(X, ⊤)), RingHom.finite_algebraMap] at hf
  exact hf

end GlobalTheory.GlobalFunFinite
