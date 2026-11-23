import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecHomExtOfLocalizationsAtAllPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSpMapEv
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_hom_ext_of_localizations_at_all_primes : ∀ (S : Type) [CommRing S] (W : Scheme.{0}) (z z' : Sp S ⟶ W), (∀ q : PrimeSpectrum S, spMap (algebraMap S (Localization.AtPrime q.asIdeal)) ≫ z = spMap (algebraMap S (Localization.AtPrime q.asIdeal)) ≫ z') → z = z' := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.hom_ext_of_localization_atPrime | exact GlobalTheory.FlagMod.FieldFlag.hom_ext_of_localization_atPrime | (intros; apply GlobalTheory.FlagMod.FieldFlag.hom_ext_of_localization_atPrime <;> assumption)
