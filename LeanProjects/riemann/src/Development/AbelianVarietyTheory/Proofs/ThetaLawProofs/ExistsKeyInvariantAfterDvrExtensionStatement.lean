import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInvariantAfterDvrExtension
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_keyInvariant_after_dvr_extension : Out.Laws → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (r : O →+* Ω) (x : KeyIn O) (xk : KeyIn Ω) φ w (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (d : ℕ) (hg : xk.P.g = x.P.g) (s : Fin x.P.g → RR x n) (sk : Fin xk.P.g → RR xk n) (zk : Fin d → Pt xk) (chk : Fin d → xk.P.L.ι), RingHom.ker r = IsLocalRing.maximalIdeal O → admitted x.P.g n l l' al → IsUnit ((degProd x.P.g n l l' : ℕ) : O) → KeyVia xk x r φ w → (∀ i, SecVia xk x φ w (sk i) (s (i.cast hg))) → EtZ xk sk zk chk → ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (j : O →+* O') (r' : O' →+* Ω) (x' : KeyIn O') (φ' : _) (w' : _) (hg' : x'.P.g = x.P.g) (s' : Fin x'.P.g → RR x' n) (u : O'ˣ), Function.Injective j ∧ IsLocalHom j ∧ r'.comp j = r ∧ KeyVia x' x j φ' w' ∧ (∀ i, SecVia x' x φ' w' (s' i) (s (i.cast hg'))) ∧ KaVal x' n l l' al s' u := by
  first | exact @GlobalTheory.KaLift.exists_kaVal_extension | exact GlobalTheory.KaLift.exists_kaVal_extension | (intros; apply GlobalTheory.KaLift.exists_kaVal_extension <;> assumption)
