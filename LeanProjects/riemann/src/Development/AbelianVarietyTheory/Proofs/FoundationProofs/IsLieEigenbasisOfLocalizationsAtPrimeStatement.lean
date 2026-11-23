import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisOfLocalizationsAtPrime
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FibreIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLieEigenbasis_of_localizations_atPrime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (χ : 𝓞 E →+* R) (m : ℕ) (v : Fin m → (epsR R ⟶ t.G)), (∀ (p : Ideal R) [p.IsPrime], ∃ (t' : SAB H (Sp (Localization.AtPrime p))) (n : SABMap t' t (spMap (algebraMap R (Localization.AtPrime p)))) (v' : Fin m → (epsR (Localization.AtPrime p) ⟶ t'.G)), (∀ i, IsVecOver (algebraMap R (Localization.AtPrime p)) n.φ (v i) (v' i)) ∧ EigenvectorLieDegree.IsEigBasis t'.act ((algebraMap R (Localization.AtPrime p)).comp χ) v') → EigenvectorLieDegree.IsEigBasis t.act χ v := by
  first | exact @GlobalTheory.FlatRow.isEigBasis_of_local | exact GlobalTheory.FlatRow.isEigBasis_of_local | (intros; apply GlobalTheory.FlatRow.isEigBasis_of_local <;> assumption)
