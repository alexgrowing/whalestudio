import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresentationFlagFiltrationExists
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.presentation_flag_filtration_exists : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (P : Pres B) (g : Γ(B.X, ⊤)), Kills g P.mod → (haveI := P.iso; Nonempty (GlobalTheory.Vert.Model.FlagPair (GlobalTheory.Vert.Model.GenIso.ofHom P.ψ) P.r)) → ∃ (Qs : Fin (P.r + 1) → Pres B) (Rs : Fin P.r → Pres B), IsZero (Qs 0).mod ∧ Nonempty ((Qs (Fin.last P.r)).mod ≅ P.mod) ∧ (∀ i, (Rs i).r = 1) ∧ (∀ i, Kills g (Qs i).mod) ∧ (∀ i, Kills g (Rs i).mod) ∧ ∀ i : Fin P.r, IsExt (Qs i.castSucc).mod (Qs i.succ).mod (Rs i).mod := by
  first | exact @GlobalTheory.MixedLocalChains.FlagFilt.exists_filtration | exact GlobalTheory.MixedLocalChains.FlagFilt.exists_filtration | (intros; apply GlobalTheory.MixedLocalChains.FlagFilt.exists_filtration <;> assumption)
