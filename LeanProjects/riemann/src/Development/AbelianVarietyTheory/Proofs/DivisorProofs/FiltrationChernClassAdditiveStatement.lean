import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationChernClassAdditive
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_chern_class_additive : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (g : Γ(B.X, ⊤)), IsRootOfP p g p → ∀ (r : ℕ) (Qs : Fin (r + 1) → Pres B) (Rs : Fin r → Pres B), IsZero (Qs 0).mod → (∀ i, (Rs i).r = 1) → (∀ i, Kills g (Qs i).mod) → (∀ i, Kills g (Rs i).mod) → (∀ i : Fin r, IsExt (Qs i.castSucc).mod (Qs i.succ).mod (Rs i).mod) → ∃ (Ss : Fin (r + 1) → Pres B) (Rs' : Fin r → Pres B), IsZero (Ss 0).mod ∧ (∀ i, IsFrob p (Qs i).mod (Ss i).mod) ∧ (∀ i, IsFrob p (Rs i).mod (Rs' i).mod) ∧ ∀ i : Fin r, IsExt (Ss i.castSucc).mod (Ss i.succ).mod (Rs' i).mod := by
  first | exact @GlobalTheory.FrobFilt.exists_frob_filtration | exact GlobalTheory.FrobFilt.exists_frob_filtration | (intros; apply GlobalTheory.FrobFilt.exists_frob_filtration <;> assumption)
