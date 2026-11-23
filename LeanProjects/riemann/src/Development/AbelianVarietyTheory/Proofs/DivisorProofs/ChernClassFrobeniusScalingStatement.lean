import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernClassFrobeniusScaling
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfHomPull
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_class_frobenius_scaling : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (P P' : Pres B) (g : Γ(B.X, ⊤)), IsRootOfP p g p → Kills g P.mod → IsFrob p P.mod P'.mod → (haveI := P.iso; Nonempty (GlobalTheory.Vert.Model.FlagPair (GlobalTheory.Vert.Model.GenIso.ofHom P.ψ) P.r)) → ∀ k : ℕ, P'.ck p k = ((p : ℚ) ^ k) • P.ck p k := by
  first | exact @GlobalTheory.FlagFrob.ck_frob_of_flagPair | exact GlobalTheory.FlagFrob.ck_frob_of_flagPair | (intros; apply GlobalTheory.FlagFrob.ck_frob_of_flagPair <;> assumption)
