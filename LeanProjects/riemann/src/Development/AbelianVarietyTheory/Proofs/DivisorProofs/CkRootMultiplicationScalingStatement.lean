import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkRootMultiplicationScaling
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ck_root_multiplication_scaling : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (P : Pres B) (g : Γ(B.X, ⊤)) (a : ℕ) (e : P.E' ≅ P.E), IsRootOfP p g a → P.ψ = e.hom ≫ smulHom P.E g → ∀ k : ℕ, (a : ℚ) • P.ck p k = ckP p (GlobalTheory.Vert.Model.GenIso.smul P.E (p : O) (GlobalTheory.Vert.natCast_ne_zero O p)) P.r k ∧ ∀ (fl : GlobalTheory.Vert.Flag P.E P.r) (Q : PicSym B.X), ckP p (GlobalTheory.Vert.Model.GenIso.smul P.E (p : O) (GlobalTheory.Vert.natCast_ne_zero O p)) P.r k Q = k * (B.toITh p).capDeg (B.toITh p).divP ((∑ i, c1 (fl.root i) (fl.isLB_root i) ^ (k - 1)) * Q) := by
  first | exact @GlobalTheory.CkSMulRoot.ck_smul_root | exact GlobalTheory.CkSMulRoot.ck_smul_root | (intros; apply GlobalTheory.CkSMulRoot.ck_smul_root <;> assumption)
