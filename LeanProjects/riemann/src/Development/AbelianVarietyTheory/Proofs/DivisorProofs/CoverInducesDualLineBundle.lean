import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSectionLiftsMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLineBundleInducedArith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleMetricSetupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicDivisorInducedNeg
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LgOfSingleNegOneEqNegStatement
open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TwoLat
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwoLat

open GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4

theorem induces_lineAdl_neg : ∀ (D : D7) (O : Setup D), O.Core → ∀ (R : ℝ) (c : O.s.Comp) (V : Cover (O.var c))
    (st : ((D.host.E →+* ℂ) × ℕ) ⊕ ℕ) (L : HermLB V.p), V.Induces (lineAdl O R c st 1) L 1 →
    V.Induces (lineAdl O R c st (-1)) L.dual 1 := by
  intro D O hO R c V st L h
  obtain ⟨x, P, hC⟩ := hO
  have hex : expo O.S.Dw (Finsupp.single (ArIn.ind ∅, some R, st) (-1)) =
      -expo O.S.Dw (Finsupp.single (ArIn.ind ∅, some R, st) 1) := by
    rw [Finsupp.single_neg, GlobalTheory.CombInd.DualComb.expo_neg]
  have hpar : parOf (Finsupp.single (ArIn.ind ∅, some R, st) (-1 : ℤ)) =
      parOf (Finsupp.single (ArIn.ind ∅, some R, st) (1 : ℤ)) := by
    rw [Finsupp.single_neg, GlobalTheory.CombInd.DualComb.parOf_neg]
  refine V.induces_dual _ _ L ?_ rfl rfl ?_ ?_ h
  · show divOf _ (expo _ _) = -divOf _ (expo _ _)
    rw [hex, GlobalTheory.CombInd.DualComb.divOf_neg]
  · intro σ y f hf
    show (cxSt _).pn _ σ _ (O.met.hm c (parOf _) σ _) _ y * (cxSt _).pn _ σ _ (O.met.hm c (parOf _) σ _) _ y = 1
    rw [hC.hm_eq, hpar]
    show (cxSt _).pn _ σ _ ((O.Φ.C c).met (x.eigMetAt (embOf O.κ.e σ) _) _) _ y *
      (cxSt _).pn _ σ _ ((O.Φ.C c).met (x.eigMetAt (embOf O.κ.e σ) _) _) _ y = 1
    revert hf
    generalize expo O.S.Dw (Finsupp.single (ArIn.ind ∅, some R, st) (-1)) = n' at hex ⊢
    subst hex
    intro hf
    exact pn_met_mul_neg _ _ hf
  · intro v e y
    exact GlobalTheory.T.lgOf_single_neg_one_eq_neg (O.Φ.C c) (ArIn.ind ∅, some R, st) v e y

end GlobalTheory.TwoLat
