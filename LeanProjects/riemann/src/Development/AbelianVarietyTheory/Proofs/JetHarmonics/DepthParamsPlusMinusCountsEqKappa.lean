import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlaceLabelBijectiveCardEqFStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem numOf_Dplus_Dminus : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ), InR D j → (numOf D L).Dplus j = ((∑ τ, ∑ i, (kaR Tp hK j).aP τ i : ℕ) : ℚ) ∧ (numOf D L).Dminus j = ((∑ τ, ∑ i, (kaR Tp hK j).aM τ i : ℕ) : ℚ) := by
  intro D L Pm Tp hK j hj
  have hb := (GlobalTheory.T.realPlaceLabel_bijective_card_eq_f D).1
  have h1 := hj.1
  have h2 := hj.2
  constructor
  · have e : (numOf D L).Dplus j =
        ∑ z : RPl D.R, ∑ i ∈ Finset.range (D.R.sigW j).1, DV.aPlusQ D j (plOf D z) i := rfl
    rw [e, hb.sum_comp (fun τ => ∑ i ∈ Finset.range (D.R.sigW j).1, DV.aPlusQ D j τ i)]
    push_cast
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← (hK j h1 h2 τ).1 i, ← kaWt_big D hK (even_nV Tp) j h1 h2 τ i, Int.cast_natCast]
    rfl
  · have e : (numOf D L).Dminus j =
        ∑ z : RPl D.R, ∑ i ∈ Finset.range (D.R.sigW j).2, DV.aMinusQ D j (plOf D z) i := rfl
    rw [e, hb.sum_comp (fun τ => ∑ i ∈ Finset.range (D.R.sigW j).2, DV.aMinusQ D j τ i)]
    push_cast
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_range, ← Equiv.sum_comp Fin.revPerm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 := kaWt_small D hK (even_nV Tp) j h1 h2 τ i
    have e2 := (hK j h1 h2 τ).2 (Fin.rev i)
    have e3 := congrArg (fun q : ℤ => (q : ℚ)) e1
    simp only [Int.cast_natCast, Int.cast_neg] at e3
    rw [e2, neg_neg] at e3
    exact e3.symm

end GlobalTheory.RunDepth
