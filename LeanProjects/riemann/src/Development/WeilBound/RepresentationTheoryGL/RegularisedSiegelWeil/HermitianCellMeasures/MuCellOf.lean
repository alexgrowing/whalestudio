import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.CellDefs

noncomputable section

open scoped Matrix NNReal ENNReal Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.Cell

theorem muCell_of (hR : Riesz) (hN : NullC) (hF : CellFormula) (hA : CellAlg) (hD : Decomp) (hW : FewC) (hS : SetC)
    (hT : TopC) : MuCell := by
  intro D p mu hmu nb hnb w hw
  refine ⟨∅, fun S _ e he lam hlam => ?_⟩
  obtain ⟨hG2, hGlc, hGsc, hH2, hHlc, hHsc, hHb⟩ := hT D p e
  haveI := hlam
  obtain ⟨h, hSet, hRho, hKh, hInv⟩ := hS D p mu hmu
  letI : MeasurableSpace (G D p ⧸ P D p) := borel _
  haveI : BorelSpace (G D p ⧸ P D p) := ⟨rfl⟩
  obtain ⟨ν, hν⟩ := hR (G D p) (P D p) h mu hSet
  obtain ⟨τ, hcell, -, hmm⟩ := hA D p nb hnb w hw S e he
  have hfew : Few (P D p) h mu (cell e) :=
    hW D p mu h nb hnb w hw (fun y => (hInv nb hnb w hw y).2) S e he
  have hnull : ν {q | rp q ∉ cell e} = 0 :=
    hN (G D p) (P D p) h mu hSet ν hν (cell e) hcell.isOpen
      (fun q hq x hx => (hcell.left q hq x hx).1) hfew
  have hdec : ∀ x ∈ cell e, ∃ q ∈ P D p, ∃ u ∈ KOff D p S, x = q * (w * nb (τ x).1) * u ∧
      ∀ z : hermS D p e, nb z.1 * u = u * nb z.1 :=
    fun x hx => hD D p nb hnb w hw S e he x hx (τ x) (hmm x hx)
  have hrel : ∀ (y : hermS D p e), ∀ x ∈ cell e,
      h (x * nb y.1) * h (w * nb (τ x).1) = h (w * nb (τ x + y).1) * h x := by
    intro y x hx
    obtain ⟨q, hq, u, hu, ex, hcomm⟩ := hdec x hx
    have hadd : nb (τ x + y).1 = nb (τ x).1 * nb y.1 := hcell.nbAdd (τ x) y
    have e0 : h (x * nb y.1) = h (q * (w * nb (τ x).1) * u * nb y.1) :=
      congrArg (fun z => h (z * nb y.1)) ex
    have e1 : q * (w * nb (τ x).1) * u * nb y.1 = q * (w * nb (τ x + y).1) * u := by
      rw [hadd]
      simp only [mul_assoc]
      rw [← hcomm y]
    have hx1 : h (x * nb y.1) = h (q * (w * nb (τ x + y).1)) := by
      rw [e0, e1, hKh S u hu]
    have hx2 : h x = h (q * (w * nb (τ x).1)) := (congrArg h ex).trans (hKh S u hu _)
    rw [hx1, hx2]
    exact hSet.law q hq _ _
  obtain ⟨c, hc⟩ := hF (G D p) (P D p) h mu hSet ν hν (hermS D p e) lam (cell e) τ w
    (fun y => nb y.1) hcell (fun y => (hInv nb hnb w hw y.1).1) hrel hnull
  have hOn : ∀ f, IsRho f → (∀ u ∈ KOff D p S, ∀ g, f (g * u) = f g) →
      OnCell h (cell e) τ w (fun y => nb y.1) f := by
    intro f hf hfK x hx
    obtain ⟨q, hq, u, hu, ex, -⟩ := hdec x hx
    have hsec := (hRho f).mp hf
    have hf1 : f x = f (q * (w * nb (τ x).1)) := (congrArg f ex).trans (hfK u hu _)
    have hh1 : h x = h (q * (w * nb (τ x).1)) := (congrArg h ex).trans (hKh S u hu _)
    show f x * h (w * nb (τ x).1) = f (w * nb (τ x).1) * h x
    rw [hf1, hh1]
    exact hsec.2 q hq _
  by_cases hc0 : c = 0
  · left
    intro f hf hfK
    have hmu' := (hc f ((hRho f).mp hf) (hOn f hf hfK)).2
    rw [hmu', hc0, zero_smul, integral_zero_measure]
  · right
    refine ⟨c, NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc0), fun f hf hfK => ?_⟩
    obtain ⟨hi, heq⟩ := hc f ((hRho f).mp hf) (hOn f hf hfK)
    refine ⟨?_, ?_⟩
    · have hi' := hi.smul_measure_nnreal (c := c⁻¹)
      rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at hi'
    · rw [heq, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

end PositivityTheory.Rg.Rsw.Cell

end
