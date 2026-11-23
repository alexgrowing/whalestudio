import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIntegralAdeleIffBothComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceMemLatticeCompletionIffPartsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceWPartFrameColumnMultipleMemIffStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjPartLineMultipleMemIffStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittHyperbolicConjPairingEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselNormalFrameIsotropicColumnsPairingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiNormalFrameIsotropicColumnsPairingStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColsBFSplit

theorem xi_unit {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (hU : q.UnitAA) : valuation k ((ofSplit q).xi) = 1 := by
  have hpe : q.pr q.e = 1 := by
    have h := q.pr_sec 1
    rwa [show q.sec 1 = q.e by simpa using q.sec_pr 1] at h
  have hpce : q.pr (cA D q.e) = 0 := by
    have h : q.pr (q.e * cA D q.e) = 0 := by rw [q.split.2.1, map_zero]
    rwa [map_mul, hpe, one_mul] at h
  have heI := GlobalTheory.FinPl.LatIndHalf.e_mem_idAt q
  have heInt : q.e ∈ GlobalTheory.FinPl.intAt D (· = q.v) :=
    (GlobalTheory.T.splitPlace_integralAdele_iff_both_components D k q q.e heI).2 ⟨by rw [hpe]; exact one_mem _, by rw [hpce]; exact zero_mem _⟩
  obtain ⟨h1, h2⟩ := hU.1 q.e heInt
  have a1 := ((GlobalTheory.T.splitPlace_integralAdele_iff_both_components D k q _ h1.1).1 h1).1
  have a2 := ((GlobalTheory.T.splitPlace_integralAdele_iff_both_components D k q _ h2.1).1 h2).1
  rw [map_mul, hpe, mul_one] at a1 a2
  have hne : q.pr (incA D D.host.xi0) ≠ 0 := by
    intro h0
    have : q.pr (incA D D.host.xi0⁻¹) * q.pr (incA D D.host.xi0) = 1 := by
      rw [← map_mul, ← map_mul, inv_mul_cancel₀ (GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero (D := D)), map_one, map_one]
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  have hinv : q.pr (incA D D.host.xi0⁻¹) = (q.pr (incA D D.host.xi0))⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, ← map_mul, inv_mul_cancel₀ (GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero (D := D)), map_one, map_one]
  rw [hinv] at a2
  have b1 := (Valuation.mem_integer_iff _ _).1 a1
  have b2 := (Valuation.mem_integer_iff _ _).1 a2
  rw [map_inv₀] at b2
  change valuation k (q.pr (incA D D.host.xi0)) = 1
  have hv0 : valuation k (q.pr (incA D D.host.xi0)) ≠ 0 := by simpa using hne
  exact le_antisymm b1 ((inv_le_one₀ (zero_lt_iff.2 hv0)).1 b2)

theorem line_crit {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {S : HSp D} {L : GlobalTheory.FinPl.Lat S} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : Frame k S.rank Y) (u u' : Fin S.rank → D.host.E) (m₀ m₁ : Y) (c₀ c₁ : k) (hL : IsSelfDualC S L)
    (hI : IntIn q S F L) (h0 : valuation k c₀ = 1) (h1 : valuation k c₁ = 1)
    (hc0 : ∀ r, F.β r m₀ = c₀ * (ofSplit q).pr (u r)) (hc1 : ∀ r, F.β r m₁ = c₁ * (ofSplit q).pr (u' r))
    (hd : ∑ r, ∑ r', star (u r) * S.gram r r' * u' r' = 1)
    (hp : ∀ m, m ≠ m₁ → ∑ r, ∑ r', (ofSplit q).pr (star (u r)) * (ofSplit q).pr (S.gram r r') * F.β r' m = 0)
    (a : AE D) (ha : a ∈ GlobalTheory.FinPl.idAt D (· = q.v)) :
    (fun r => a * incA D (u r)) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ a ∈ GlobalTheory.FinPl.intAt D (· = q.v) := by
  rw [GlobalTheory.T.splitPlace_mem_latticeCompletion_iff_parts D k q S L _ (fun r => Ideal.mul_mem_right _ _ ha), GlobalTheory.T.splitPlace_wPart_frameColumnMultiple_mem_iff D k q S L Y F u m₀ c₀ hI h0 hc0 a,
    GlobalTheory.T.splitPlace_conjPart_lineMultiple_mem_iff D k q S L Y F u u' m₁ c₁ hL hI h1 hc1 hd hp a, GlobalTheory.T.splitPlace_integralAdele_iff_both_components D k q a ha]

end GlobalTheory.ColsBFSplit

end
