import Formalism.HermitianCurvature.CompositeFormulaOfDensities
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateSplitAssocMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HerClassesOfPartsC

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

theorem sfinite_of_isHaarOn {k r : ℕ} (U : Set (B.Mat k r)) (μ : Measure (Mt k r)) (h : B.IsHaarOn U μ) :
    SFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

theorem herAnalyticCOfE : HerAnalyticCOfE := by
  intro hE Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ'
  obtain ⟨hAdj, hSD, hFI, hMeas⟩ := hE Wp Wq S P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ'
  haveI : SFinite μ := sfinite_of_isHaarOn _ μ hD.2.1
  have hTI := topIdentFromParts (S := S) P z z' π π' X μ L st (herK S P z z' π π' L st l0 D) l0 hD
    Formalism.FourierDecayAlt.P.frame_of_admissible_word ofWordRR hAdj
  have hXK := xKappaOfNF Formalism.FourierDecayAlt.P.normal_form_actual kappaFibrePos Wp Wq P z z' π π' X μ L st l0 hD
  have hTD := topDensNonnegOfKappa Wp Wq S P z z' π π' X μ L st l0 (herK S P z z' π π' L st l0 D) hD hl1 hl2 hXK
  exact ⟨hAdj, hSD, hFI, integral_formula_of_steps Wp Wq S P z z' π π' μ L st l0 _ hTI hTD herK_sliceIn hSD hMeas⟩

theorem thmPActualOfE (hZS : NF.ActualZetaSmooth) (hE : HerAnalyticEAll) : ThmPActual :=
  thmPActualOfZ hZS (herAnalyticCOfE hE)

theorem herAnalyticEOfF (hM : TopDensMeasAll) (hF : HerAnalyticFAll) : HerAnalyticEAll := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ'
  obtain ⟨hAdj, hSD, hFI⟩ := hF Wp Wq S P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ'
  exact ⟨hAdj, hSD, hFI, hM Wp Wq S P z z' π π' μ L st _⟩

theorem thmPActualOfCoreMZ (hZS : NF.ActualZetaSmooth) (hM : TopDensMeasAll) (hF : HerAnalyticFAll) : ThmPActual :=
  thmPActualOfE hZS (herAnalyticEOfF hM hF)

end Formalism.FourierDecayAlt.P5
