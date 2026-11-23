import Mathlib
import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KSchur
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KinstSecondCountable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.IntegrableOfContinuousCompact
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef

noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 PositivityTheory.RgFd

variable {n : ℕ}

theorem cont_triple {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] [Group B]
    [IsTopologicalGroup B] (F : A × B → ℝ) (c : B → ℝ) (hF : Continuous F) (hc : Continuous c) :
    Continuous fun z : A × (B × B) => F (z.1, z.2.1) * F (z.1, z.2.2) * c (z.2.1⁻¹ * z.2.2) ^ 2 := by
  have h1 : Continuous fun z : A × (B × B) => F (z.1, z.2.1) :=
    hF.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have h2 : Continuous fun z : A × (B × B) => F (z.1, z.2.2) :=
    hF.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  have h3 : Continuous fun z : A × (B × B) => c (z.2.1⁻¹ * z.2.2) :=
    hc.comp (((continuous_fst.comp continuous_snd).inv).mul (continuous_snd.comp continuous_snd))
  exact (h1.mul h2).mul (h3.pow 2)

theorem cont_slice {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] (f : A × B → ℝ)
    (hf : Continuous f) (a : A) : Continuous fun b : B => f (a, b) :=
  hf.comp (continuous_const.prodMk continuous_id)

theorem cK_continuous {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Continuous (cK T) := by
  have h : Continuous fun k : KG ε => T.op k T.w :=
    (KType_continuous_op T).clm_apply continuous_const
  have h2 : Continuous fun k : KG ε => ‖⟪T.w, T.op k T.w⟫_ℂ‖ := (continuous_const.inner h).norm
  exact h2

theorem hI_continuous (hC : PhiCont) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    (μ : Fin n → ℤ) :
    Continuous fun z : UJ ε × (KG ε × KG ε) => hI T μ (pP (toM z.1)) z.2 :=
  cont_triple (fun z : UJ ε × KG ε => phiK μ (pP (toM z.1)) z.2) (cK T) (hC n ε μ) (cK_continuous T)

theorem hI_measurable (hC : PhiCont) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    (μ : Fin n → ℤ) :
    Measurable fun z : UJ ε × (KG ε × KG ε) => hI T μ (pP (toM z.1)) z.2 :=
  (hI_continuous hC T μ).measurable

theorem hI_nonneg (hMul : PhiMul) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) (p : KG ε × KG ε) :
    0 ≤ hI T μ x p := by
  have a := (hMul n ε μ 0 x hx p.1).1
  have b := (hMul n ε μ 0 x hx p.2).1
  exact mul_nonneg (mul_pos a b).le (sq_nonneg _)

theorem hI_integrable (hC : PhiCont) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ)
    (μ : Fin n → ℤ) (g : UJ ε) :
    Integrable (fun p : KG ε × KG ε => hI T μ (pP (toM g)) p) ((dk ε).prod (dk ε)) := by
  haveI : IsProbabilityMeasure (dk ε) := (dk_props ε).1
  have hc : Continuous fun p : KG ε × KG ε => hI T μ (pP (toM g)) p :=
    cont_slice (fun z : UJ ε × (KG ε × KG ε) => hI T μ (pP (toM z.1)) z.2)
      (hI_continuous hC T μ) g
  exact integrableOn_univ.mp (hc.continuousOn.integrableOn_compact isCompact_univ)

theorem hsInt : HsPs → HsPol → PhiMul → PhiCont → HsInt := by
  intro hPs hPol hMul hC n ε Λ T μ
  refine ⟨hI_measurable hC T μ, fun g => ?_⟩
  obtain ⟨⟨X, hX, hE⟩, hN⟩ := hPol n ε (toM g) g.2
  have hpd : (pP (toM g)).PosDef := by
    rw [hE]
    exact exp_noncompactPart_posDef hX
  rw [hN Λ T μ, hPs n ε Λ T μ _ hpd, ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal (hI_integrable hC T μ g)
      (Filter.Eventually.of_forall (hI_nonneg hMul T μ hpd))]

end GlobalTheory.CompanionTheory.RgFd
