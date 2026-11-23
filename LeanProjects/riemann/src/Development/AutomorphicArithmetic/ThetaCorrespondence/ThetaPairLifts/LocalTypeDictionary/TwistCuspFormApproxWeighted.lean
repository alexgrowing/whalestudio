import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormUniformHeightApprox
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCuspAverageKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormUniformHeightApproxStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
noncomputable section
open scoped ENNReal
theorem GlobalTheory.CuspApproxAll.cusp_form_approx_weighted : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (A : ℕ) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (F : Fin n → N.Maps) (v : Fin n → Formalism.IndefR.Links.SmT N.M), (∀ l, F l ∈ N.Cusp θ) ∧ ∀ g, ‖φ g - ∑ l, F l (v l) g‖ * GlobalTheory.Grow.quotHeight N.V g ^ A ≤ ε := by
  intro D θ hθ hP N φ hφ A ε hε
  obtain ⟨hA, hc, -⟩ := id hφ
  obtain ⟨U, hU, hlev⟩ := hA.level
  obtain ⟨d, C, hC⟩ := hP.cuspDecaySobolev D θ hθ N.V U hU 0 A
  have hφg : GlobalTheory.CuspApproxAll.Good θ N.V φ := ⟨GlobalTheory.Size.rapidDecSm_of_cuspForm hP.cuspRapidDecay hθ hA hc, hc⟩
  have hη : 0 < ε / ((C : ℝ) + 1) := div_pos hε (by positivity)
  obtain ⟨e, he, hgrow⟩ := GlobalTheory.T.exists_KFinite_iteratedCompactAverage_approx D θ hθ N φ hφg.1 (Finset.univ : Finset D.what₂.Tau).toList (Finset.nodup_toList _) d _ hη
  obtain ⟨n, F, v, hF, hFlev, hsum⟩ := _root_.GlobalTheory.T.twist_cusp_average_k_finite_decomposition D θ hθ hP N φ hφ U hU hlev e he
    (Finset.univ : Finset D.what₂.Tau).toList (fun τ => Finset.mem_toList.2 (Finset.mem_univ τ))
  rw [hsum] at hgrow
  refine ⟨n, F, v, hF, fun g => ?_⟩
  set ψ : GA D N.V → ℂ := φ - ∑ j, F j (v j) with hψ
  have hsg : GlobalTheory.CuspApproxAll.Good θ N.V (∑ j, F j (v j)) :=
    Finset.sum_induction _ (GlobalTheory.CuspApproxAll.Good θ N.V) (fun _ _ => GlobalTheory.CuspApproxAll.good_add)
      (GlobalTheory.CuspApproxAll.good_zero θ N.V) fun j _ => GlobalTheory.CuspApproxAll.good_value hP.cuspRapidDecay hθ N (hF j) (v j)
  have hg : GlobalTheory.CuspApproxAll.Good θ N.V ψ := by
    have := GlobalTheory.CuspApproxAll.good_add hφg (GlobalTheory.CuspApproxAll.good_smul (-1) hsg)
    rwa [neg_one_smul, ← sub_eq_add_neg] at this
  have hψlev : ∀ k ∈ U, k ∈ GfC N.V → ∀ x, ψ (x * k) = ψ x := fun k hk hk' x => by
    simp only [hψ, Pi.sub_apply, Finset.sum_apply, hlev k hk hk' x, hFlev _ k hk hk' x]
  have h1 := hC ψ hg.1.toIsAutFun hψlev hg.1.smooth (GlobalTheory.CuspApproxAll.growthSob_zero_ne_top hg.1) hg.2
  have h2 : decaySize N.V A ψ ≤ ENNReal.ofReal ε := by
    have h4 : (C : ℝ≥0∞) * growthSob θ N.V d 0 ψ ≤ C * ENNReal.ofReal (ε / ((C : ℝ) + 1)) := by gcongr
    refine h1.trans (h4.trans ?_)
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [NNReal.coe_nonneg C]
  have h3 : ENNReal.ofReal (‖ψ g‖ * quotHeight N.V g ^ A) ≤ ENNReal.ofReal ε := (le_iSup (fun x => ENNReal.ofReal (‖ψ x‖ * quotHeight N.V x ^ A)) g).trans h2
  rw [ENNReal.ofReal_le_ofReal_iff hε.le] at h3
  simpa [hψ, Finset.sum_apply] using h3
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_cusp_form_approx_weighted : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (A : ℕ) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (F : Fin n → N.Maps) (v : Fin n → Formalism.IndefR.Links.SmT N.M), (∀ l, F l ∈ N.Cusp θ) ∧ ∀ g, ‖φ g - ∑ l, F l (v l) g‖ * GlobalTheory.Grow.quotHeight N.V g ^ A ≤ ε := by
  first | exact @_root_.GlobalTheory.CuspApproxAll.cusp_form_approx_weighted | exact _root_.GlobalTheory.CuspApproxAll.cusp_form_approx_weighted | (intros; apply _root_.GlobalTheory.CuspApproxAll.cusp_form_approx_weighted <;> assumption)
end
