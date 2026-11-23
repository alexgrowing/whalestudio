import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.WhitKOfSteps

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem holValueAt_const_mul_cpow (c : ℂ) {C : ℝ} (hC : 0 < C) (s₀ : ℂ) :
    HolValueAt (fun z => c * (C : ℂ) ^ (z - s₀)) s₀ c := by
  have h := holValueAt_self (h := fun z => c * (C : ℂ) ^ (z - s₀)) (σ := s₀.re - 1) (s₀ := s₀)
    (fun z _ => analyticAt_const.mul (analyticAt_const.cpow (analyticAt_id.sub analyticAt_const)
      (Complex.ofReal_mem_slitPlane.2 hC))) (by linarith)
  convert h using 1
  simp

theorem coreStep : CoreStep := by
  intro hT hA hS hU hW hD F E _ _ _ _ _ σ d R hnm hE Φ hΦ hP x hx nb lam 𝓖 hcd ε w hw T hTnd
  obtain ⟨dd, J, T', bs, ψ, θ, l, εs, fr, g, P, lv, L₁, L₂, Φg, Φf, Φv, μ, ν, c, C, hDat, hC, ⟨t, ht⟩, μH, 𝓕, hH, hF,
    horb⟩ := hD hT hA F E σ d R hnm Φ hΦ hP x hx nb lam 𝓖 hcd ε w hw T hTnd
  obtain ⟨t', ht'⟩ := hU F E σ d (s0 d.m d.n) (d.sec0 Φ) (hS F E σ d Φ hΦ) (hE Φ hΦ)
  have hG := hW F E σ d.m d.n dd J T' bs ψ (InfinitePlace F) θ l εs fr g P lv L₁ L₂ Φg Φf Φv μ ν hDat
    ⟨max t t', fun z hz => (ht z (lt_of_le_of_lt (le_max_left _ _) hz)).1
      ((ht' z (lt_of_le_of_lt (le_max_right _ _) hz) nb lam 𝓖 hcd ε w hw x).1)⟩ μH 𝓕 hH hF
  rw [horb]
  exact ((holValueAt_const_mul_cpow c hC (s0 d.m d.n)).mul hG).congr ⟨t, fun z hz => ((ht z hz).2).symm⟩

end PositivityTheory.SiegelWeilFormula.KWhit

end
