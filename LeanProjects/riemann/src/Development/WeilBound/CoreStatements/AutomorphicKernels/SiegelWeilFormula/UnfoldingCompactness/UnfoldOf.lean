import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.UnfoldCore
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IsClosedSiegelStabiliser

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.kunf

theorem unfold : Unfold := by
  intro F E _ _ _ _ _ σ d s₁ f hf hE
  obtain ⟨U, p, Ê, t, -, -, -, -, -, -, -, hmaj⟩ := hE 0
  refine ⟨t, fun z hz nb lam 𝓖 hc ε w hw x => ?_⟩
  have hΦ : (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x) = flat d.a f s₁ z := funext fun x => by
    rw [flat, ht_eq]
  have hmaj' := (hmaj z hz).1
  rw [hΦ] at hmaj'
  have hlaw : Law d.χ (s₁ + d.n / 2) f := hf.law
  have hlawF := hlaw.flat (s₀ := s₁) d.ok.hgt (a_pos d) z
  have hcore := unfoldCore d.B d.ok.good d.ok.frame hc (flat d.a f s₁ z)
    (continuous_flat hf.cont (continuous_a d) (a_pos d) z)
    (fun p hp hpr y => hlawF.rat d.ok.hecke hp hpr y)
    (fun p t ht hdet y => by rw [hlawF p t y ht, hdet]; simp)
    hmaj' hw x
  refine ⟨hcore.1, fun T hT => ?_⟩
  show fc d.B.ψ d.b nb lam 𝓖 (GlobalTheory.Eis.cosetSum _ _ (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x)) T x = _
  rw [hΦ]
  exact hcore.2 T hT

end PositivityTheory.SiegelWeilFormula.kunf

end
