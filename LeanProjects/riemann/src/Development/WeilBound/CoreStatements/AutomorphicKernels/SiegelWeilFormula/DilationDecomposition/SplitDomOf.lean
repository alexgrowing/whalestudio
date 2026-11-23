import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.ThetaPtOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdDecomp
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.LiftExOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.ProdGenMem

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Kdil

theorem isSw_gauss {m n : ℕ} {δ : ℝ} (hδ : 0 < δ) : IsSw (fun u : Fin m → Fin n → ℂ => (Real.exp (-δ * sq u) : ℂ)) := by
  obtain ⟨S, hS⟩ := KFock.fPSch (1 : PX m n) hδ
  refine ⟨S, funext fun u => ?_⟩
  rw [hS u]
  simp [evX, gs, sq, Complex.ofReal_exp, neg_mul]

theorem splitDom_of (hT : TAll) (hAw : AwayAct) (hD : DecompW) : SplitDom := by
  intro F E _ _ _ _ _ σ d R w L hL Ψ hΨ g
  obtain ⟨x, y₀, hg, hx⟩ := hD F E σ d R w g
  have hind : d.Indep w Ψ := KFock.away_inv R w Ψ hΨ
  obtain ⟨A, hA⟩ := hAw F E σ d R w x hx
  obtain ⟨-, hAT⟩ := hA Ψ hind
  refine ⟨y₀, A Ψ, ?_, ?_⟩
  · intro Φ hΦ f hf hT' y
    have h1 := (hL (y₀ * y) f hf).2 Ψ hind Φ hΦ hT'
    have hmem : d.om (R.ι w (y₀ * y)) Φ ∈ d.sch := om_mem d _ hΦ
    have h2 := hAT (L (y₀ * y) f) (hL (y₀ * y) f hf).1 _ hmem h1
    rw [hg, mul_assoc, ← map_mul (R.ι w), map_mul d.om, Module.End.mul_apply]
    exact h2
  · intro δ hδ
    obtain ⟨hTs, hTsurj, -⟩ := hT.1 F E σ d
    have hm := KFock.tens_mem d R w _ (isSw_gauss hδ) Ψ hΨ
    obtain ⟨Φ, hΦ, hTΦ⟩ := hTsurj _ hm
    have h2 := hAT _ (isSw_gauss hδ) Φ hΦ hTΦ
    rw [← h2]
    exact hTs _ (om_mem d x hΦ)

end PositivityTheory.SiegelWeilFormula.Kdil

end
