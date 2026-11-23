import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThPDatumEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevMov

theorem finE_mem_St_of_isMov : ∀ (D : D7) (V : HSp D) (L : Lt D.host.E V.rank) (β : GL (Fin V.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame β L → ∀ k : GA D V, IsMov (fmt V k) L L → Lev.finE V k ∈ Formalism.L2.DIV.St β := by
  intro D V L β hβ k hk
  have h1 := GlobalTheory.LevSplit.mem_St_iff β L hβ (Lev.finE V k)
  have h2 := GlobalTheory.LevSplit.stab_gen (GlobalTheory.LevSplit.swp D.host.F D.host.E) GlobalTheory.LevSplit.swp_bij.2 _ _
    (GlobalTheory.LevSplit.latHat_iff L) (finHom V k)
  refine h1.2 (h2.1 ?_)
  have hk' : ∀ u, u ∈ hatV L ↔ ∃ u₀ ∈ hatV L, u = (finHom V k).1 *ᵥ u₀ := hk
  intro y
  constructor
  · intro hy
    exact (hk' _).2 ⟨y, hy, rfl⟩
  · intro hy
    obtain ⟨u₀, hu₀, e⟩ := (hk' _).1 hy
    have e2 : y = u₀ := by
      have := congrArg (fun z => ((finHom V k)⁻¹).1 *ᵥ z) e
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
      exact this
    rw [e2]; exact hu₀

end GlobalTheory.LevMov
