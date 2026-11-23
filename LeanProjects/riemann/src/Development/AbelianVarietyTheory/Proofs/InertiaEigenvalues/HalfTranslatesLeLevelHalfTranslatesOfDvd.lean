import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSumPartialProperties
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

theorem trSp_le_of_subhalf : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (l₂ : Geo.Tor.Level H) (e₂ e' : AE D) (P' : Finset (Formalism.L2.DIV.Pl D.host.E)), IsHalfIdem l₂ e₂ → IsIdemSum e' P' → (∀ PP ∈ P', l₂.Mb ≤ PP.asIdeal) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (f₀ : WO V W → ℂ) (M : ℕ) (O : Subring ℂ), trSp ψ V W ΛV ΛW f₀ e' M O ≤ trSp ψ V W ΛV ΛW f₀ e₂ M O := by
  intro D H l₂ e₂ e' P' h₂ h' hP ψ V W ΛV ΛW f₀ M O
  obtain ⟨P₂, ⟨⟨es₂, hes₂, rfl⟩, -⟩, hP₂⟩ := h₂
  obtain ⟨⟨es', hes', rfl⟩, -⟩ := h'
  have hsub : P' ⊆ P₂ := fun PP h => (hP₂ PP).2 (hP PP h)
  have key := GlobalTheory.PartialIdemSum.sum_mul_sum_of_subset P' P₂ es' es₂ hes' hes₂ hsub
  unfold trSp
  refine Submodule.span_mono ?_
  rintro f ⟨y, hy, hM, rfl⟩
  refine ⟨y, fun i j => ?_, hM, rfl⟩
  rw [← hy i j, ← mul_assoc, mul_comm (∑ P ∈ P₂, es₂ P), key]

end GlobalTheory.LevelSeries

end
