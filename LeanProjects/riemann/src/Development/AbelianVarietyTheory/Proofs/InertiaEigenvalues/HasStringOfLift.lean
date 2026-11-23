import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.LiftInjProof

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem hasString_of_lift (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (ok : Pl D.host.E → Prop)
    (h1 : UnrCorr R i t fun w => ¬ ok w) (h1' : UnrCorr R i t ok)
    (h2 : ParamsEx R i t) (h3 : DownEig R i t) {h} (hh : GlobalTheory.Hk3.IsOpsV R i t h) {s : Sys D} {y} (hy : IsEigV R i t h s y)
    (h0 : R.thF i t y ≠ 0) : HasString R i t s := by
  obtain ⟨c, hc⟩ := h3 h hh s
  obtain ⟨B, hB⟩ := h2.1 h hh s y hy (fun e => h0 (by rw [e, map_zero]))
  obtain ⟨B', hB', hb⟩ := h2.2 c ((Submodule.ne_bot_iff _).2 ⟨_, hc y hy, h0⟩)
  refine ⟨B, hB, fun w hw => ⟨(B' w).map (fun a : ℂˣ => ((a * valV R i t w * (valW R i t w)⁻¹ : ℂˣ) : ℂ)), ?_, fun a ha => ?_⟩⟩
  · by_cases hw' : ok w
    · exact h1' h hh s c y hy h0 (hc y hy) B B' hB hB' w hw hw'
    · exact h1 h hh s c y hy h0 (hc y hy) B B' hB hB' w hw hw'
  obtain ⟨b, hb', rfl⟩ := Multiset.mem_map.1 ha
  have e1 : ‖(valV R i t w : ℂ)‖ = 1 := GlobalTheory.LFun.norm_val _ _
  have e2 : ‖(valW R i t w : ℂ)‖ = 1 := GlobalTheory.LFun.norm_val _ _
  simpa [e1, e2] using hb w hw b hb'

theorem liftInj_of_typeNZ : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → (∀ i, TypeNZ R i A.μ0 ∧ DownEig R i A.μ0 ∧ UnrCorr R i A.μ0 (fun w => ¬ IsConjPl w w) ∧ UnrCorr R i A.μ0 (fun w => IsConjPl w w) ∧ ParamsEx R i A.μ0) → GlobalTheory.LiftRows.LiftInj R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ hZ
  intro i h hops s x y hx hy hxne hyG hy0
  obtain ⟨hT, hDE, hU1, hU2, hPE⟩ := hZ i
  have hF : R.thF i A.μ0 x ≠ 0 := by
    intro h0
    apply hxne
    apply (hG.core.models.HW i (sg0 D A)).1
    rw [hG.core.thP.thG i A.μ0 x, h0, map_zero, map_zero]
  exact hT h hops s (hasString_of_lift R i A.μ0 (fun w => IsConjPl w w) hU1 hU2 hPE hDE hops hx hF) y hy hyG hy0

end GlobalTheory.LiftInjProof

end
