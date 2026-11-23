import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker

theorem isWeak_one_of_rank_zero (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (h : T.rank = 0) :
    IsWeak ψ S T 1 := by
  haveI : IsEmpty (Fin T.rank) := by rw [h]; infer_instance
  haveI : Subsingleton (WO S T) := ⟨fun a b => by
    first
      | (funext i; exact isEmptyElim i)
      | (funext j i; exact isEmptyElim i)⟩
  refine ⟨fun p f hf => by simpa using hf, fun g k w₀ f _ => ?_, fun γ _ γ' _ f _ => by simp,
    fun μ 𝓕 _ _ p f _ => by simp⟩
  rw [Subsingleton.elim (actO S T g k w₀) w₀]
  simp

end GlobalTheory.Ker
