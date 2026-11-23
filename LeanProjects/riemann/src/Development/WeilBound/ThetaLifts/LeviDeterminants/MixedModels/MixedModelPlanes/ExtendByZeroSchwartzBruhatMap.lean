import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroSchwartzBruhatMap
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
theorem _root_.PositivityTheory.Mix.T.extend_by_zero_schwartzBruhat_map : ∀ (F : Type) [Field F] [NumberField F] {κ₁ κ : Type} [Fintype κ₁] [Fintype κ] (j : κ₁ → κ), Function.Injective j →
    ∀ v : Pl F, (SB (κ → Fv F v)).map (LinearMap.funLeft ℂ ℂ (fun y : κ₁ → Fv F v => Function.extend j y 0)) = SB (κ₁ → Fv F v) := by
  first | exact @GlobalTheory.SchwartzBruhatRestrict.map_funLeft_extendZero | exact fun _ => @GlobalTheory.SchwartzBruhatRestrict.map_funLeft_extendZero | exact GlobalTheory.SchwartzBruhatRestrict.map_funLeft_extendZero | exact @GlobalTheory.SchwartzBruhatRestrict.map_funLeft_extendZero trivial
