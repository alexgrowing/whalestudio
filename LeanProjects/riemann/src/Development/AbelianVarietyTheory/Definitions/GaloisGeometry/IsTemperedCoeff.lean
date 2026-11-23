import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL
namespace GlobalTheory.LocGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ}

variable (k N) in

abbrev AdGL : Type := GL (Fin N) k ⧸ Subgroup.center (GL (Fin N) k)

def CoeffLp (p : ℝ) (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∀ [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : Measure (AdGL k N)), μ.IsHaarMeasure →
    ∀ (v : V) (l : Module.Dual ℂ V), IsOpen {g : GL (Fin N) k | l ∘ₗ π g = l} →
      ∃ F : AdGL k N → ℝ, (∀ g : GL (Fin N) k, F (QuotientGroup.mk g) = ‖l (π g v)‖) ∧ MemLp F (ENNReal.ofReal p) μ

def IsSqIntCoeff (π : Representation ℂ (GL (Fin N) k) V) : Prop := CoeffLp 2 π

def IsTemperedCoeff (π : Representation ℂ (GL (Fin N) k) V) : Prop := ∀ ε : ℝ, 0 < ε → CoeffLp (2 + ε) π

end GlobalTheory.LocGL
