import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyCompSideMulEq

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne

noncomputable section
namespace GlobalTheory.PosOne.SrcAction

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def srcRep {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) :
    Representation ℂ (GL a k) (SB (Matrix b a k)) where
  toFun g :=
    { toFun := fun Φ => ⟨om μ g 1 Φ.1, om_mem_SB μ g 1 Φ.2⟩
      map_add' := fun Φ Ψ => by
        apply Subtype.ext
        have := om_smul_add μ g (1 : GL b k) 1 Φ.1 Ψ.1
        simpa using this
      map_smul' := fun z Φ => by
        apply Subtype.ext
        have := om_smul_add μ g (1 : GL b k) z Φ.1 0
        have h0 : om μ g (1 : GL b k) (0 : Matrix b a k → ℂ) = 0 := by
          funext x
          simp [om]
        simpa [h0] using this }
  map_one' := LinearMap.ext fun Φ => Subtype.ext (om_one μ Φ.1)
  map_mul' g h := LinearMap.ext fun Φ => Subtype.ext (by
    show om μ (g * h) 1 Φ.1 = om μ g 1 (om μ h 1 Φ.1)
    rw [← om_mul, mul_one])

end GlobalTheory.PosOne.SrcAction

namespace GlobalTheory.PosOne
open GlobalTheory.PosOne.SrcAction

theorem isSrc_exists_isSmoothRep : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)), (∃ ρ' : Representation ℂ (GL a k) (SB (Matrix b a k)), IsSrc μ ρ') ∧ ∀ ρ' : Representation ℂ (GL a k) (SB (Matrix b a k)), IsSrc μ ρ' → IsSmoothRep ρ' := by
  intro k _ _ _ _ _ _ a b _ _ _ _ μ hμ
  refine ⟨⟨srcRep μ, fun g Φ => rfl⟩, fun ρ' hρ' Φ => ?_⟩
  have hO := (om_isSmoothRepresentation k a b μ hμ).2.2.2.2 Φ.1 Φ.2
  have hc : Continuous fun g : GL a k => ((g, 1) : GL a k × GL b k) :=
    continuous_id.prodMk continuous_const
  convert hO.preimage hc using 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  rw [← hρ' g Φ]
  exact Subtype.ext_iff

end GlobalTheory.PosOne
