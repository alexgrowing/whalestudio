import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
import Development.DiscreteGroups.GlobalIrreducibility.LConvSepT

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology

namespace DiscreteGroups.sglob.LConv

theorem sepOfExtreme : SepOfExtreme := by
  intro hEx hIrr hUA k _ _ _ _ _ m
  obtain ⟨I, hI1, hI2, hI3⟩ := exists_pos_isInvIntegral k m
  have hI : PosInt I := ⟨hI1, hI2, hI3⟩
  refine ⟨I, hI1, fun ψ hψ f hf hsep => ?_⟩
  by_contra hf0
  let x₀ : WT (m := m) ψ := ⟨f, hf⟩
  have hx₀ : x₀ ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
  obtain ⟨B, hBext, hBf⟩ := hEx _ _ (rhoW ψ) exists_countable_span (formI ψ I) (isInvForm_formI hI) x₀
    (formI_self_ne_zero hI hx₀)
  have hB := hBext.1
  have hZ := hIrr _ _ (rhoW ψ) isSmooth_rhoW exists_fix (fun K hKo hKc => hUA k m K hKo hKc) B hBext
  let τ : IrrRep (GL (Fin m) k) :=
    ⟨WSp hψ hI hB, tauRep hψ hI hB, isSmooth_tau hψ hI hB, isIrreducible_tau hψ hI hB hZ hBf⟩
  let l : Module.Dual ℂ τ.V := (LinearMap.proj (1 : GL (Fin m) k)).comp (WSp hψ hI hB).subtype
  have hl : IsFunctional ψ⁻¹ τ.ρ l := fun u hu w => by
    obtain ⟨y, hy⟩ := w.2
    show (w : GL (Fin m) k → ℂ) (1 * u) = _ * (w : GL (Fin m) k → ℂ) 1
    have h1 := Wf_left hψ hI hB y hu 1
    rw [mul_one] at h1
    rw [one_mul, ← hy, h1]
  have h0 := hsep τ l hl (Phi hψ hI hB x₀)
  have e : (fun g => f g * l (τ.ρ g (Phi hψ hI hB x₀))) =
      fun g => (x₀ : GL (Fin m) k → ℂ) g * Wf ψ hψ I B x₀ g := funext fun g => by
    show f g * Wf ψ hψ I B x₀ (1 * g) = f g * Wf ψ hψ I B x₀ g
    rw [one_mul]
  apply hBf
  rw [← repr hψ hI hB x₀ x₀, ← e]
  exact h0

end DiscreteGroups.sglob.LConv

end
