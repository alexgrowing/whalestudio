import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SmoothRepIrreducibleSubcontainingVector

noncomputable section

namespace UpperTheory.NonzeroTypeTheory

namespace SchurKernelSubmodule

def kerSub {K : Type} [Group K] {d : ℕ} (ξ : Representation ℂ K (Fin d → ℂ)) {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ K W) (g : (Fin d → ℂ) →ₗ[ℂ] W)
    (hint : ∀ k v, g (ξ k v) = ρ k (g v)) : Subrepresentation ξ :=
  ⟨LinearMap.ker g, fun k v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hint, hv, map_zero]⟩

end SchurKernelSubmodule

open SchurKernelSubmodule in
theorem schurInjective_holds : SchurInjectiveFromIrreducible := by
  intro K _ d ξ hξ W _ _ ρ g hg hint
  haveI : IsSimpleOrder (Subrepresentation ξ) := hξ
  rcases eq_bot_or_eq_top (kerSub ξ ρ g hint) with h | h
  · rw [← LinearMap.ker_eq_bot]
    have hk := congrArg Subrepresentation.toSubmodule h
    first
      | exact hk
      | simpa [kerSub] using hk
  · exfalso
    apply hg
    rw [← LinearMap.ker_eq_top]
    have hk := congrArg Subrepresentation.toSubmodule h
    first
      | exact hk
      | simpa [kerSub] using hk

end UpperTheory.NonzeroTypeTheory
