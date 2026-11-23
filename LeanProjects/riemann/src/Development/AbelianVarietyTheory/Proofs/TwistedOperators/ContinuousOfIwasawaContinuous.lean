import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace

namespace GlobalTheory.ParabCompact

theorem continuous_of_continuous_mul : ∀ (n a : ℕ) (ε : Fin n → Bool) (j : Fin a → ℕ) (W : Flag n a), IsIsoFlag ε j W →
    ∀ (Y : Type) [TopologicalSpace Y] (F : UJ ε → Y),
      Continuous (fun q : parab ε W × KG ε => F ((q.1 : UJ ε) * (q.2 : UJ ε))) → Continuous F := by
  intro n a ε j W hW Y _ F hF
  let q : parab ε W × KG ε → UJ ε := fun x => (x.1 : UJ ε) * (x.2 : UJ ε)
  have hqc : Continuous q :=
    (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have hsurj : Function.Surjective q := by
    intro g
    obtain ⟨k, hk, hp⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact hW g
    have hk' : k ∈ KG ε := ((KG_eq ε).symm ▸ hk :)
    exact ⟨(⟨g * k⁻¹, hp⟩, ⟨k, hk'⟩), by simp [q]⟩
  have hι : Topology.IsClosedEmbedding (Prod.map (Subtype.val : parab ε W → UJ ε) (id : KG ε → KG ε)) :=
    (isClosed_parab.isClosedEmbedding_subtypeVal).prodMap Topology.IsClosedEmbedding.id
  let e : UJ ε × KG ε ≃ₜ UJ ε × KG ε :=
    { toFun := fun x => (x.1 * (x.2 : UJ ε), x.2)
      invFun := fun x => (x.1 * (x.2 : UJ ε)⁻¹, x.2)
      left_inv := fun x => by simp
      right_inv := fun x => by simp
      continuous_toFun := by
        exact (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)).prodMk continuous_snd
      continuous_invFun := by
        exact (continuous_fst.mul (continuous_subtype_val.comp continuous_snd).inv).prodMk continuous_snd }
  have hcl : IsClosedMap q := by
    have : q = Prod.fst ∘ e ∘ Prod.map Subtype.val id := by funext x; rfl
    rw [this]
    exact isClosedMap_fst_of_compactSpace.comp (e.isClosedMap.comp hι.isClosedMap)
  have hQ : Topology.IsQuotientMap q := hcl.isQuotientMap hqc hsurj
  exact hQ.continuous_iff.2 hF

end GlobalTheory.ParabCompact
