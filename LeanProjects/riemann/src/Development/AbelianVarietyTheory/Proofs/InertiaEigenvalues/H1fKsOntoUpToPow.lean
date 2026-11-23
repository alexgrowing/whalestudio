import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemContinuousCocyclesRestrictLattice

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.RightExactKs

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem h1fKs_onto_up_to_pow : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L), Function.Surjective π.f → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → ∀ κ₂ ∈ H1fIntegralCyclotomicLayer W T₂, ∃ (c : ℕ), ∃ κ₁ ∈ H1fIntegralCyclotomicLayer W T₁, (resHom π W.GKs).H1map κ₁ = (l ^ c : ℕ) • κ₂ := by
  intro D HW l _ K s LL h W T₁ T₂ π hπ h₁ h₂ κ₂ hκ₂
  refine (Submodule.mem_map.1 hκ₂).elim fun c₂ hc => ?_
  have hf : ((c₂ : _) : ↥W.GKs → T₂.V) ∈ BlochKatoCocyclesSubgroup ((D.loc l).PD K) W.GKs T₂ := hc.1.2
  refine hf.2.elim fun x hx => ?_
  refine (lift_cocycle (D.loc l) (D.locA l) (D.locT l) h.2.2.1 W ((HW l).W_s K s LL h)
    T₁ T₂ π hπ h₁ h₂ c₂ κ₂ hc.2 x hx).elim fun n hn => hn.elim fun c₁ hn =>
      hn.elim fun κ₁ hn => ?_
  refine ⟨n, κ₁, Submodule.mem_map.2 ⟨c₁, ⟨c₁.2, ?_⟩, hn.1⟩, hn.2.2⟩
  exact ⟨mem_continuousCocycles_restrictLattice T₁ W.GKs c₁, hn.2.1⟩

end GlobalTheory.NL.RightExactKs
