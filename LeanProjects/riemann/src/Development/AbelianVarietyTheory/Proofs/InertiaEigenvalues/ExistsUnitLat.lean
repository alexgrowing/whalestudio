import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL

noncomputable def unitLat (G : Type) [Group G] [TopologicalSpace G] (Qp LL O : Type) [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    [IsTopologicalRing LL] (hO : Function.Injective (algebraMap O LL)) : LocLat G Qp LL O where
  V := LL
  ρ := Representation.trivial LL G LL
  cont := fun x => by simpa using continuous_const
  L :=
    { T := Submodule.span O {1}
      fg := Submodule.fg_span_singleton _
      free := Module.Free.of_equiv
        ((LinearEquiv.ofInjective (LinearMap.toSpanSingleton O LL 1)
          (fun a b h => hO (by simpa [Algebra.smul_def] using h))).trans
          (LinearEquiv.ofEq _ _ (LinearMap.span_singleton_eq_range O LL 1).symm))
      span := by
        rw [Submodule.span_span_of_tower, eq_top_iff]
        intro x _
        exact Submodule.mem_span_singleton.2 ⟨x, by simp⟩
      stable := fun g x hx => by simpa using hx }

theorem exists_unitLat : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), ∃ one : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), (∀ g x, one.ρ g x = x) ∧ ∃ e : one.V, e ≠ 0 ∧ one.L.T = Submodule.span ↥(OL LL) {e} := by
  intro l _ K LL
  have hO : Function.Injective (algebraMap (↥(OL LL)) ↥LL.1) :=
    Subtype.val_injective
  refine ⟨unitLat (↥(GK K)) ℚ_[l] ↥LL.1 ↥(OL LL) hO, fun _ _ => rfl, (1 : ↥LL.1), ?_, rfl⟩
  show (1 : ↥LL.1) ≠ 0
  exact one_ne_zero

end GlobalTheory.HWL
