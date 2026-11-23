import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMir

def stabSub {M W : Type} [Group M] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ M W) (w : W) :
    Subgroup M where
  carrier := {m | σ m w = w}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem twAct_isSmooth {G M V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
    [TopologicalSpace M] [IsTopologicalGroup M] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hsc : Continuous s)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) :
    IsSmooth (twAct ρ N θ s hs) := by
  intro x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hle : ((stabSub ρ v).comap s) ≤ stabSub (twAct ρ N θ s hs) (Submodule.Quotient.mk v) := by
    intro m hm
    change ρ (s m) v = v at hm
    change (twAct ρ N θ s hs) m (Submodule.Quotient.mk v) = Submodule.Quotient.mk v
    exact congrArg (Submodule.Quotient.mk (p := twKer ρ N θ)) hm
  have hop : IsOpen (((stabSub ρ v).comap s : Subgroup M) : Set M) :=
    (hρ v).preimage hsc
  exact Subgroup.isOpen_mono hle hop

end GlobalTheory.CompanionTheory.BZMir
