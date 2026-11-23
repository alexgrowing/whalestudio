import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ScalarOnInertiaProp

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace DeterminantVector

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem mem_fixed_iff {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin N) k) V) (K : Subgroup (GL (Fin N) k)) (v : V) :
    v ∈ fixed ρ K ↔ ∀ g ∈ K, ρ g v = v := by
  constructor
  · intro h g hg
    simpa using h ⟨g, hg⟩
  · intro h g
    simpa using h g g.2

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem hasDetVec_twist {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin N) k) V) (η : kˣ →* ℂˣ) (h : IsSpherical ρ) :
    HasDetVec (twist ρ (detChar (Fin N) η)) η := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  refine ⟨v, hv0, fun g hg => ?_⟩
  rw [twist_apply, detChar_apply, (mem_fixed_iff ρ _ v).1 hv g hg]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem isSpherical_twist {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin N) k) V) (η : kˣ →* ℂˣ) (h : HasDetVec ρ η) :
    IsSpherical (twist ρ (detChar (Fin N) η⁻¹)) := by
  obtain ⟨v, hv0, hv⟩ := h
  refine (Submodule.ne_bot_iff _).2 ⟨v, ?_, hv0⟩
  refine (mem_fixed_iff _ _ v).2 fun g hg => ?_
  rw [twist_apply, detChar_apply, hv g hg, smul_smul, MonoidHom.inv_apply, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_smul]

end DeterminantVector

theorem step_detVec : DeterminantVectorProp := by
  intro k _ _ _ _ N V _ _ ρ η
  exact ⟨DeterminantVector.hasDetVec_twist ρ η, DeterminantVector.isSpherical_twist ρ η⟩

end UpperTheory.TNZ
