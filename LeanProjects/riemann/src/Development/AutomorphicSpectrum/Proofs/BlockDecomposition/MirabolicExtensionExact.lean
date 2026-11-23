import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd

theorem ses_of_subQuot {G V₁ V₂ V₃ : Type} [Group G] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂]
    [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃] {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂}
    {ρ₃ : Representation ℂ G V₃} (S : Subrepresentation ρ₂) (e₁ : (subQuot S ⊥).Equiv ρ₁)
    (e₂ : (subQuot ⊤ S).Equiv ρ₃) : Ses ρ₁ ρ₂ ρ₃ := by
  let p : Submodule ℂ S.toSubmodule :=
    (⊥ : Subrepresentation ρ₂).toSubmodule.comap S.toSubmodule.subtype
  have hp : p = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    exact (Submodule.mem_bot ℂ).2 (Subtype.ext hs)
  let q : S.toSubmodule ≃ₗ[ℂ] (S.toSubmodule ⧸ p) :=
    LinearEquiv.ofBijective p.mkQ ⟨by
      rw [← LinearMap.ker_eq_bot, Submodule.ker_mkQ]; exact hp, p.mkQ_surjective⟩
  have hq : ∀ (x : G) (w : S.toSubmodule ⧸ p),
      (q.symm (subQuot S ⊥ x w) : V₂) = ρ₂ x (q.symm w : V₂) := by
    intro x w
    obtain ⟨s, rfl⟩ := q.surjective w
    have : subQuot S ⊥ x (q s) = q (S.toRepresentation x s) := rfl
    rw [this, q.symm_apply_apply, q.symm_apply_apply]
    rfl
  let t : V₂ →ₗ[ℂ] (⊤ : Subrepresentation ρ₂).toSubmodule :=
    LinearMap.codRestrict _ LinearMap.id (fun _ => trivial)
  let r : Submodule ℂ (⊤ : Subrepresentation ρ₂).toSubmodule :=
    S.toSubmodule.comap (⊤ : Subrepresentation ρ₂).toSubmodule.subtype
  let f : V₁ →ₗ[ℂ] V₂ :=
    S.toSubmodule.subtype ∘ₗ q.symm.toLinearMap ∘ₗ e₁.toLinearEquiv.symm.toLinearMap
  let g : V₂ →ₗ[ℂ] V₃ := e₂.toLinearEquiv.toLinearMap ∘ₗ r.mkQ ∘ₗ t
  have hf1 : ∀ v, f v = (q.symm (e₁.symm v) : V₂) := fun _ => rfl
  have hg1 : ∀ v, g v = e₂ (r.mkQ (t v)) := fun _ => rfl
  refine ⟨f, g, fun x v => ?_, fun x v => ?_, ?_, ?_, ?_⟩
  · rw [hf1, hf1, eint e₁.symm, hq]
  · rw [hg1, hg1, ← eint e₂]
    rfl
  · intro a b hab
    exact e₁.symm.injective (q.symm.injective (Subtype.ext hab))
  · intro c
    obtain ⟨w, rfl⟩ := e₂.surjective c
    obtain ⟨⟨v, hv⟩, rfl⟩ := r.mkQ_surjective w
    exact ⟨v, rfl⟩
  · ext v
    constructor
    · rintro ⟨a, rfl⟩
      rw [LinearMap.mem_ker, hg1, hf1]
      have : r.mkQ (t (q.symm (e₁.symm a) : V₂)) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact (q.symm (e₁.symm a)).2
      rw [this, map_zero]
    · intro hv
      rw [LinearMap.mem_ker, hg1] at hv
      have h0 : r.mkQ (t v) = 0 := e₂.injective (hv.trans (map_zero e₂).symm)
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
      have hvS : v ∈ S.toSubmodule := h0
      refine ⟨e₁ (q ⟨v, hvS⟩), ?_⟩
      rw [hf1, e₁.symm_apply_apply, q.symm_apply_apply]

theorem ses_of_mext (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (A B C : MRep k n) : MExt A B C → Ses A.ρ B.ρ C.ρ := by
  rintro ⟨S, ⟨e₁⟩, ⟨e₂⟩⟩
  exact ses_of_subQuot S e₁ e₂

end GlobalTheory.CompanionTheory.LeibOrd

end
