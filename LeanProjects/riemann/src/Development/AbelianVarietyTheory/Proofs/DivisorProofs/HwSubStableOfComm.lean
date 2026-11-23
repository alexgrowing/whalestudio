import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweHighestWeightSupStableLeStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem hwSub_stable_of_comm {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (f : Module.End ℂ V)
    (hf : ∀ Z v, f (act Z v) = act Z (f v)) (μ : Ix p q → ℚ) :
    ∀ v ∈ hwSub act μ, f v ∈ hwSub act μ := by
  intro v hv
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hv ⊢
  obtain ⟨h1, h2⟩ := hv
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · have := congrArg f (h1 a)
    simpa [hf, map_sub, map_smul] using this
  · rw [← hf, h2 a b hab, map_zero]

theorem hw_joint_split : ∀ (T : Type) [Fintype T] [DecidableEq T] (R S : T → ℕ) (V : Type) [AddCommGroup V]
    [Module ℂ V] (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ V), (∀ w, Good (a w)) →
    (∀ w w', w ≠ w' → ∀ Z Z' v, a w Z (a w' Z' v) = a w' Z' (a w Z v)) →
    ∀ N N' : Submodule ℂ V, (∀ w, Stab (a w) N) → (∀ w, Stab (a w) N') →
    ∀ μ : ∀ w, Ix (R w) (S w) → ℚ,
    (N ⊔ N') ⊓ (⨅ w, hwSub (a w) (μ w)) ≤
      (N ⊓ ⨅ w, hwSub (a w) (μ w)) ⊔ (N' ⊓ ⨅ w, hwSub (a w) (μ w)) := by
  intro T _ _ R S V _ _ a hg hc N N' hN hN' μ
  have key : ∀ s : Finset T, (N ⊔ N') ⊓ (⨅ w ∈ s, hwSub (a w) (μ w)) ≤
      (N ⊓ ⨅ w ∈ s, hwSub (a w) (μ w)) ⊔ (N' ⊓ ⨅ w ∈ s, hwSub (a w) (μ w)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert w s hws ih =>
      set H := ⨅ w ∈ s, hwSub (a w) (μ w) with hH
      have hHst : ∀ X, ∀ v ∈ H, a w X v ∈ H := by
        intro X v hv
        rw [hH, Submodule.mem_iInf] at hv ⊢
        intro w'
        have hv' := hv w'
        rw [Submodule.mem_iInf] at hv' ⊢
        intro hw'
        have hne : w ≠ w' := fun h => hws (h ▸ hw')
        exact hwSub_stable_of_comm (a w') (a w X) (fun Z u => hc w w' hne X Z u) (μ w') v (hv' hw')
      have hK : ∀ M : Submodule ℂ V, (∀ Z, ∀ y ∈ M, a w Z y ∈ M) → KStable (a w) (M ⊓ H) := by
        intro M hM X _ v hv
        exact Submodule.mem_inf.mpr ⟨hM X v (Submodule.mem_inf.mp hv).1, hHst X v (Submodule.mem_inf.mp hv).2⟩
      have hsp := GlobalTheory.T.howeHighestWeight_sup_stable_le (R w) (S w) V (a w) (hg w) (N ⊓ H) (N' ⊓ H) (hK N (hN w)) (hK N' (hN' w)) (μ w)
      rw [Finset.iInf_insert]
      calc (N ⊔ N') ⊓ (hwSub (a w) (μ w) ⊓ H) = ((N ⊔ N') ⊓ H) ⊓ hwSub (a w) (μ w) := by
              rw [inf_comm (hwSub (a w) (μ w)) H, inf_assoc]
        _ ≤ ((N ⊓ H) ⊔ (N' ⊓ H)) ⊓ hwSub (a w) (μ w) := inf_le_inf_right _ ih
        _ ≤ ((N ⊓ H) ⊓ hwSub (a w) (μ w)) ⊔ ((N' ⊓ H) ⊓ hwSub (a w) (μ w)) := hsp
        _ = (N ⊓ (hwSub (a w) (μ w) ⊓ H)) ⊔ (N' ⊓ (hwSub (a w) (μ w) ⊓ H)) := by
              rw [inf_assoc, inf_assoc, inf_comm H]
  simpa using key Finset.univ

end GlobalTheory.HoweR
