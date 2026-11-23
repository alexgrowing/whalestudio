import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FlatHermRootLineDegree
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CechAbPullApp

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite GlobalTheory SheafPull

noncomputable section

namespace GlobalTheory.Cube.PullHom

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R S : Type} [Ring R] [Ring S]
  {σ : R →+* S} {τ : κ → ι} {A : Cube.{0} ι R} {B : Cube.{0} κ S} (ψ : Cube.PullHom σ τ A B)

open Classical in

def totalPull (y : ∀ s : Finset ι, A.obj s) (s : Finset κ) : B.obj s :=
  if Set.InjOn τ (s : Set κ) then PD.sortSign τ s • ψ.app s (y (s.image τ)) else 0

theorem term_eq_totalPull {p : ℕ} (x : Cube.Term A p) (s : {s : Finset κ // s.card = p}) :
    ψ.term p x s = totalPull ψ (Cube.extend A p x) s.1 := by
  by_cases h : Set.InjOn τ (s.1 : Set κ)
  · rw [term_apply_of_injOn ψ x s h, totalPull, if_pos h, Cube.extend_apply_of_eq A x (card_image s h)]
  · rw [term_apply_of_not_injOn ψ x s h, totalPull, if_neg h]

theorem totalPull_totalD (y : ∀ s : Finset ι, A.obj s) :
    totalPull ψ (Cube.totalD A y) = Cube.totalD B (totalPull ψ y) := by
  funext t
  rw [Cube.totalD_apply B]
  by_cases h : Set.InjOn τ (t : Set κ)
  · rw [totalPull, if_pos h, Cube.totalD_apply A,
      Finset.sum_image (fun x hx y hy hxy => h hx hy hxy), map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : Set.InjOn τ ((t.erase i : Finset κ) : Set κ) :=
      h.mono (Finset.coe_subset.2 (Finset.erase_subset i t))
    rw [totalPull, if_pos hi', map_zsmul, map_zsmul, smul_smul, smul_smul,
      PD.PullMap.sign_inj h hi, ← ψ.app_res]
    congr 2
    exact Cube.res_congr A y (PD.PullMap.image_erase_of_injOn h hi) _ _
  · rw [totalPull, if_neg h]
    obtain ⟨a, ha, b, hb, he, hab⟩ : ∃ a ∈ t, ∃ b ∈ t, τ a = τ b ∧ a ≠ b := by
      by_contra hc
      push_neg at hc
      exact h (fun x hx y hy hxy => hc x hx y hy hxy)
    have zero_of : ∀ s : Finset κ, a ∈ s → b ∈ s → totalPull ψ y s = 0 := fun s has hbs => by
      rw [totalPull, if_neg]
      intro hs
      exact hab (hs has hbs he)
    rw [Finset.sum_eq_add_of_mem a b ha hb hab (fun x _ hne => by
      rw [zero_of _ (Finset.mem_erase.2 ⟨hne.1.symm, ha⟩) (Finset.mem_erase.2 ⟨hne.2.symm, hb⟩),
        map_zero, smul_zero])]
    by_cases hia : Set.InjOn τ ((t.erase a : Finset κ) : Set κ)
    · have hib := PD.PullMap.injOn_erase_swap hb hab he hia
      have key : ∀ c ∈ t, (t.erase c).image τ = t.image τ →
          Cube.res B (Finset.erase_subset c t) (ψ.app (t.erase c) (y ((t.erase c).image τ))) =
            ψ.app t (y (t.image τ)) := by
        intro c _ e
        rw [← ψ.app_res, Cube.res_congr A y e _ (subset_refl _), Cube.res_self]
      rw [totalPull, totalPull, if_pos hia, if_pos hib, map_zsmul, map_zsmul,
        key a ha (PD.PullMap.image_erase_eq hb hab he),
        key b hb (PD.PullMap.image_erase_eq ha hab.symm he.symm), smul_smul, smul_smul, ← add_smul,
        PD.PullMap.sign_pair ha hb hab he hia, neg_add_cancel, zero_smul]
    · have hib : ¬ Set.InjOn τ ((t.erase b : Finset κ) : Set κ) := fun hib =>
        hia (PD.PullMap.injOn_erase_swap ha hab.symm he.symm hib)
      rw [totalPull, totalPull, if_neg hia, if_neg hib, map_zero, map_zero, smul_zero, smul_zero,
        add_zero]

theorem term_d (p : ℕ) (x : Cube.Term A p) :
    ψ.term (p + 1) (Cube.d A p x) = Cube.d B p (ψ.term p x) := by
  funext t
  rw [Cube.d_apply_eq_totalD B (ψ.term p x) (totalPull ψ (Cube.extend A p x))
    (fun s => term_eq_totalPull ψ x s), ← totalPull_totalD]
  by_cases h : Set.InjOn τ (t.1 : Set κ)
  · rw [term_apply_of_injOn ψ _ t h, totalPull, if_pos h, Cube.d_apply_eq_totalD A x (Cube.extend A p x)
      (fun s => (Cube.extend_apply_of_eq A x s.2).symm)]
  · rw [term_apply_of_not_injOn ψ _ t h, totalPull, if_neg h]

end GlobalTheory.Cube.PullHom
