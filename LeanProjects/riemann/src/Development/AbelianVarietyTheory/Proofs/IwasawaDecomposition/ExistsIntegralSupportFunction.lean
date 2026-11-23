import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntBilinFormToRealMemBalancedPsdCone
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.PolFan

theorem isPolFanOn_exists_strict_bound : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], IsPolFanOn bar φ X → ∃ Nmax : ℕ, ∀ (m : ℕ) (ε : Fin m → LinearMap.BilinForm ℤ X), IsCone bar φ ε → ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), 0 < N ∧ N ≤ Nmax ∧ (∀ i, (ℓ (ε i) : ℝ) = N * φ.evalZ (ε i)) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → N * φ.evalZ β ≤ ℓ β) ∧ ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → N * φ.evalZ β = ℓ β → ∃ (k : ℕ) (c : Fin m → ℕ), 0 < k ∧ k • β = ∑ i, c i • ε i := by
  classical
  intro O _ bar φ X _ _ _ h
  obtain ⟨S, hS, hfin⟩ := h.finite
  let Q : ℕ → Finset (LinearMap.BilinForm ℤ X) → Prop := fun N T =>
    0 < N ∧ ∃ ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ g ∈ T, (ℓ g : ℝ) = N * φ.evalZ g) ∧
      (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → N * φ.evalZ β ≤ ℓ β) ∧
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → N * φ.evalZ β = ℓ β →
        ∃ k : ℕ, 0 < k ∧ k • β ∈ AddSubmonoid.closure (T : Set (LinearMap.BilinForm ℤ X))
  let n : Finset (LinearMap.BilinForm ℤ X) → ℕ := fun T => if hT : ∃ N, Q N T then Nat.find hT else 0
  refine ⟨hS.toFinset.powerset.sup n, fun m ε hε => ?_⟩
  obtain ⟨e, he⟩ := hfin m ε hε
  let ε' : Fin m → LinearMap.BilinForm ℤ X := fun i => pull e.toLinearMap (ε i)
  have hc' : IsCone bar φ ε' := hε.pull_equiv e
  let T : Finset (LinearMap.BilinForm ℤ X) := Finset.univ.image ε'
  have hTS : T ∈ hS.toFinset.powerset := Finset.mem_powerset.2 fun g hg => by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hg
    exact hS.mem_toFinset.2 (he i)
  have hTr : (T : Set (LinearMap.BilinForm ℤ X)) = Set.range ε' := by simp [T]
  have hex : ∃ N, Q N T := by
    obtain ⟨N₀, ℓ₀, hN₀, h1, h2, h3⟩ := hc'.strict
    refine ⟨N₀, hN₀, ℓ₀, fun g hg => ?_, h2, fun β hβ hp heq => ?_⟩
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hg
      exact h1 i
    · obtain ⟨k, c, hk, hc⟩ := h3 β hβ hp heq
      refine ⟨k, hk, ?_⟩
      rw [hTr, hc]
      exact AddSubmonoid.sum_mem _ fun i _ =>
        AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure (Set.mem_range_self i)) _
  have hnT : n T = Nat.find hex := dif_pos hex
  obtain ⟨hN, ℓ', h1, h2, h3⟩ := Nat.find_spec hex
  let P : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X :=
    { toFun := pull e.toLinearMap, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  refine ⟨Nat.find hex, ℓ' ∘ₗ P, hN, hnT ▸ Finset.le_sup hTS, fun i => ?_, fun β hβ hp => ?_, fun β hβ hp heq => ?_⟩
  · have := h1 (ε' i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    rw [evalZ_pull φ e.surjective] at this
    exact this
  · rw [← evalZ_pull φ (r := e.toLinearMap) e.surjective]
    exact h2 _ (pull_mem _ hβ) fun y => hp _
  · rw [← evalZ_pull φ (r := e.toLinearMap) e.surjective] at heq
    obtain ⟨k, hk, hmem⟩ := h3 _ (pull_mem _ hβ) (fun y => hp _) heq
    rw [hTr] at hmem
    obtain ⟨c, hc⟩ := AddSubmonoid.mem_closure_range_iff_of_fintype.1 hmem
    refine ⟨k, c, hk, LinearMap.ext₂ fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := e.surjective a
    obtain ⟨b, rfl⟩ := e.surjective b
    simpa [ε', LinearMap.sum_apply] using LinearMap.congr_fun₂ hc a b

end GlobalTheory.PolFan
