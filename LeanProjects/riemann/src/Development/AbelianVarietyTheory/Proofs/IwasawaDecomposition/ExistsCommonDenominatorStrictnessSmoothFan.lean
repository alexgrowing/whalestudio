import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdConeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearFormFromFinsupp
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

noncomputable section

namespace GlobalTheory.PolCell

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X X₁ : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] {m : ℕ}

theorem StrictWith.mul {N t : ℕ} (ht : 0 < t) {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    {u : Fin m → LinearMap.BilinForm ℤ X} (h : StrictWith bar φ N ℓ u) :
    StrictWith bar φ (t * N) ((t : ℤ) • ℓ) u := by
  obtain ⟨h1, h2, h3⟩ := h
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  refine ⟨fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => h3 β hβ hp ?_⟩
  · simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast, h1 i, Nat.cast_mul]; ring
  · have := mul_le_mul_of_nonneg_left (h2 β hβ hp) ht'.le
    simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    linarith
  · simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] at he
    have : (t : ℝ) * (N * φ.evalZ β) = t * ℓ β := by linarith
    exact mul_left_cancel₀ ht'.ne' this

theorem StrictWith.of_pull {N : ℕ} {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    {u : Fin m → LinearMap.BilinForm ℤ X₁} (h : StrictWith bar φ N ℓ fun i => pull r (u i)) :
    StrictWith bar φ N (ℓ ∘ₗ { toFun := pull r, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }) u := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun i => (h1 i).trans (by rw [evalZ_pull φ hr]), fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
  · rw [← evalZ_pull φ hr]
    exact h2 _ (pull_mem r hβ) fun y => hp _
  · rw [← evalZ_pull φ hr] at he
    obtain ⟨k, c, hk, hc⟩ := h3 _ (pull_mem r hβ) (fun y => hp _) he
    refine ⟨k, c, hk, LinearMap.ext₂ fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := hr a
    obtain ⟨b, rfl⟩ := hr b
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hc a b

end GlobalTheory.PolCell

open Classical in

theorem GlobalTheory.PolCell.exists_common_den : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (φ : InvFun ℤ),
    IsPolFanOn (id : ℤ → ℤ) φ X → ∃ N : ℕ, 0 < N ∧ ∀ B ∈ psdCone (id : ℤ → ℤ) X, ∃ (m : ℕ)
      (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ), IsCone (id : ℤ → ℤ) φ u ∧
      StrictWith (id : ℤ → ℤ) φ N (linW w) u ∧ B ∈ rcone u := by
  intro X _ _ φ hφ
  obtain ⟨S, hS, hSc⟩ := hφ.finite
  haveI : Finite S := hS.to_subtype
  let K := Σ m : Fin (Nat.card S + 1), (Fin m → S)
  haveI : Fintype K := Fintype.ofFinite K
  let D : K → ℕ := fun k =>
    if h : IsCone (id : ℤ → ℤ) φ (fun i => ((k.2 i : S) : LinearMap.BilinForm ℤ X)) then Classical.choose h.strict else 1
  have hD : ∀ k, 0 < D k := fun k => by
    simp only [D]
    split_ifs with h
    · exact (Classical.choose_spec (Classical.choose_spec h.strict)).1
    · exact one_pos
  refine ⟨∏ k, D k, Finset.prod_pos fun k _ => hD k, fun B hB => ?_⟩
  obtain ⟨m, γ, c, hγ, hc, rfl⟩ := hφ.cover B hB
  obtain ⟨e, he⟩ := hSc m γ hγ
  have hγ' := hγ.pull_equiv e
  have hm : m < Nat.card S + 1 := by
    have := Nat.card_le_card_of_injective (fun i : Fin m => (⟨_, he i⟩ : S))
      (fun i j h => hγ'.injective (congrArg Subtype.val h))
    rw [Nat.card_fin] at this
    exact Nat.lt_succ_of_le this
  let k : K := ⟨⟨m, hm⟩, fun i => ⟨_, he i⟩⟩
  have hk : IsCone (id : ℤ → ℤ) φ (fun i => ((k.2 i : S) : LinearMap.BilinForm ℤ X)) := hγ'
  have hDk : D k = Classical.choose hk.strict := dif_pos hk
  obtain ⟨ℓ, -, hℓ⟩ := Classical.choose_spec hk.strict
  obtain ⟨t, ht⟩ : D k ∣ ∏ k, D k := Finset.dvd_prod_of_mem D (Finset.mem_univ k)
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · have := Finset.prod_pos fun k (_ : k ∈ Finset.univ) => hD k
      rw [ht, h, mul_zero] at this; exact absurd this (lt_irrefl 0)
    · exact h
  have h1 : StrictWith (id : ℤ → ℤ) φ (t * D k) ((t : ℤ) • ℓ) fun i => pull e.toLinearMap (γ i) := by
    rw [hDk]; exact StrictWith.mul ht0 hℓ
  have h2 := StrictWith.of_pull e.surjective h1
  obtain ⟨w, hw⟩ := exists_linW_eq X (((t : ℤ) • ℓ) ∘ₗ
    { toFun := pull e.toLinearMap, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl })
  refine ⟨m, γ, w, hγ, ?_, c, hc, rfl⟩
  rw [hw, ht, mul_comm]
  exact h2
