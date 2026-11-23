import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageMapLatticeEquivStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageProdFubiniStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

def sumArrowAddHomeo (A ι κ : Type) [AddCommGroup A] [TopologicalSpace A] :
    ((ι → A) × (κ → A)) ≃ₜ+ (ι ⊕ κ → A) where
  toFun p := Sum.elim p.1 p.2
  invFun f := (fun i => f (Sum.inl i), fun j => f (Sum.inr j))
  left_inv _ := rfl
  right_inv f := by ext (i | j) <;> rfl
  map_add' p q := by ext (i | j) <;> rfl
  continuous_toFun := by
    refine continuous_pi fun s => ?_
    rcases s with i | j
    · exact (continuous_apply i).comp continuous_fst
    · exact (continuous_apply j).comp continuous_snd
  continuous_invFun :=
    (continuous_pi fun i => continuous_apply _).prodMk (continuous_pi fun j => continuous_apply _)

theorem sum_elim_mem_ratV (E : Type) [Field E] [NumberField E] (ι κ : Type) (x : ι → Ad E) (y : κ → Ad E) :
    Sum.elim x y ∈ ratV E (ι ⊕ κ) ↔ x ∈ ratV E ι ∧ y ∈ ratV E κ := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨⟨fun i => c (Sum.inl i), funext fun i => congrFun hc (Sum.inl i)⟩,
      ⟨fun j => c (Sum.inr j), funext fun j => congrFun hc (Sum.inr j)⟩⟩
  · rintro ⟨⟨c, rfl⟩, ⟨d, rfl⟩⟩
    refine ⟨Sum.elim c d, funext fun s => ?_⟩
    rcases s with i | j <;> rfl

theorem avg_sum_index : ∀ (E : Type) [Field E] [NumberField E] (ι κ : Type) [Fintype ι] [Fintype κ]
    (Φ : (ι ⊕ κ → Ad E) → ℂ), Per (ratV E (ι ⊕ κ)) Φ →
    avg (ratV E (ι ⊕ κ)) Φ = avg (ratV E ι) (fun x => avg (ratV E κ) (fun y => Φ (Sum.elim x y))) := by
  intro E _ _ ι κ _ _ Φ hΦ
  have hι := isCoLat_ratV E ι
  have hκ := isCoLat_ratV E κ
  have hs := isCoLat_ratV E (ι ⊕ κ)
  have hp : IsCoLat ((ratV E ι).prod (ratV E κ)) := by
    obtain ⟨d₁, K₁, hK₁, c₁⟩ := hι
    obtain ⟨d₂, K₂, hK₂, c₂⟩ := hκ
    refine ⟨?_, K₁ ×ˢ K₂, hK₁.prod hK₂, fun x => ?_⟩
    · let f : ↥((ratV E ι).prod (ratV E κ)) → ratV E ι × ratV E κ := fun p => (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
      have hf : Continuous f :=
        (continuous_subtype_val.fst.subtype_mk _).prodMk (continuous_subtype_val.snd.subtype_mk _)
      refine DiscreteTopology.of_continuous_injective hf fun p q h => ?_
      have e₁ := congrArg (fun r => (r.1 : ι → Ad E)) h
      have e₂ := congrArg (fun r => (r.2 : κ → Ad E)) h
      exact Subtype.ext (Prod.ext e₁ e₂)
    · obtain ⟨γ₁, m₁, k₁⟩ := c₁ x.1
      obtain ⟨γ₂, m₂, k₂⟩ := c₂ x.2
      exact ⟨(γ₁, γ₂), ⟨m₁, m₂⟩, k₁, k₂⟩
  let e := sumArrowAddHomeo (Ad E) ι κ
  have he : ∀ p, e p ∈ ratV E (ι ⊕ κ) ↔ p ∈ (ratV E ι).prod (ratV E κ) := fun p =>
    (sum_elim_mem_ratV E ι κ p.1 p.2).trans AddSubgroup.mem_prod.symm
  have hper : Per ((ratV E ι).prod (ratV E κ)) (fun p => Φ (e p)) := by
    refine ⟨hΦ.1.comp e.continuous_toFun, fun γ hγ x => ?_⟩
    have : e (γ + x) = e γ + e x := map_add e γ x
    simp only [this]
    exact hΦ.2 _ ((he γ).2 hγ) _
  have h1 := GlobalTheory.T.quotientAverage_map_lattice_equiv _ _ _ _ hp hs e he Φ hΦ
  have h2 := GlobalTheory.T.quotientAverage_prod_fubini _ _ _ _ hι hκ _ hper
  rw [← h1, h2]
  rfl

end GlobalTheory.CuspGeneric
