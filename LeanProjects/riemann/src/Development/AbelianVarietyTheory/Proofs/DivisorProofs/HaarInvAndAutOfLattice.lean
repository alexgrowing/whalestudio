import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSemiMeasOfCovolOne
open MeasureTheory

namespace GlobalTheory.LatticeHaar

theorem haar_inv_and_aut_of_lattice : ∀ {N : Type} [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N] [SecondCountableTopology N] [T2Space N]
    [MeasurableSpace N] [BorelSpace N] (ν : Measure N) [ν.IsHaarMeasure] (Λ : Subgroup N) [Countable Λ] (𝓕 : Set N),
    IsFundamentalDomain Λ 𝓕 ν → ν 𝓕 ≠ 0 → ν 𝓕 ≠ ⊤ →
    MeasurePreserving (fun u : N => u⁻¹) ν ν ∧
      ∀ α : N ≃* N, Continuous α → Continuous α.symm → (∀ x, α x ∈ Λ ↔ x ∈ Λ) → MeasurePreserving α ν ν := by
  intro N _ _ _ _ _ _ _ _ ν _ Λ _ 𝓕 h𝓕 _ hfin
  haveI := GlobalTheory.SemiHaar.rightInv_of_fd Λ ν h𝓕 hfin
  haveI := GlobalTheory.SemiHaar.invInv_of_rightInv ν
  refine ⟨⟨measurable_inv, ?_⟩, ?_⟩
  · exact Measure.map_inv_eq_self ν
  · intro α hα hαs hΛ
    let φ : N ≃ₜ N := { toEquiv := α.toEquiv, continuous_toFun := hα, continuous_invFun := hαs }
    haveI : (ν.map φ).IsHaarMeasure := α.isHaarMeasure_map ν hα hαs
    let e : Λ → Λ := fun g => ⟨α.symm g, (hΛ (α.symm g)).1 (by simp)⟩
    have he : Function.Bijective e := by
      refine ⟨fun a b h => ?_, fun b => ⟨⟨α b, (hΛ b).2 b.2⟩, by ext; simp [e]⟩⟩
      have : α.symm (a : N) = α.symm b := congrArg Subtype.val h
      exact Subtype.ext (α.symm.injective this)
    have hφ : ∀ (g : Λ) (x : N), φ ((e g).1 * x) = g.1 * φ x := by
      intro g x; simp [φ, e, map_mul]
    have hm := GlobalTheory.SemiHaar.map_eq_self_of_fd Λ ν h𝓕 hfin φ e he hφ
    exact ⟨hα.measurable, hm⟩

end GlobalTheory.LatticeHaar
