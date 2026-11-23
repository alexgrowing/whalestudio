import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal

namespace GlobalTheory.Twist.ClassSumReindex

theorem tsum_ratClass_eq_tsum_weighted (H : Type) [Group H] (Γ : Subgroup H) (γ : H) (_hγ : γ ∈ Γ)
    (α : H → ℝ≥0∞) (hα : ∀ y, ∑' h : Γ.subgroupOf (cent γ), α (((h : cent γ) : H) * y) = 1)
    (G : H → ℝ≥0∞) (x : H) :
    ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, G (x⁻¹ * δ * x) =
      ∑' g : Γ, α ((g : H) * x) * G (((g : H) * x)⁻¹ * γ * ((g : H) * x)) := by
  classical
  set C := Γ.subgroupOf (cent γ)
  let R := GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ
  let s : R → H := fun δ => Classical.choose δ.2
  have hs : ∀ δ : R, s δ ∈ Γ ∧ (δ : H) = (s δ)⁻¹ * γ * s δ := fun δ => Classical.choose_spec δ.2
  have hcomm : ∀ h : C, ((h : cent γ) : H) * γ = γ * ((h : cent γ) : H) := fun h =>
    (Subgroup.mem_centralizer_singleton_iff).1 (h : cent γ).2
  have hΓ : ∀ h : C, ((h : cent γ) : H) ∈ Γ := fun h => Subgroup.mem_subgroupOf.1 h.2
  have hconj : ∀ (h : C) (δ : R), (((h : cent γ) : H) * s δ)⁻¹ * γ * (((h : cent γ) : H) * s δ) = δ := by
    intro h δ
    rw [(hs δ).2]
    have := hcomm h
    calc (((h : cent γ) : H) * s δ)⁻¹ * γ * (((h : cent γ) : H) * s δ)
        = (s δ)⁻¹ * (((h : cent γ) : H)⁻¹ * (((h : cent γ) : H) * γ)) * s δ := by rw [this]; group
      _ = (s δ)⁻¹ * γ * s δ := by group
  let p : Γ → R := fun g => ⟨(g : H)⁻¹ * γ * g, g, g.2, rfl⟩
  have hq : ∀ g : Γ, (g : H) * (s (p g))⁻¹ ∈ cent γ := by
    intro g
    have h1 := (hs (p g)).2
    change (g : H)⁻¹ * γ * g = (s (p g))⁻¹ * γ * s (p g) at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : γ = (g : H) * ((s (p g))⁻¹ * γ * s (p g)) * (g : H)⁻¹ := by rw [← h1]; group
    calc (g : H) * (s (p g))⁻¹ * γ = (g : H) * ((s (p g))⁻¹ * γ * s (p g)) * (g : H)⁻¹ * ((g : H) * (s (p g))⁻¹) := by
          group
      _ = γ * ((g : H) * (s (p g))⁻¹) := by rw [← h2]
  let e : Γ ≃ R × C :=
    { toFun := fun g => (p g, ⟨⟨(g : H) * (s (p g))⁻¹, hq g⟩,
        Subgroup.mem_subgroupOf.2 (mul_mem g.2 (inv_mem (hs (p g)).1))⟩)
      invFun := fun q => ⟨((q.2 : cent γ) : H) * s q.1, mul_mem (hΓ q.2) (hs q.1).1⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun q => by
        obtain ⟨δ, h⟩ := q
        have hp : p ⟨((h : cent γ) : H) * s δ, mul_mem (hΓ h) (hs δ).1⟩ = δ := Subtype.ext (hconj h δ)
        refine Prod.ext hp (Subtype.ext (Subtype.ext ?_))
        simp only [hp]
        group }
  rw [← e.symm.tsum_eq]
  refine Eq.trans ?_ (ENNReal.tsum_prod (f := fun (δ : R) (h : C) => α (((e.symm (δ, h) : Γ) : H) * x) *
      G ((((e.symm (δ, h) : Γ) : H) * x)⁻¹ * γ * (((e.symm (δ, h) : Γ) : H) * x)))).symm
  refine tsum_congr fun δ => ?_
  have key : ∀ h : C, α (((e.symm (δ, h) : Γ) : H) * x) *
      G ((((e.symm (δ, h) : Γ) : H) * x)⁻¹ * γ * (((e.symm (δ, h) : Γ) : H) * x)) =
      α (((h : cent γ) : H) * (s δ * x)) * G (x⁻¹ * δ * x) := by
    intro h
    change α (((h : cent γ) : H) * s δ * x) * G ((((h : cent γ) : H) * s δ * x)⁻¹ * γ * (((h : cent γ) : H) * s δ * x)) = _
    rw [mul_assoc ((h : cent γ) : H) (s δ) x]
    congr 1
    congr 1
    rw [← hconj h δ]
    group
  rw [tsum_congr key, ENNReal.tsum_mul_right, hα, one_mul]

end GlobalTheory.Twist.ClassSumReindex
