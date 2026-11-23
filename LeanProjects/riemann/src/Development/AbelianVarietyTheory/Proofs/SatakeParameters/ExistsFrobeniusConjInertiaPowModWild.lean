import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws

noncomputable section

namespace GlobalTheory.TameRel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem wild_conj {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {s u : G E Ω} (hs : s ∈ Dec (F := E) A)
    (hu : ∀ y : Ω, y ≠ 0 → A.valuation (u y / y - 1) < 1) :
    ∀ y : Ω, y ≠ 0 → A.valuation ((s * u * s⁻¹) y / y - 1) < 1 := by
  intro y hy
  set z := (s⁻¹ : G E Ω) y with hz
  have hsz : s z = y := mul_inv_apply y
  have hz0 : z ≠ 0 := by
    intro h; apply hy; rw [← hsz, h, map_zero]
  have e : (s * u * s⁻¹) y / y - 1 = s (u z / z - 1) := by
    rw [map_sub, map_div₀, map_one, hsz]
    rfl
  rw [e, GlobalTheory.TameLabels.valuation_apply_of_mem_Dec hs]
  exact hu z hz0

end GlobalTheory.TameRel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem GlobalTheory.TameRel.main : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (k : Fin 2) (v : N.PlG k), ∀ γ ∈ Ine (F := H.E) (N.plOm.1 (A.plGw k v)), ∃ φ : G H.E N.Om, φ * γ * φ⁻¹ * (γ ^ H.g k)⁻¹ ∈ Ine (F := H.E) (N.plOm.1 (A.plGw k v)) ∧ φ * γ * φ⁻¹ * (γ ^ H.g k)⁻¹ ∈ wildSet N (N.plOm.1 (A.plGw k v)) := by
  intro R H what₂ N A k v γ hγ
  obtain ⟨φ, hφ⟩ := exists_isFrob (N.plOm.2 (A.plGw k v))
  rw [GlobalTheory.TameLabels.normV_eq_of_split (H.g_prime k) (N.g_split k) (A.plGw_over k v)] at hφ
  refine ⟨φ, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (conj_mem_Ine hφ.1 hγ) (Subgroup.inv_mem _ (Subgroup.pow_mem _ hγ _))
  · have hu := GlobalTheory.TameLabels.wild_of_frob hγ hφ
    have hs : γ ^ H.g k ∈ Dec (F := H.E) (N.plOm.1 (A.plGw k v)) :=
      (Dec (F := H.E) _).pow_mem (Ine_le_Dec _ hγ) _
    have h := GlobalTheory.TameRel.wild_conj hs hu
    have e : γ ^ H.g k * ((γ ^ H.g k)⁻¹ * (φ * γ * φ⁻¹)) * (γ ^ H.g k)⁻¹ = φ * γ * φ⁻¹ * (γ ^ H.g k)⁻¹ := by
      group
    rw [e] at h
    exact h
