import Mathlib
import Formalism.PeriodIntegrals.FoldMult

open MeasureTheory
open scoped ENNReal NNReal

namespace PI.FoldMult.UnitaryGroupMassFormula

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

def cnt (Γ : Subgroup G) (Ω : Set G) (x y : G) : Set Γ := {γ : Γ | x⁻¹ * ((γ : G) * y) ∈ Ω}

theorem cnt_encard_le (Γ : Subgroup G) [DiscreteTopology Γ] (Ω : Set G) (hΩ : IsCompact Ω)
    (x : G) : ∃ N : ℕ∞, N < ⊤ ∧ ∀ y, (cnt Γ Ω x y).encard ≤ N := by
  set K : Set G := (fun p : G × G => x * p.1 * (x * p.2)⁻¹) '' (Ω ×ˢ Ω) with hKdef
  have hK : IsCompact K := (hΩ.prod hΩ).image (by fun_prop)
  have hS : ((Subtype.val : Γ → G) ⁻¹' K).Finite :=
    ((Subgroup.isClosed_of_discrete (H := Γ)).isClosedEmbedding_subtypeVal.isCompact_preimage hK).finite_of_discrete
  refine ⟨((Subtype.val : Γ → G) ⁻¹' K).encard, hS.encard_lt_top, fun y => ?_⟩
  rcases (cnt Γ Ω x y).eq_empty_or_nonempty with h | ⟨γ₀, hγ₀⟩
  · rw [h, Set.encard_empty]
    exact zero_le
  · refine le_trans (Set.encard_le_encard (t := (fun δ : Γ => δ * γ₀) '' ((Subtype.val : Γ → G) ⁻¹' K)) ?_)
      (Set.encard_image_le _ _)
    intro γ hγ
    refine ⟨γ * γ₀⁻¹, ?_, by simp⟩
    refine ⟨(x⁻¹ * ((γ : G) * y), x⁻¹ * ((γ₀ : G) * y)), ⟨hγ, hγ₀⟩, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group

theorem one_le_mult (Γ : Subgroup G) (Ω : Set G) (h1 : (1 : G) ∈ Ω) (x : G) :
    1 ≤ Formalism.L2.SG.FoldBound.mult Γ Ω x := by
  unfold Formalism.L2.SG.FoldBound.mult
  refine le_iSup_of_le x ?_
  have h : (1 : ℕ∞) ≤ ({γ : Γ | x⁻¹ * ((γ : G) * x) ∈ Ω} : Set Γ).encard :=
    Set.one_le_encard_iff_nonempty.2 ⟨1, by simpa using h1⟩
  exact_mod_cast h

theorem mult_lt_top (Γ : Subgroup G) [DiscreteTopology Γ] (Ω : Set G) (hΩ : IsCompact Ω)
    (x : G) : Formalism.L2.SG.FoldBound.mult Γ Ω x < ⊤ := by
  obtain ⟨N, hN, hle⟩ := cnt_encard_le Γ Ω hΩ x
  exact lt_of_le_of_lt (b := (N : ℝ≥0∞)) (iSup_le fun y => ENat.toENNReal_le.2 (hle y))
    (ENat.toENNReal_lt_top.2 hN)

theorem mult_mul_left (Γ : Subgroup G) (Ω : Set G) (γ : G) (hγ : γ ∈ Γ) (x : G) :
    Formalism.L2.SG.FoldBound.mult Γ Ω (γ * x) = Formalism.L2.SG.FoldBound.mult Γ Ω x := by
  unfold Formalism.L2.SG.FoldBound.mult
  refine iSup_congr fun y => ?_
  have hs : ({δ : Γ | (γ * x)⁻¹ * ((δ : G) * y) ∈ Ω} : Set Γ) =
      (fun ε : Γ => (⟨γ, hγ⟩ : Γ) * ε) '' {ε : Γ | x⁻¹ * ((ε : G) * y) ∈ Ω} := by
    ext δ
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro hδ
      refine ⟨(⟨γ, hγ⟩ : Γ)⁻¹ * δ, ?_, by simp⟩
      simpa [mul_assoc] using hδ
    · rintro ⟨ε, hε, rfl⟩
      simpa [mul_assoc] using hε
  rw [hs, Set.InjOn.encard_image (mul_right_injective _).injOn]

def hitSet (Γ : Subgroup G) (Ω : Set G) (A : Finset Γ) : Set G :=
  {x | ∃ y : G, ∀ a ∈ A, x⁻¹ * ((a : G) * y) ∈ Ω}

theorem isClosed_hitSet (Γ : Subgroup G) (Ω : Set G) (hΩ : IsCompact Ω) (A : Finset Γ) :
    IsClosed (hitSet Γ Ω A) := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · convert isClosed_univ
    ext x
    simp [hitSet]
  · have hΩc : IsClosed Ω := hΩ.isClosed
    have : CompactSpace Ω := isCompact_iff_compactSpace.1 hΩ
    have hC : IsClosed {p : G × Ω | ∀ a ∈ A, p.1⁻¹ * ((a : G) * ((a₀ : G)⁻¹ * (p.1 * (p.2 : G)))) ∈ Ω} := by
      have hI : {p : G × Ω | ∀ a ∈ A, p.1⁻¹ * ((a : G) * ((a₀ : G)⁻¹ * (p.1 * (p.2 : G)))) ∈ Ω} =
          ⋂ a ∈ A, (fun p : G × Ω => p.1⁻¹ * ((a : G) * ((a₀ : G)⁻¹ * (p.1 * (p.2 : G))))) ⁻¹' Ω := by
        ext p
        simp
      rw [hI]
      exact isClosed_biInter fun a _ => hΩc.preimage (by fun_prop)
    have hEq : hitSet Γ Ω A =
        Prod.fst '' {p : G × Ω | ∀ a ∈ A, p.1⁻¹ * ((a : G) * ((a₀ : G)⁻¹ * (p.1 * (p.2 : G)))) ∈ Ω} := by
      ext x
      constructor
      · rintro ⟨y, hy⟩
        refine ⟨(x, ⟨x⁻¹ * ((a₀ : G) * y), hy a₀ ha₀⟩), fun a ha => ?_, rfl⟩
        simpa [mul_assoc] using hy a ha
      · rintro ⟨p, hp, rfl⟩
        exact ⟨(a₀ : G)⁻¹ * (p.1 * (p.2 : G)), hp⟩
    rw [hEq]
    exact isClosedMap_fst_of_compactSpace _ hC

theorem mult_eq_iSup (Γ : Subgroup G) [DiscreteTopology Γ] (Ω : Set G) (hΩ : IsCompact Ω)
    (x : G) : Formalism.L2.SG.FoldBound.mult Γ Ω x =
      ⨆ A : Finset Γ, (hitSet Γ Ω A).indicator (fun _ => (A.card : ℝ≥0∞)) x := by
  obtain ⟨N, hN, hle⟩ := cnt_encard_le Γ Ω hΩ x
  unfold Formalism.L2.SG.FoldBound.mult
  apply le_antisymm
  · refine iSup_le fun y => ?_
    have hfin : (cnt Γ Ω x y).Finite := Set.encard_lt_top_iff.1 ((hle y).trans_lt hN)
    refine le_iSup_of_le hfin.toFinset ?_
    have hx : x ∈ hitSet Γ Ω hfin.toFinset := ⟨y, fun a ha => hfin.mem_toFinset.1 ha⟩
    rw [Set.indicator_of_mem hx]
    change ((cnt Γ Ω x y).encard : ℝ≥0∞) ≤ (hfin.toFinset.card : ℝ≥0∞)
    exact le_of_eq (by rw [hfin.encard_eq_coe_toFinset_card, ENat.toENNReal_coe])
  · refine iSup_le fun B => ?_
    by_cases hx : x ∈ hitSet Γ Ω B
    · obtain ⟨y, hy⟩ := hx
      rw [Set.indicator_of_mem (show x ∈ hitSet Γ Ω B from ⟨y, hy⟩)]
      refine le_iSup_of_le y ?_
      have hsub : (B : Set Γ) ⊆ cnt Γ Ω x y := fun a ha => hy a ha
      have hc := Set.encard_le_encard hsub
      rw [Set.encard_coe_eq_coe_finsetCard] at hc
      show (B.card : ℝ≥0∞) ≤ _
      rw [← ENat.toENNReal_coe]
      exact ENat.toENNReal_le.2 hc
    · rw [Set.indicator_of_notMem hx]
      exact zero_le

theorem measurable_mult [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] (Ω : Set G) (hΩ : IsCompact Ω) :
    Measurable (Formalism.L2.SG.FoldBound.mult Γ Ω) := by
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hm : Formalism.L2.SG.FoldBound.mult Γ Ω =
      fun x => ⨆ A : Finset Γ, (hitSet Γ Ω A).indicator (fun _ => (A.card : ℝ≥0∞)) x :=
    funext (mult_eq_iSup Γ Ω hΩ)
  rw [hm]
  exact Measurable.iSup fun A => measurable_const.indicator (isClosed_hitSet Γ Ω hΩ A).measurableSet

end PI.FoldMult.UnitaryGroupMassFormula
