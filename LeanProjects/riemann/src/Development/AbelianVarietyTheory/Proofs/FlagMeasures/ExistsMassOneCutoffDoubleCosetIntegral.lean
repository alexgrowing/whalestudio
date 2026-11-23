import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableLintegralCosetEqOneClosedSubgrouStatement

open MeasureTheory

namespace GlobalTheory.StabUnfold

open MeasureTheory in
open scoped ENNReal in

theorem _root_.GlobalTheory.StabUnfold.exists_cutoff_doubleCoset : ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (j : H →* G), Topology.IsClosedEmbedding j → ∀ (K : Subgroup G) (K' : Subgroup H) (x : G) (S : Set G), IsOpen (K : Set G) → IsOpen (K' : Set H) → IsCompact (K' : Set H) → (∀ h, h ∈ K' ↔ x⁻¹ * j h * x ∈ K) → (∀ g, g ∈ S ↔ ∃ h, ∃ k ∈ K, g = j h * x * k) → ∃ b : G → ENNReal, Measurable b ∧ (∀ g, ∫⁻ h, b (j h * g) ∂ν = 1) ∧ ∫⁻ g, S.indicator 1 g * b g ∂μ = μ K / ν K' := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ _ j hj K K' x S hK hK'o hK'c hK'K hS
  obtain ⟨b₀, hb₀m, hb₀⟩ := _root_.GlobalTheory.exists_measurable_lintegral_coset_eq_one G H ν j hj
  have hSeq : S = ⋃ h : H, (fun g => j h * x * g) '' (K : Set G) := by
    ext g
    rw [hS g]
    simp only [Set.mem_iUnion, Set.mem_image, SetLike.mem_coe]
    constructor <;> rintro ⟨h, k, hk, e⟩ <;> exact ⟨h, k, hk, e.symm⟩
  have hSopen : IsOpen S := by
    rw [hSeq]
    exact isOpen_iUnion fun h => isOpenMap_mul_left (j h * x) _ hK
  have hSm : MeasurableSet S := hSopen.measurableSet
  set T : Set G := (fun g => x⁻¹ * g) ⁻¹' (K : Set G) with hT_def
  have hTm : MeasurableSet T := measurable_const_mul x⁻¹ hK.measurableSet
  have hc0 : ν K' ≠ 0 := (hK'o.measure_pos ν ⟨1, K'.one_mem⟩).ne'
  have hcT : ν K' ≠ ∞ := hK'c.measure_lt_top.ne
  have hSinv : ∀ h g, j h * g ∈ S ↔ g ∈ S := by
    intro h g
    rw [hS, hS]
    constructor
    · rintro ⟨h', k, hk, e⟩
      refine ⟨h⁻¹ * h', k, hk, ?_⟩
      have e' : g = (j h)⁻¹ * (j h' * x * k) := by rw [← e]; group
      rw [e', map_mul, map_inv]; group
    · rintro ⟨h', k, hk, e⟩
      exact ⟨h * h', k, hk, by rw [e, map_mul]; group⟩
  have hTS : ∀ g, g ∈ T → g ∈ S := by
    intro g hg
    rw [hS]
    exact ⟨1, x⁻¹ * g, hg, by simp⟩
  have hcoset : ∀ g ∈ S, ∫⁻ h, T.indicator (fun _ => (ν K')⁻¹) (j h * g) ∂ν = 1 := by
    intro g hg
    obtain ⟨h0, k, hk, rfl⟩ := (hS g).1 hg
    have e : ∀ h, T.indicator (fun _ => (ν K')⁻¹) (j h * (j h0 * x * k))
        = (K' : Set H).indicator (fun _ => (ν K')⁻¹) (h * h0) := by
      intro h
      have hiff : j h * (j h0 * x * k) ∈ T ↔ h * h0 ∈ (K' : Set H) := by
        show x⁻¹ * (j h * (j h0 * x * k)) ∈ K ↔ h * h0 ∈ K'
        rw [hK'K, map_mul]
        have e2 : x⁻¹ * (j h * (j h0 * x * k)) = x⁻¹ * (j h * j h0) * x * k := by group
        rw [e2, Subgroup.mul_mem_cancel_right _ hk]
      by_cases hm : h * h0 ∈ (K' : Set H)
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hiff.2 hm)]
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (mt hiff.1 hm)]
    calc ∫⁻ h, T.indicator (fun _ => (ν K')⁻¹) (j h * (j h0 * x * k)) ∂ν
        = ∫⁻ h, (K' : Set H).indicator (fun _ => (ν K')⁻¹) (h * h0) ∂ν := lintegral_congr e
      _ = ∫⁻ h, (K' : Set H).indicator (fun _ => (ν K')⁻¹) h ∂ν :=
          lintegral_mul_right_eq_self (fun h => (K' : Set H).indicator (fun _ => (ν K')⁻¹) h) h0
      _ = 1 := by rw [lintegral_indicator_const hK'o.measurableSet, ENNReal.inv_mul_cancel hc0 hcT]
  have hzero : ∀ g, g ∉ S → ∫⁻ h, T.indicator (fun _ => (ν K')⁻¹) (j h * g) ∂ν = 0 := by
    intro g hg
    have e : ∀ h, T.indicator (fun _ => (ν K')⁻¹) (j h * g) = 0 := fun h =>
      Set.indicator_of_notMem (fun hT => hg ((hSinv h g).1 (hTS _ hT))) _
    simp [e]
  have hjg : ∀ g, Measurable fun h => j h * g := fun g => hj.continuous.measurable.mul_const g
  refine ⟨fun g => T.indicator (fun _ => (ν K')⁻¹) g + Sᶜ.indicator b₀ g,
    (measurable_const.indicator hTm).add (hb₀m.indicator hSm.compl), fun g => ?_, ?_⟩
  · dsimp only
    rw [lintegral_add_left (show Measurable fun h => T.indicator (fun _ => (ν K')⁻¹) (j h * g)
      from (measurable_const.indicator hTm).comp (hjg g))]
    by_cases hg : g ∈ S
    · have e : ∀ h, Sᶜ.indicator b₀ (j h * g) = 0 := fun h =>
        Set.indicator_of_notMem (show j h * g ∉ Sᶜ from fun hc => hc ((hSinv h g).2 hg)) _
      simp only [e, lintegral_zero, add_zero]
      exact hcoset g hg
    · have e : ∀ h, Sᶜ.indicator b₀ (j h * g) = b₀ (j h * g) := fun h =>
        Set.indicator_of_mem (show j h * g ∈ Sᶜ from fun hs => hg ((hSinv h g).1 hs)) _
      rw [hzero g hg, zero_add]
      simp only [e]
      exact hb₀ g
  · have e : ∀ g, S.indicator 1 g * (T.indicator (fun _ => (ν K')⁻¹) g + Sᶜ.indicator b₀ g)
        = T.indicator (fun _ => (ν K')⁻¹) g := by
      intro g
      by_cases hg : g ∈ S
      · simp [hg]
      · have hgT : g ∉ T := fun hT => hg (hTS g hT)
        simp [hg, hgT]
    rw [lintegral_congr e, lintegral_indicator_const hTm, hT_def, measure_preimage_mul,
      ENNReal.div_eq_inv_mul]

end GlobalTheory.StabUnfold
