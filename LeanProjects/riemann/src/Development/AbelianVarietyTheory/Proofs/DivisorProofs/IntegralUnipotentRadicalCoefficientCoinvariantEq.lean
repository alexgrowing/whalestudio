import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData
open scoped Topology

noncomputable section

namespace GlobalTheory.UnipCoefInt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def box (a b : ℕ) (s : kˣ) : Set (Fin a → Fin b → k) :=
  Set.univ.pi fun _ => Set.univ.pi fun _ => cball s

theorem mem_box {a b : ℕ} {s : kˣ} {X : Fin a → Fin b → k} :
    X ∈ box a b s ↔ ∀ p q, X p q ∈ cball s := by
  simp [box, Set.mem_univ_pi]

theorem isOpen_box (a b : ℕ) (s : kˣ) : IsOpen (box a b s) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball s

theorem isCompact_box (a b : ℕ) (s : kˣ) : IsCompact (box a b s) :=
  isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_cball s

theorem box_mono {a b : ℕ} {s t : kˣ} (h : valuation k (s : k) ≤ valuation k (t : k)) :
    box a b s ⊆ box a b t := by
  intro X hX
  rw [mem_box] at hX ⊢
  intro p q
  exact le_trans (show valuation k (X p q) ≤ valuation k (s : k) from hX p q) h

theorem add_mem_box_iff {a b : ℕ} {s : kˣ} {X Y : Fin a → Fin b → k} (hY : Y ∈ box a b s) :
    X + Y ∈ box a b s ↔ X ∈ box a b s := by
  rw [mem_box] at hY
  simp only [mem_box, Pi.add_apply]
  constructor
  · intro h p q
    simpa using add_mem_cball (h p q) (neg_mem_cball (hY p q))
  · intro h p q
    exact add_mem_cball (h p q) (hY p q)

theorem exists_mem_box {a b : ℕ} (X : Fin a → Fin b → k) : ∃ s : kˣ, X ∈ box a b s := by
  set γ : ValueGroupWithZero k := ∏ pq : Fin a × Fin b, max 1 (valuation k (X pq.1 pq.2)) with hγ
  have h1 : ∀ pq ∈ (Finset.univ : Finset (Fin a × Fin b)), 1 ≤ max 1 (valuation k (X pq.1 pq.2)) :=
    fun _ _ => le_max_left _ _
  have hγ1 : 1 ≤ γ := Finset.one_le_prod' h1
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective γ
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact absurd (hy ▸ hγ1) (by simp)
  refine ⟨Units.mk0 y hy0, mem_box.mpr fun p q => ?_⟩
  show valuation k (X p q) ≤ valuation k y
  rw [hy]
  exact (le_max_right _ _).trans (Finset.single_le_prod' h1 (Finset.mem_univ (p, q)))

theorem directed_box (a b : ℕ) : Directed (· ⊆ ·) (box (k := k) a b) := by
  intro s t
  rcases le_total (valuation k (s : k)) (valuation k (t : k)) with h | h
  · exact ⟨t, box_mono h, subset_rfl⟩
  · exact ⟨s, subset_rfl, box_mono h⟩

theorem exists_subset_box {a b : ℕ} {K : Set (Fin a → Fin b → k)} (hK : IsCompact K) :
    ∃ s : kˣ, K ⊆ box a b s :=
  hK.elim_directed_cover _ (isOpen_box a b) (fun X _ => Set.mem_iUnion.mpr (exists_mem_box X))
    (directed_box a b)

section Meas
variable [MeasurableSpace k] [BorelSpace k]

theorem main : ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.PRep.IsSmooth π → ∀ (a b : ℕ) (μ : Measure (Fin a → Fin b → k)), μ.IsAddHaarMeasure → ∀ u : (Fin a → Fin b → k) → GL (Fin N) k, Continuous u → (∀ X Y, u (X + Y) = u X * u Y) → ∀ (l : Module.Dual ℂ V) (w : V), w ∈ Submodule.span ℂ {x | ∃ (Y : Fin a → Fin b → k) (y : V), x = π (u Y) y - y} → ∀ F : (Fin a → Fin b → k) → ℂ, HasCompactSupport F → (∀ X, F X = l (π (u X) w)) → ∫ X, F X ∂μ = 0 := by
  intro N V _ _ π hπ a b μ hμ u hu hadd l w hw F hF hFw
  haveI := secondCountable k
  haveI := t2Space k
  haveI : OpensMeasurableSpace (Fin b → k) := inferInstance
  haveI : OpensMeasurableSpace (Fin a → Fin b → k) := inferInstance
  have hu0 : u 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)

  have hcont : ∀ y : V, Continuous fun X => l (π (u X) y) := by
    intro y
    have hlc : IsLocallyConstant fun X => π (u X) y := by
      refine (IsLocallyConstant.iff_eventually_eq _).mpr fun X₀ => ?_
      have hO : IsOpen ((fun X => u (X - X₀)) ⁻¹' {g | π g y = y}) :=
        (hπ y).preimage (hu.comp (continuous_id.sub continuous_const))
      have hX₀ : X₀ ∈ (fun X => u (X - X₀)) ⁻¹' {g | π g y = y} := by
        simp [hu0]
      filter_upwards [hO.mem_nhds hX₀] with X hX
      have hX' : π (u (X - X₀)) y = y := hX
      have e : X = X₀ + (X - X₀) := by abel
      rw [e, hadd, map_mul, Module.End.mul_apply, hX']
    exact (hlc.comp l).continuous
  have hmeas : ∀ s : kˣ, MeasurableSet (box a b s) := fun s => (isOpen_box a b s).measurableSet
  have hint : ∀ (y : V) (s : kˣ), IntegrableOn (fun X => l (π (u X) y)) (box a b s) μ :=
    fun y s => (hcont y).continuousOn.integrableOn_compact (isCompact_box a b s)

  have hshift : ∀ (y : V) (s : kˣ) (Y : Fin a → Fin b → k), Y ∈ box a b s →
      ∫ X in box a b s, l (π (u (X + Y)) y) ∂μ = ∫ X in box a b s, l (π (u X) y) ∂μ := by
    intro y s Y hY
    rw [← integral_indicator (hmeas s), ← integral_indicator (hmeas s)]
    have : ∀ X, (box a b s).indicator (fun X => l (π (u (X + Y)) y)) X =
        (box a b s).indicator (fun X => l (π (u X) y)) (X + Y) := by
      intro X
      by_cases hX : X ∈ box a b s
      · rw [Set.indicator_of_mem hX, Set.indicator_of_mem ((add_mem_box_iff hY).mpr hX)]
      · rw [Set.indicator_of_notMem hX,
          Set.indicator_of_notMem (fun h => hX ((add_mem_box_iff hY).mp h))]
    simp only [this]
    exact integral_add_right_eq_self (μ := μ) (fun X => (box a b s).indicator (fun X => l (π (u X) y)) X) Y

  have key : ∀ w' ∈ Submodule.span ℂ {x | ∃ (Y : Fin a → Fin b → k) (y : V), x = π (u Y) y - y},
      ∃ s₀ : kˣ, ∀ s : kˣ, valuation k (s₀ : k) ≤ valuation k (s : k) →
        ∫ X in box a b s, l (π (u X) w') ∂μ = 0 := by
    intro w' hw'
    induction hw' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨Y, y, rfl⟩ := hx
      obtain ⟨s₀, hs₀⟩ := exists_mem_box Y
      refine ⟨s₀, fun s hs => ?_⟩
      have hY : Y ∈ box a b s := box_mono hs hs₀
      have e : ∀ X, l (π (u X) (π (u Y) y - y)) = l (π (u (X + Y)) y) - l (π (u X) y) := by
        intro X
        rw [map_sub, map_sub, hadd, map_mul, Module.End.mul_apply]
      simp only [e]
      have hi2 : IntegrableOn (fun X => l (π (u (X + Y)) y)) (box a b s) μ :=
        ((hcont y).comp (continuous_id.add continuous_const)).continuousOn.integrableOn_compact (isCompact_box a b s)
      rw [integral_sub hi2 (hint y s), hshift y s Y hY, sub_self]
    | zero => exact ⟨1, fun s _ => by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨s₁, h₁⟩ := hx
      obtain ⟨s₂, h₂⟩ := hz
      rcases le_total (valuation k (s₁ : k)) (valuation k (s₂ : k)) with h | h
      · refine ⟨s₂, fun s hs => ?_⟩
        simp only [map_add]
        rw [integral_add (hint x s) (hint z s), h₁ s (h.trans hs), h₂ s hs, add_zero]
      · refine ⟨s₁, fun s hs => ?_⟩
        simp only [map_add]
        rw [integral_add (hint x s) (hint z s), h₁ s hs, h₂ s (h.trans hs), add_zero]
    | smul c x _ hx =>
      obtain ⟨s₀, h₀⟩ := hx
      refine ⟨s₀, fun s hs => ?_⟩
      simp only [map_smul, smul_eq_mul]
      rw [integral_const_mul, h₀ s hs, mul_zero]
  obtain ⟨s₀, hs₀⟩ := key w hw
  obtain ⟨s₁, hs₁⟩ := exists_subset_box hF
  obtain ⟨s, hs0, hs1⟩ : ∃ s : kˣ, valuation k (s₀ : k) ≤ valuation k (s : k) ∧
      box a b s₁ ⊆ box a b s := by
    rcases le_total (valuation k (s₀ : k)) (valuation k (s₁ : k)) with h | h
    · exact ⟨s₁, h, subset_rfl⟩
    · exact ⟨s₀, le_rfl, box_mono h⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := box a b s)
    (fun X hX => image_eq_zero_of_notMem_tsupport (fun h => hX (hs1 (hs₁ h))))]
  simp only [hFw]
  exact hs₀ s hs0

end Meas

theorem integral_coef_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.PRep.IsSmooth π → ∀ (a b : ℕ) (μ : Measure (Fin a → Fin b → k)), μ.IsAddHaarMeasure → ∀ u : (Fin a → Fin b → k) → GL (Fin N) k, Continuous u → (∀ X Y, u (X + Y) = u X * u Y) → ∀ (l : Module.Dual ℂ V) (w : V), w ∈ Submodule.span ℂ {x | ∃ (Y : Fin a → Fin b → k) (y : V), x = π (u Y) y - y} → ∀ F : (Fin a → Fin b → k) → ℂ, HasCompactSupport F → (∀ X, F X = l (π (u X) w)) → ∫ X, F X ∂μ = 0 := by
  intro k _ _ _ _ _ _
  exact main

end GlobalTheory.UnipCoefInt
