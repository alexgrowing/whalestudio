import Mathlib

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace Formalism.L2.SG.FoldBound

def mult {G : Type*} [Group G] (Γ : Subgroup G) (Ω : Set G) (x : G) : ℝ≥0∞ :=
  ⨆ y : G, ((({γ : Γ | x⁻¹ * ((γ : G) * y) ∈ Ω} : Set Γ).encard : ℕ∞) : ℝ≥0∞)

def IsRightTransversal {G : Type*} [Group G] (Γ S : Subgroup G) (D : Set G) : Prop :=
  D ⊆ (Γ : Set G) ∧ ∀ γ ∈ Γ, ∃! p : S × D, ((p.1 : G) * (p.2 : G)) = γ

def quotientLIntegral {G : Type*} [MeasurableSpace G] (μ : Measure G) (F : Set G) (Ph : G → ℂ) : ℝ≥0∞ :=
  ∫⁻ y in F, ‖Ph y‖ₑ ∂μ

set_option linter.dupNamespace false in

def FoldBound (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] : Prop :=
  ∀ (Γ S : Subgroup G), DiscreteTopology Γ → S ≤ Γ →
  ∀ (Ω : Set G), MeasurableSet Ω →
  ∀ (a : ℝ≥0) (Ph : G → ℂ), Measurable Ph →
    (∀ s ∈ S, ∀ y : G, Ph (s * y) = Ph y) →
    (∀ y : G, ‖Ph y‖ₑ ≤ (a : ℝ≥0∞) * ∫⁻ ω in Ω, ‖Ph (y * ω)‖ₑ ∂μ) →
  ∀ (F : Set G), IsFundamentalDomain S F μ →
  ∀ (D : Set G), IsRightTransversal Γ S D →
  ∀ x : G,
    ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ ≤ (a : ℝ≥0∞) * mult Γ Ω x * quotientLIntegral μ F Ph

theorem tsum_transversal {G : Type*} [Group G] (Γ S : Subgroup G) (hSΓ : S ≤ Γ) (D : Set G)
    (hD : IsRightTransversal Γ S D) (φ : G → ℝ≥0∞) :
    ∑' δ : D, ∑' s : S, φ ((δ : G)⁻¹ * (s : G)) = ∑' γ : Γ, φ (γ : G) := by
  classical
  have hmem : ∀ (δ : D) (s : S), (δ : G)⁻¹ * (s : G) ∈ Γ := fun δ s =>
    Γ.mul_mem (Γ.inv_mem (hD.1 δ.2)) (hSΓ s.2)
  let f : D × S → Γ := fun p => ⟨(p.1 : G)⁻¹ * (p.2 : G), hmem p.1 p.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨δ, s⟩ ⟨δ', s'⟩ h
      have h' : (δ : G)⁻¹ * (s : G) = (δ' : G)⁻¹ * (s' : G) := congrArg Subtype.val h
      have hγ : (s : G)⁻¹ * (δ : G) ∈ Γ := Γ.mul_mem (Γ.inv_mem (hSΓ s.2)) (hD.1 δ.2)
      obtain ⟨p, -, hp⟩ := hD.2 _ hγ
      have e1 := hp (s⁻¹, δ) (by simp)
      have h'' : (s' : G)⁻¹ * (δ' : G) = (s : G)⁻¹ * (δ : G) := by
        have := congrArg (·⁻¹) h'
        simp only [mul_inv_rev, inv_inv] at this
        exact this.symm
      have e2 := hp (s'⁻¹, δ') (by simpa using h'')
      have := e1.trans e2.symm
      simp only [Prod.mk.injEq, inv_inj] at this
      obtain ⟨rfl, rfl⟩ := this
      rfl
    · rintro ⟨γ, hγ⟩
      obtain ⟨p, hp, -⟩ := hD.2 _ (Γ.inv_mem hγ)
      refine ⟨(p.2, p.1⁻¹), Subtype.ext ?_⟩
      simp only [f, Subgroup.coe_inv]
      rw [← mul_inv_rev, hp, inv_inv]
  rw [← ENNReal.tsum_prod]
  exact (Equiv.ofBijective f hf).tsum_eq (fun γ : Γ => φ (γ : G))

theorem foldBound_holds (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] : FoldBound G μ := by
  intro Γ S hΓ hSΓ Ω hΩ a Ph hPh hS hbd F hF D hD x
  classical
  haveI := hΓ
  haveI : Countable Γ := by
    obtain ⟨s, hs, hd⟩ := TopologicalSpace.exists_countable_dense Γ
    have hu : s = Set.univ := by
      have := hd.closure_eq
      rwa [closure_discrete] at this
    rw [hu] at hs
    exact Set.countable_univ_iff.mp hs
  haveI : Countable D := ((Set.countable_range ((↑) : Γ → G)).mono
    (show D ⊆ Set.range ((↑) : Γ → G) from fun y hy => ⟨⟨y, hD.1 hy⟩, rfl⟩)).to_subtype
  haveI : Countable S := ((Set.countable_range ((↑) : Γ → G)).mono
    (show (S : Set G) ⊆ Set.range ((↑) : Γ → G) from fun y hy => ⟨⟨y, hSΓ hy⟩, rfl⟩)).to_subtype
  set ind : G → ℝ≥0∞ := Ω.indicator (fun _ => 1) with hind
  have hindm : Measurable ind := measurable_const.indicator hΩ
  set Fd : G → G → ℝ≥0∞ := fun g y => ind (g⁻¹ * y) * ‖Ph y‖ₑ with hFd
  have hFdm : ∀ g, Measurable (Fd g) := fun g =>
    (hindm.comp (measurable_const_mul _)).mul hPh.enorm

  have step1 : ∀ g : G, ‖Ph g‖ₑ ≤ (a : ℝ≥0∞) * ∫⁻ y, Fd g y ∂μ := by
    intro g
    refine (hbd g).trans (le_of_eq ?_)
    congr 1
    have e1 : ∫⁻ y, Fd g y ∂μ = ∫⁻ ω, Fd g (g * ω) ∂μ := (lintegral_mul_left_eq_self (Fd g) g).symm
    rw [e1, ← lintegral_indicator hΩ]
    refine lintegral_congr fun ω => ?_
    by_cases hω : ω ∈ Ω <;> simp [hFd, hind, hω]
  have step2 : ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ ≤
      (a : ℝ≥0∞) * ∫⁻ y, ∑' δ : D, Fd ((δ : G) * x) y ∂μ := by
    rw [lintegral_tsum (fun δ => (hFdm _).aemeasurable), ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun δ => step1 _

  have step3 : ∫⁻ y, ∑' δ : D, Fd ((δ : G) * x) y ∂μ =
      ∫⁻ y in F, ∑' s : S, ∑' δ : D, Fd ((δ : G) * x) ((s : G) * y) ∂μ := by
    refine (hF.lintegral_eq_tsum'' _).trans (lintegral_tsum fun s => ?_).symm
    exact (Measurable.ennreal_tsum fun δ => (hFdm _).comp (measurable_const_mul _)).aemeasurable

  have step4 : ∀ y, ∑' s : S, ∑' δ : D, Fd ((δ : G) * x) ((s : G) * y) ≤
      mult Γ Ω x * ‖Ph y‖ₑ := by
    intro y
    have e : ∀ (s : S) (δ : D), Fd ((δ : G) * x) ((s : G) * y) =
        ind (x⁻¹ * (((δ : G)⁻¹ * (s : G)) * y)) * ‖Ph y‖ₑ := by
      intro s δ
      simp only [hFd, hS s s.2 y, mul_inv_rev, mul_assoc]
    simp_rw [e, ENNReal.tsum_mul_right]
    have ht := tsum_transversal Γ S hSΓ D hD (fun g => ind (x⁻¹ * (g * y)))
    beta_reduce at ht
    rw [ENNReal.tsum_comm, ht]
    gcongr
    have hsum : ∑' γ : Γ, ind (x⁻¹ * ((γ : G) * y)) =
        ((({γ : Γ | x⁻¹ * ((γ : G) * y) ∈ Ω} : Set Γ).encard : ℕ∞) : ℝ≥0∞) := by
      rw [← ENNReal.tsum_set_one, tsum_subtype _ (fun _ : Γ => (1 : ℝ≥0∞))]
      congr 1
    rw [hsum]
    exact le_iSup (fun y' => ((({γ : Γ | x⁻¹ * ((γ : G) * y') ∈ Ω} : Set Γ).encard : ℕ∞) : ℝ≥0∞)) y
  calc ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ
      ≤ (a : ℝ≥0∞) * ∫⁻ y, ∑' δ : D, Fd ((δ : G) * x) y ∂μ := step2
    _ = (a : ℝ≥0∞) * ∫⁻ y in F, ∑' s : S, ∑' δ : D, Fd ((δ : G) * x) ((s : G) * y) ∂μ := by
        rw [step3]
    _ ≤ (a : ℝ≥0∞) * ∫⁻ y in F, mult Γ Ω x * ‖Ph y‖ₑ ∂μ := by
        gcongr with y
        exact step4 y
    _ = (a : ℝ≥0∞) * mult Γ Ω x * quotientLIntegral μ F Ph := by
        unfold quotientLIntegral
        rw [lintegral_const_mul _ hPh.enorm, mul_assoc]

end Formalism.L2.SG.FoldBound
