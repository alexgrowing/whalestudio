import Mathlib

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace GlobalTheory
namespace OrbitUnfold

variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H}

def pull (𝓕 : Set H) (g : H) : Set H := (fun h => g * h) ⁻¹' 𝓕

open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in
theorem _root_.GlobalTheory.OrbitUnfold.nullMeasurableSet_pull (hF : IsFundamentalDomain Γ 𝓕 ν) (g : H) :
    NullMeasurableSet (_root_.GlobalTheory.OrbitUnfold.pull 𝓕 g) ν :=
  hF.nullMeasurableSet.preimage (measurePreserving_mul_left ν g).quasiMeasurePreserving

open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in
theorem _root_.GlobalTheory.OrbitUnfold.aedisjoint_pull (hF : IsFundamentalDomain Γ 𝓕 ν) {a b : Γ}
    (hab : a ≠ b) :
    AEDisjoint ν (_root_.GlobalTheory.OrbitUnfold.pull 𝓕 (a : H)) (_root_.GlobalTheory.OrbitUnfold.pull 𝓕 (b : H)) := by
  have key : ∀ c : Γ, _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (c : H) = c⁻¹ • 𝓕 := fun c => by
    ext x
    simp [_root_.GlobalTheory.OrbitUnfold.pull, Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def]
  rw [key, key]
  exact hF.aedisjoint (inv_injective.ne hab)

open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in
theorem _root_.GlobalTheory.OrbitUnfold.setIntegral_pull (g : H) (f : H → ℂ) :
    ∫ h in _root_.GlobalTheory.OrbitUnfold.pull 𝓕 g, f (g * h) ∂ν = ∫ h in 𝓕, f h ∂ν :=
  (measurePreserving_mul_left ν g).setIntegral_preimage_emb (measurableEmbedding_mulLeft g) f 𝓕

open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in
theorem _root_.GlobalTheory.OrbitUnfold.setLIntegral_pull (g : H) (f : H → ℝ≥0∞) :
    ∫⁻ h in _root_.GlobalTheory.OrbitUnfold.pull 𝓕 g, f (g * h) ∂ν = ∫⁻ h in 𝓕, f h ∂ν :=
  (measurePreserving_mul_left ν g).setLIntegral_comp_preimage_emb
    (measurableEmbedding_mulLeft g) f 𝓕

open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in

theorem _root_.GlobalTheory.OrbitUnfold.isFundamentalDomain_iUnion_pull (hF : IsFundamentalDomain Γ 𝓕 ν)
    (y₀ : Y) {O : Set Y}
    [Countable O] (hO : ∀ γ : Γ, γ • y₀ ∈ O) (σ : O → Γ) (hσ : ∀ a : O, σ a • y₀ = a) :
    IsFundamentalDomain ((MulAction.stabilizer Γ y₀).map Γ.subtype)
      (⋃ a : O, _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H)) ν where
  nullMeasurableSet := .iUnion fun a => _root_.GlobalTheory.OrbitUnfold.nullMeasurableSet_pull hF _
  ae_covers := by
    filter_upwards [hF.ae_covers] with x ⟨γ, hγ⟩
    let a : O := ⟨γ • y₀, hO γ⟩
    have hs : (σ a)⁻¹ * γ ∈ MulAction.stabilizer Γ y₀ := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, hσ a]
    refine ⟨⟨Γ.subtype ((σ a)⁻¹ * γ), Subgroup.mem_map_of_mem _ hs⟩, Set.mem_iUnion.2 ⟨a, ?_⟩⟩
    simpa [_root_.GlobalTheory.OrbitUnfold.pull, Subgroup.smul_def, mul_assoc] using hγ
  aedisjoint := by
    rintro ⟨_, s, hs, rfl⟩ ⟨_, t, ht, rfl⟩ hst
    have hset : ∀ (u : Γ) (hu : u ∈ MulAction.stabilizer Γ y₀) (a : O),
        (⟨Γ.subtype u, Subgroup.mem_map_of_mem _ hu⟩ :
            (MulAction.stabilizer Γ y₀).map Γ.subtype) •
          _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H) = (σ a * u⁻¹)⁻¹ • 𝓕 := by
      intro u hu a
      ext x
      simp [Set.mem_smul_set_iff_inv_smul_mem, _root_.GlobalTheory.OrbitUnfold.pull, Subgroup.smul_def,
        mul_assoc]
    simp only [Function.onFun, Set.smul_set_iUnion, hset s hs, hset t ht]
    refine AEDisjoint.iUnion_left_iff.2 fun a => AEDisjoint.iUnion_right_iff.2 fun b => ?_
    refine hF.aedisjoint (inv_injective.ne fun h => hst ?_)
    have hab : a = b := by
      apply Subtype.ext
      have h1 := congrArg (· • y₀) h
      simp only [mul_smul] at h1
      rwa [inv_smul_eq_iff.2 hs.symm, inv_smul_eq_iff.2 ht.symm, hσ, hσ] at h1
    subst hab
    have : s = t := inv_injective (mul_left_cancel h)
    subst this
    rfl

open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in
private theorem selfEquivSigmaOrbits_symm_mk {G X : Type} [Group G] [MulAction G X]
    (ω : MulAction.orbitRel.Quotient G X) (x : MulAction.orbit G ω.out) :
    (MulAction.selfEquivSigmaOrbits G X).symm ⟨ω, x⟩ = x := rfl

open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in

theorem _root_.GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero :
    ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H)
      [ν.IsMulLeftInvariant] (Γ : Subgroup H) [Countable Γ] (Y : Type) [Countable Y]
      [MulAction Γ Y] (𝓕 : Set H), IsFundamentalDomain Γ 𝓕 ν → ∀ Φ : Y → H → ℂ,
      (∀ y, Measurable (Φ y)) → (∀ (γ : Γ) y h, Φ (γ • y) ((γ : H) * h) = Φ y h) →
      ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν ≠ ⊤ →
      (∀ y (𝓖 : Set H), IsFundamentalDomain ((MulAction.stabilizer Γ y).map Γ.subtype) 𝓖 ν →
        IntegrableOn (Φ y) 𝓖 ν → ∫ h in 𝓖, Φ y h ∂ν = 0) →
      ∑' y, ∫ h in 𝓕, Φ y h ∂ν = 0 := by
  intro H _ _ _ ν _ Γ _ Y _ _ 𝓕 hF Φ hmeas hinv hfin hzero
  have horbit : ∀ y₀ : Y, ∑' a : MulAction.orbit Γ y₀, ∫ h in 𝓕, Φ a h ∂ν = 0 := by
    intro y₀
    have hO : ∀ γ : Γ, γ • y₀ ∈ MulAction.orbit Γ y₀ := fun γ => MulAction.mem_orbit y₀ γ
    choose σ hσ using fun a : MulAction.orbit Γ y₀ =>
      (MulAction.mem_orbit_iff.1 a.2 : ∃ g : Γ, g • y₀ = a)
    have hT := _root_.GlobalTheory.OrbitUnfold.isFundamentalDomain_iUnion_pull hF y₀ hO σ hσ
    have hshift : ∀ a : MulAction.orbit Γ y₀, ∀ h, Φ a ((σ a : H) * h) = Φ y₀ h := fun a h => by
      rw [← hinv (σ a) y₀ h, hσ]
    have hpt : ∀ a : MulAction.orbit Γ y₀,
        ∫ h in 𝓕, Φ a h ∂ν = ∫ h in _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H), Φ y₀ h ∂ν := by
      intro a
      rw [← _root_.GlobalTheory.OrbitUnfold.setIntegral_pull (σ a : H) (Φ a)]
      simp only [hshift]
    have hlpt : ∀ a : MulAction.orbit Γ y₀,
        ∫⁻ h in _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H), ‖Φ y₀ h‖ₑ ∂ν = ∫⁻ h in 𝓕, ‖Φ a h‖ₑ ∂ν := by
      intro a
      rw [← _root_.GlobalTheory.OrbitUnfold.setLIntegral_pull (σ a : H) (fun h => ‖Φ a h‖ₑ)]
      simp only [hshift]
    have hσinj : Function.Injective σ := fun a b hab =>
      Subtype.ext (by rw [← hσ a, ← hσ b, hab])
    have hdisj : Pairwise (Function.onFun (AEDisjoint ν)
        fun a : MulAction.orbit Γ y₀ => _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H)) :=
      fun a b hab => _root_.GlobalTheory.OrbitUnfold.aedisjoint_pull hF (hσinj.ne hab)
    have hint : IntegrableOn (Φ y₀)
        (⋃ a : MulAction.orbit Γ y₀, _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H)) ν := by
      refine ⟨(hmeas y₀).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      calc ∫⁻ h in ⋃ a : MulAction.orbit Γ y₀, _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H), ‖Φ y₀ h‖ₑ ∂ν
          ≤ ∑' a : MulAction.orbit Γ y₀, ∫⁻ h in _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H), ‖Φ y₀ h‖ₑ ∂ν :=
            lintegral_iUnion_le _ _
        _ = ∑' a : MulAction.orbit Γ y₀, ∫⁻ h in 𝓕, ‖Φ a h‖ₑ ∂ν := by simp only [hlpt]
        _ ≤ ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν :=
            ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
        _ < ⊤ := lt_top_iff_ne_top.2 hfin
    simp only [hpt]
    rw [← integral_iUnion_ae (fun a => _root_.GlobalTheory.OrbitUnfold.nullMeasurableSet_pull hF _) hdisj hint]
    exact hzero y₀ _ hT hint
  have hsum : Summable fun y => ∫ h in 𝓕, Φ y h ∂ν := by
    refine Summable.of_norm_bounded (ENNReal.summable_toReal hfin) fun y => ?_
    rw [← toReal_enorm]
    exact ENNReal.toReal_mono (ENNReal.ne_top_of_tsum_ne_top hfin y)
      (enorm_integral_le_lintegral_enorm _)
  have hs' := ((MulAction.selfEquivSigmaOrbits Γ Y).symm.summable_iff
    (f := fun y => ∫ h in 𝓕, Φ y h ∂ν)).2 hsum
  rw [← (MulAction.selfEquivSigmaOrbits Γ Y).symm.tsum_eq (fun y => ∫ h in 𝓕, Φ y h ∂ν)]
  simp only [Function.comp_def] at hs'
  rw [Summable.tsum_sigma hs']
  simp only [Function.comp_apply, selfEquivSigmaOrbits_symm_mk, horbit, tsum_zero]

end OrbitUnfold
end GlobalTheory
