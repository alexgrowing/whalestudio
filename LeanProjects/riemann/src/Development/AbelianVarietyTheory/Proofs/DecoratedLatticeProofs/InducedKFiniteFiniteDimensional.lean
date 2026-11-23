import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst

open scoped NNReal
open GlobalTheory.Doubling

noncomputable section
namespace GlobalTheory.EisCont

def transComb {G : Type} [Group G] (K : Subgroup G) (ψ : G → ℂ) : (K →₀ ℂ) →ₗ[ℂ] (G → ℂ) :=
  Finsupp.lsum ℂ fun k : K => LinearMap.smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ) (fun g => ψ (g * k))

theorem transComb_apply {G : Type} [Group G] (K : Subgroup G) (ψ : G → ℂ) (c : K →₀ ℂ) (g : G) :
    transComb K ψ c g = c.sum fun k z => z * ψ (g * k) := by
  simp [transComb, Finsupp.lsum_apply, Finsupp.sum, Finset.sum_apply]

def domSub {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G) (χ : P →* Circle) (t : ℂ)
    (φ : G → ℂ) : Submodule ℂ (G → ℂ) where
  carrier := domSet δ K χ t φ
  zero_mem' := ⟨fun _ _ => by simp, fun c _ g => by simp [Finsupp.sum]⟩
  add_mem' := fun {a b} ha hb => ⟨fun p g => by simp only [Pi.add_apply, ha.1 p g, hb.1 p g, mul_add],
    fun c hc g => by
      have h1 := ha.2 c hc g
      have h2 := hb.2 c hc g
      simp only [Pi.add_apply, mul_add]
      rw [Finsupp.sum_add, h1, h2, add_zero]⟩
  smul_mem' := fun a b hb => ⟨fun p g => by simp only [Pi.smul_apply, hb.1 p g, smul_eq_mul]; ring,
    fun c hc g => by
      have h1 := hb.2 c hc g
      simp only [Pi.smul_apply, smul_eq_mul]
      have : (c.sum fun k z => z * (a * b (g * k))) = a * c.sum fun k z => z * b (g * k) := by
        rw [Finsupp.mul_sum]; congr 1; ext k z; ring
      rw [this, h1, mul_zero]⟩

theorem span_domSet_le {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G) (χ : P →* Circle)
    (t : ℂ) (φ : G → ℂ) : Submodule.span ℂ (domSet δ K χ t φ) ≤ domSub δ K χ t φ :=
  Submodule.span_le.2 fun _ h => h

theorem range_transComb_le {G : Type} [Group G] (K : Subgroup G) (φ : G → ℂ) :
    LinearMap.range (transComb K φ) ≤ kSpan K φ := by
  rintro _ ⟨c, rfl⟩
  have : transComb K φ c = c.sum fun k z => z • fun g => φ (g * k) := by
    ext g; rw [transComb_apply]; simp [Finsupp.sum, Finset.sum_apply]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i : G), i.2, rfl⟩)

def evalForm {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G) (χ : P →* Circle) (t : ℂ)
    (φ : G → ℂ) : domSub δ K χ t φ →ₗ[ℂ] ((K →₀ ℂ) ⧸ LinearMap.ker (transComb K φ)) →ₗ[ℂ] ℂ where
  toFun ψ := (LinearMap.ker (transComb K φ)).liftQ ((LinearMap.proj 1).comp (transComb K ψ)) (by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    have := ψ.2.2 c (fun g => by rw [← transComb_apply, hc]; rfl) 1
    simpa [transComb_apply] using this)
  map_add' a b := by
    ext c
    simp [transComb_apply, Finsupp.sum_add, mul_add]
  map_smul' a b := by
    ext c
    simp only [transComb_apply, LinearMap.comp_apply, Submodule.liftQ_apply, LinearMap.coe_comp, Function.comp_apply,
      Submodule.mkQ_apply, LinearMap.proj_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      LinearMap.smul_apply, Finsupp.mul_sum]
    congr 1; ext k z; ring

theorem evalForm_injective {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G) (χ : P →* Circle)
    (t : ℂ) (φ : G → ℂ) (hPK : ∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k) : Function.Injective (evalForm δ K χ t φ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ψ hψ
  apply Subtype.ext
  refine IndLaw.ext hPK ψ.2.1 (fun _ _ => by simp) fun k hk => ?_
  have := LinearMap.congr_fun hψ (Submodule.mkQ _ (Finsupp.single ⟨k, hk⟩ 1))
  simpa [evalForm, transComb_apply] using this

theorem finiteDimensional_span_domSet : ∀ (G : Type) [Group G] (P K : Subgroup G) (δ : P →* ℝ≥0) (χ : P →* Circle)
    (t : ℂ) (φ : G → ℂ), (∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k) → IsKFinite K φ →
    FiniteDimensional ℂ (Submodule.span ℂ (domSet δ K χ t φ)) := by
  intro G _ P K δ χ t φ hPK hφ
  haveI : FiniteDimensional ℂ (kSpan K φ) := hφ
  have : FiniteDimensional ℂ (LinearMap.range (transComb K φ)) :=
    Submodule.finiteDimensional_of_le (range_transComb_le K φ)
  have : FiniteDimensional ℂ ((K →₀ ℂ) ⧸ LinearMap.ker (transComb K φ)) :=
    LinearEquiv.finiteDimensional (transComb K φ).quotKerEquivRange.symm
  have : FiniteDimensional ℂ (domSub δ K χ t φ) :=
    Module.Finite.of_injective _ (evalForm_injective δ K χ t φ hPK)
  exact Submodule.finiteDimensional_of_le (span_domSet_le δ K χ t φ)

end GlobalTheory.EisCont
end
