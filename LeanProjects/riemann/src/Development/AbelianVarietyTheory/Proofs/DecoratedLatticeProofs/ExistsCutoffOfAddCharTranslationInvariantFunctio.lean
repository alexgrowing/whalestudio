import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzBruhatConvolutionLocalFieldPower
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralScaledBoxPiSupersetOfIsCompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinsetIntegralScaledBoxPiCosetRepsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumIntegralScaledBoxPiCosetRepsShiftInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralBoxInvariantEqMeasureRealMulSumRepsStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

noncomputable section
namespace GlobalTheory.CharCutoff

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dot_eq_one {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) {n : Type} [Fintype n]
    (R : kˣ) {t y : n → k} (ht : t ∈ box n (c * R⁻¹)) (hy : y ∈ box n R) : ψ (t ⬝ᵥ y) = 1 := by
  apply h.eq_one
  show valuation k (∑ i, t i * y i) ≤ valuation k (c : k)
  refine Valuation.map_sum_le (valuation k) fun i _ => ?_
  have h2 : valuation k (t i * y i) ≤ valuation k (((c * R⁻¹ : kˣ) : k) * R) := by
    rw [map_mul, map_mul]
    exact mul_le_mul' (ht i trivial) (hy i trivial)
  rwa [← Units.val_mul, inv_mul_cancel_right] at h2

theorem exists_dot_ne_one {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) {n : Type} [Fintype n]
    (s : kˣ) {y : n → k} (hy : y ∉ box n s) : ∃ b ∈ box n (c * s⁻¹), ψ (b ⬝ᵥ y) ≠ 1 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, y i ∉ cball s := by
    by_contra hne
    push_neg at hne
    exact hy fun i _ => hne i
  have hcs : c * (c * s⁻¹)⁻¹ = s := by
    rw [_root_.mul_inv_rev, inv_inv, mul_comm s, mul_inv_cancel_left]
  obtain ⟨t, ht, hne⟩ := h.exists_ne_one (c * s⁻¹) (x := y i) (by rwa [hcs])
  refine ⟨Pi.single i t, fun j _ => ?_, ?_⟩
  · by_cases hj : j = i
    · subst hj; simpa using ht
    · simp [Pi.single_eq_of_ne hj, cball]
  · rwa [single_dotProduct]

theorem sum_char {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) {n : Type} [Fintype n]
    (s R : kˣ) (S : Finset (n → k)) (hS : ∀ b ∈ S, b ∈ box n (c * s⁻¹))
    (hU : ∀ a ∈ box n (c * s⁻¹), ∃! b, b ∈ S ∧ a - b ∈ box n (c * R⁻¹)) {y : n → k}
    (hy : y ∈ box n R) :
    ∑ b ∈ S, (ψ (b ⬝ᵥ y) : ℂ) = (box n s).indicator (fun _ => (1 : ℂ)) y * S.card := by
  by_cases hys : y ∈ box n s
  · rw [Set.indicator_of_mem hys, one_mul]
    rw [Finset.sum_congr rfl fun b hb => by rw [dot_eq_one h s (hS b hb) hys, Circle.coe_one]]
    simp
  · rw [Set.indicator_of_notMem hys, zero_mul]
    obtain ⟨a, ha, hne⟩ := exists_dot_ne_one h s hys
    have key := GlobalTheory.T.sum_integralScaledBoxPi_coset_reps_shift_invariant k n (c * R⁻¹) (c * s⁻¹) S hS hU (fun b => (ψ (b ⬝ᵥ y) : ℂ))
      (fun t ht z => by
        rw [add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, dot_eq_one h R ht hy,
          Circle.coe_one, mul_one]) a ha
    simp only [add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, ← Finset.mul_sum] at key
    have h3 : (ψ (a ⬝ᵥ y) : ℂ) - 1 ≠ 0 := fun h4 => hne (Circle.ext (by simpa using sub_eq_zero.mp h4))
    refine (mul_eq_zero.mp ?_).resolve_left h3
    rw [sub_mul, key, one_mul, sub_self]

theorem exists_cutoff_of_char_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) →ₗ[ℂ] M), (∀ (b : I₁ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x) → l Φ' = l Φ) → ∀ (Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))) (s : kˣ), ∃ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)), (∀ x, Φ'.1 x = (box I₁ s).indicator (fun _ => (1 : ℂ)) x.2.1 * Φ.1 x) ∧ l Φ = l Φ' := by
  intro k _ _ _ _ ψ hψ h1 I₀ I₁ I₂ _ _ _ M _ _ l hl Φ s
  haveI := t2Space k
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
  have hK : IsCompact ((fun x : (I₀ → k) × (I₁ → k) × (I₂ → k) => x.2.1) '' tsupport Φ.1) :=
    Φ.2.2.image (by fun_prop)
  obtain ⟨R, hsR, hKR⟩ := GlobalTheory.T.exists_integralScaledBoxPi_superset_of_isCompact k I₁ _ hK s
  have hvr : valuation k ((c * R⁻¹ : kˣ) : k) ≤ valuation k ((c * s⁻¹ : kˣ) : k) := by
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
    exact mul_le_mul' le_rfl (inv_anti₀ (by simp [zero_lt_iff]) hsR)
  obtain ⟨S, hS, hU⟩ := GlobalTheory.T.exists_finset_integralScaledBoxPi_coset_reps k I₁ (c * R⁻¹) (c * s⁻¹) hvr
  have hmem : ∀ b : I₁ → k,
      (fun x : (I₀ → k) × (I₁ → k) × (I₂ → k) => (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x) ∈
        SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) := fun b => by
    have hcont : Continuous fun x : (I₀ → k) × (I₁ → k) × (I₂ → k) => b ⬝ᵥ x.2.1 :=
      continuous_const.dotProduct (continuous_fst.comp continuous_snd)
    have h2 : IsLocallyConstant fun x : (I₀ → k) × (I₁ → k) × (I₂ → k) => (ψ (b ⬝ᵥ x.2.1) : ℂ) :=
      (IsLocallyConstant.comp_continuous hc.isLocallyConstant hcont).comp (fun z : Circle => (z : ℂ))
    exact ⟨IsLocallyConstant.mul h2 Φ.2.1, Φ.2.2.mul_left⟩
  let Φb : (I₁ → k) → SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) := fun b => ⟨_, hmem b⟩
  have hlb : ∀ b, l (Φb b) = l Φ := fun b => hl b Φ (Φb b) (fun x => rfl)
  have h0 : (0 : I₁ → k) ∈ box I₁ (c * s⁻¹) := fun i _ => by simp [cball]
  obtain ⟨b0, ⟨hb0, _⟩, _⟩ := hU 0 h0
  have hcard : (S.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨b0, hb0⟩).ne'
  refine ⟨(S.card : ℂ)⁻¹ • ∑ b ∈ S, Φb b, fun x => ?_, ?_⟩
  · simp only [Submodule.coe_smul, Submodule.coe_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    show (S.card : ℂ)⁻¹ * ∑ b ∈ S, (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x = _
    rw [← Finset.sum_mul]
    by_cases hx : x ∈ tsupport Φ.1
    · rw [sum_char hc s R S hS hU (hKR ⟨x, hx, rfl⟩), ← mul_assoc, mul_comm ((S.card : ℂ)⁻¹),
        mul_inv_cancel_right₀ hcard]
    · rw [image_eq_zero_of_notMem_tsupport hx]; simp
  · rw [map_smul, map_sum, Finset.sum_congr rfl fun b _ => hlb b, Finset.sum_const,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

end GlobalTheory.CharCutoff
