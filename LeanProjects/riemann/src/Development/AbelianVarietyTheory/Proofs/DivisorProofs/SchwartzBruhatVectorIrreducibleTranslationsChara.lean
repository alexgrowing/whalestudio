import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNeZeroOfEventually
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.IrredSBVec

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem norm_char_eq_one (ψ0 : AddChar k ℂ) (h1 : ∀ y ∈ 𝒪[k], ψ0 y = 1) (x : k) : ‖ψ0 x‖ = 1 := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨n, hn, hxn⟩ := GlobalTheory.SBUnif.exists_nat_mem_mul_integer x⁻¹ (inv_ne_zero hx)
  rw [inv_inv] at hxn
  have hp : ψ0 x ^ n = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_comm]
    exact h1 _ hxn
  have := congrArg norm hp
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this

def toCircle (ψ0 : AddChar k ℂ) (h1 : ∀ y ∈ 𝒪[k], ψ0 y = 1) : AddChar k Circle where
  toFun x := ⟨ψ0 x, mem_sphere_zero_iff_norm.2 (norm_char_eq_one ψ0 h1 x)⟩
  map_zero_eq_one' := Circle.ext (by simp)
  map_add_eq_mul' a b := Circle.ext (AddChar.map_add_eq_mul ψ0 a b)

theorem coe_toCircle (ψ0 : AddChar k ℂ) (h1 : ∀ y ∈ 𝒪[k], ψ0 y = 1) (x : k) :
    ((toCircle ψ0 h1 x : Circle) : ℂ) = ψ0 x := rfl

theorem continuous_toCircle (ψ0 : AddChar k ℂ) (h1 : ∀ y ∈ 𝒪[k], ψ0 y = 1) (hψ : Continuous ψ0) :
    Continuous (toCircle ψ0 h1) :=
  hψ.subtype_mk _

theorem sb_irreducible_vec : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    {κ : Type} [Fintype κ] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    (∀ x : k, (∀ y ∈ 𝒪[k], ψ0 (x * y) = 1) ↔ x ∈ 𝒪[k]) →
    ∀ W : Submodule ℂ ((κ → k) → ℂ), W ≤ GlobalTheory.WeilM.SB (κ → k) →
    (∀ φ ∈ W, ∀ v : κ → k, (fun x => φ (x + v)) ∈ W) →
    (∀ φ ∈ W, ∀ y : κ → k, (fun x => ψ0 (x ⬝ᵥ y) * φ x) ∈ W) →
    ∀ φ₀ ∈ W, φ₀ ≠ 0 → W = GlobalTheory.WeilM.SB (κ → k) := by
  intro k _ _ _ _ _ κ _ ψ0 hψ hcond W hW hT hM φ₀ h0 hne
  classical
  have h1 : ∀ y ∈ 𝒪[k], ψ0 y = 1 := fun y hy => by
    simpa using (hcond 1).2 (one_mem _) y hy
  set ψ := toCircle ψ0 h1 with hψdef
  have hψc : Continuous ψ := continuous_toCircle ψ0 h1 hψ
  have hψ1 : ψ ≠ 1 := by
    obtain ⟨w, hw0, hw1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
    have hno : w⁻¹ ∉ 𝒪[k] := by
      intro h
      have h' : valuation k w⁻¹ ≤ 1 := h
      rw [map_inv₀] at h'
      have hv0 : valuation k w ≠ 0 := (Valuation.ne_zero_iff _).2 hw0
      have := (one_lt_inv₀ (zero_lt_iff.2 hv0)).2 hw1
      exact absurd h' (not_le.2 this)
    have := mt (hcond w⁻¹).1 hno
    push_neg at this
    obtain ⟨y, -, hy⟩ := this
    intro he
    apply hy
    have := congrArg (fun χ : AddChar k Circle => ((χ (w⁻¹ * y) : Circle) : ℂ)) he
    simpa [hψdef, coe_toCircle] using this

  let toM : (κ → k) → Matrix κ Unit k := fun x i _ => x i
  let frM : Matrix κ Unit k → (κ → k) := fun t i => t i ()
  have hto : Continuous toM := by fun_prop
  have hfr : Continuous frM := by fun_prop
  have hft : ∀ t, toM (frM t) = t := fun t => by funext i j; rfl
  let e : Matrix κ Unit k ≃ₜ (κ → k) :=
    { toFun := frM, invFun := toM, left_inv := hft, right_inv := fun x => rfl,
      continuous_toFun := hfr, continuous_invFun := hto }
  have SBto : ∀ φ : (κ → k) → ℂ, φ ∈ GlobalTheory.WeilM.SB (κ → k) → (fun t => φ (frM t)) ∈ GlobalTheory.SplitWeil.SB (Matrix κ Unit k) :=
    fun φ hφ => ⟨hφ.1.comp_continuous hfr, hφ.2.comp_homeomorph e⟩
  let W' : Submodule ℂ (Matrix κ Unit k → ℂ) := W.comap (LinearMap.funLeft ℂ ℂ toM)
  have mem' : ∀ Φ, Φ ∈ W' ↔ (fun x => Φ (toM x)) ∈ W := fun Φ => Iff.rfl
  have hW' : W' ≤ GlobalTheory.SplitWeil.SB (Matrix κ Unit k) := by
    intro Φ hΦ
    have := SBto _ (hW ((mem' Φ).1 hΦ))
    simpa only [hft] using this
  have key := GlobalTheory.IrredSB.sb_irreducible k κ Unit ψ hψc hψ1 W' hW'
    (fun Φ hΦ x _ => by
      rw [mem']
      have := hT _ ((mem' Φ).1 hΦ) (frM x)
      have hv : ∀ v, toM (v + frM x) = toM v + x := fun v => by
        funext i j
        cases j
        rfl
      show (fun v => Φ (toM v + x)) ∈ W
      simpa only [hv] using this)
    (fun Φ hΦ b _ => by
      rw [mem']
      have := hM _ ((mem' Φ).1 hΦ) (fun i => b i ())
      have hs : ∀ v, (∑ r, ∑ q, b r q * toM v r q) = v ⬝ᵥ (fun i => b i ()) := fun v => by
        rw [dotProduct]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Fintype.sum_unique]
        exact mul_comm _ _
      show (fun v => ((ψ (∑ r, ∑ q, b r q * toM v r q) : Circle) : ℂ) * Φ (toM v)) ∈ W
      simp only [hs]
      exact this)
    (fun t => φ₀ (frM t)) ((mem' _).2 h0) (by
      intro h
      apply hne
      funext x
      exact congrFun h (toM x))
  refine le_antisymm hW fun φ hφ => ?_
  · have : (fun t => φ (frM t)) ∈ W' := key ▸ SBto φ hφ
    exact (mem' _).1 this

end GlobalTheory.IrredSBVec
