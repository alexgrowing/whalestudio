import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharZeroAdicCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import GroundTheory.LocalFields.ConductorReciprocity
import GroundTheory.LocalFields.LubinTateReciprocity
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeTate

theorem ord_zpow_units {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : kˣ) (n : ℤ) : GlobalTheory.SmGL.ord k (x ^ n) = n * GlobalTheory.SmGL.ord k x := by
  let f : kˣ →* Multiplicative ℤ :=
    { toFun := fun y => Multiplicative.ofAdd (GlobalTheory.SmGL.ord k y)
      map_one' := by rw [GlobalTheory.SmGL.ord_eq_zero (by simp)]; rfl
      map_mul' := fun y z => by rw [GlobalTheory.SmGL.ord_mul]; rfl }
  have := congrArg Multiplicative.toAdd (map_zpow f x n)
  simpa [f] using this

theorem isUnit_artin_mul_zpow : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a → ∀ (σ : Weil h) (π u : 𝒪[w.adicCompletion E]),
    Irreducible π → (u : w.adicCompletion E) = (a σ : w.adicCompletion E) * (π : w.adicCompletion E) ^ deg σ →
    IsUnit u := by
  intro E Ω _ _ _ _ _ A w h a ha σ π u hπ hu
  set K := w.adicCompletion E
  have hint := Valuation.integer.integers (valuation K)
  have hπ0 : (π : K) ≠ 0 := fun h0 => hπ.ne_zero (Subtype.ext h0)
  have hπle : valuation K (π : K) ≤ 1 := π.2
  have hπlt : valuation K (π : K) < 1 := by
    have := hπ.not_isUnit
    rw [hint.isUnit_iff_valuation_eq_one] at this
    exact lt_of_le_of_ne hπle this
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.Published.JacquetShalikaLocalBound.exists_uniformizer K
  have hπv : valuation K (π : K) = uniformizer K := by
    apply le_antisymm (le_uniformizer_iff.2 hπlt)
    by_contra hlt
    push_neg at hlt
    have hϖ0 : (ϖ : K) ≠ 0 := ϖ.ne_zero
    have hpos : (0 : ValueGroupWithZero K) < valuation K (ϖ : K) := by
      rw [hϖ]; exact zero_lt_iff.2 uniformizer_ne_zero
    have hq : valuation K ((π : K) * (ϖ : K)⁻¹) < 1 := by
      rw [map_mul, map_inv₀]
      exact (mul_inv_lt_iff₀ hpos).2 (by rw [one_mul, hϖ]; exact hlt)
    let x : 𝒪[K] := ⟨ϖ, by show valuation K (ϖ : K) ≤ 1; rw [hϖ]; exact uniformizer_lt_one.le⟩
    let y : 𝒪[K] := ⟨(π : K) * (ϖ : K)⁻¹, hq.le⟩
    have hxy : π = x * y := Subtype.ext (by
      show (π : K) = (ϖ : K) * ((π : K) * (ϖ : K)⁻¹)
      field_simp)
    rcases hπ.isUnit_or_isUnit hxy with hx | hy
    · rw [hint.isUnit_iff_valuation_eq_one] at hx
      exact uniformizer_lt_one.ne (hϖ ▸ hx)
    · rw [hint.isUnit_iff_valuation_eq_one] at hy
      exact hq.ne hy
  let p : Kˣ := Units.mk0 _ hπ0
  have hp1 : GlobalTheory.SmGL.ord K p = 1 := GlobalTheory.SmGL.ord_eq_one hπv
  have hd := ha.ord_eq σ
  have hz : GlobalTheory.SmGL.ord K (a σ * p ^ deg σ) = 0 := by
    rw [GlobalTheory.SmGL.ord_mul, ord_zpow_units, hd, hp1]; ring
  have hv := GlobalTheory.SmGL.ord_eq_zero_iff.1 hz
  rw [hint.isUnit_iff_valuation_eq_one]
  show valuation K (u : K) = 1
  rw [hu]
  simpa [p, Units.val_zpow_eq_zpow_val] using hv

end GlobalTheory.HeckeTate
