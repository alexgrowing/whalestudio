import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemOfAevalEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem notMem_mCoordIdeal_of_aeval_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {h : MRing ι} (h0 : aeval y h ≠ 0) : h ∉ mCoordIdeal y := by
  intro hh
  apply h0
  have e := UnitChart.aeval_scaled y (fun _ => 1) h
  simp only [mul_one] at e
  rw [e, show mConeMap y h = 0 from hh, map_zero]

theorem exists_flatHerm_unit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (α : (𝓞 F)ˣ), OverInt y φ → ∃ S : FlatHerm y φ (constLine (ι := ι) 0), S.M = 1 ∧ ∀ σ, S.κ σ = ‖σ ((α : 𝓞 F) : F)‖ := by
  intro K _ ι _ Ω _ F _ _ y φ α hO
  obtain ⟨hy, hR⟩ := hO
  choose c hc using id hy
  obtain ⟨m, G, hG, e⟩ := UnitChart.chart_form hc (hR c hc (α : 𝓞 F))
  have hα : ((α : 𝓞 F) : F) ≠ 0 := by
    simp
  have hφα : φ ((α : 𝓞 F) : F) ≠ 0 := (map_ne_zero φ).2 hα
  have hprod : (∏ k, y ⟨k, c k⟩ ^ m k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  have hg0 : aeval y (UnitChart.cMon c m) ≠ 0 := by rwa [UnitChart.aeval_cMon]
  have hG0 : aeval y G ≠ 0 := by rw [← e]; exact mul_ne_zero hφα hprod
  have e' : aeval y G = φ ((α : 𝓞 F) : F) * aeval y (UnitChart.cMon c m) := by
    rw [UnitChart.aeval_cMon, e]
  have hq : aeval y G / aeval y (UnitChart.cMon c m) = φ ((α : 𝓞 F) : F) := by
    rw [e', mul_div_cancel_right₀ _ hg0]
  have hinv : φ (((α⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = (φ ((α : 𝓞 F) : F))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul]
    have : (((α⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ((α : 𝓞 F) : F) = 1 := by
      have h1 : ((α⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * (α : 𝓞 F) = 1 := α.inv_mul
      have h2 := congrArg (algebraMap (𝓞 F) F) h1
      rw [map_mul, map_one] at h2
      exact h2
    rw [this, map_one]
  have hfn := notMem_mCoordIdeal_of_aeval_ne_zero hG0
  have hgn := notMem_mCoordIdeal_of_aeval_ne_zero hg0
  refine ⟨{ M := 1
            M_pos := one_pos
            f := G
            g := UnitChart.cMon c m
            df := m
            dg := m
            hf := hG
            hg := UnitChart.homog_cMon c m
            deg := fun k => by simp [constLine, HermLine.ofWeight]
            f_ne := hfn
            g_ne := hgn
            unit := ?_
            κ := fun σ => ‖σ ((α : 𝓞 F) : F)‖
            κ_pos := fun σ => norm_pos_iff.2 ((map_ne_zero σ).2 hα)
            κ_conj := fun σ => by simp [ComplexEmbedding.conjugate_coe_eq]
            norm := ?_ }, rfl, fun _ => rfl⟩
  · rw [isUnitSec_iff_chart K ι Ω y G _ m m hy hG (UnitChart.homog_cMon c m) hfn hgn]
    intro c' hc'
    simp only [sub_self, neg_zero, zpow_zero, Finset.prod_const_one, mul_one, hq]
    exact ⟨hR c' hc' _, hinv ▸ hR c' hc' _⟩
  · intro σ z hz
    rw [hz.2 _ m G _ hG (UnitChart.homog_cMon c m) e', norm_mul]
    simp [constLine, HermLine.ofWeight]

end GlobalTheory.CompanionTheory.Ar.Flat
