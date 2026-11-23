import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem exists_integral_of_modelAt (F : IntermediateField ℚ ℂ) [NumberField F] (w : HeightOneSpectrum (𝓞 F))
    (V : ValuationSubring ℂ) (A : WeierstrassCurve F) (D : F)
    (hV : ∀ x : F, (x : ℂ) ∈ V ↔ x ∈ w.valuationSubringAtPrime F) (hD : D ≠ 0)
    (h : ModelAt V F (A.map (algebraMap F ℂ)) (D : ℂ)) :
    ∃ (C : VariableChange F) (u : (w.valuationSubringAtPrime F)ˣ),
      (C • A).IsIntegral (w.valuationSubringAtPrime F) ∧
        (C • A).Δ = ((u : w.valuationSubringAtPrime F) : F) * D := by
  obtain ⟨C, hu, hr, hs, ht, ⟨h1, h2, h3, h4, h6⟩, hΔ⟩ := h
  have hu0 : (⟨(C.u : ℂ), hu⟩ : F) ≠ 0 := by
    intro h0
    exact C.u.ne_zero (congrArg (fun x : F => (x : ℂ)) h0)
  let C' : VariableChange F := ⟨Units.mk0 _ hu0, ⟨C.r, hr⟩, ⟨C.s, hs⟩, ⟨C.t, ht⟩⟩
  have hC : C'.map (algebraMap F ℂ) = C := by
    ext <;> rfl
  have hmap : (C' • A).map (algebraMap F ℂ) = C • A.map (algebraMap F ℂ) := by
    rw [← hC, map_variableChange]
  rw [← hmap] at h1 h2 h3 h4 h6 hΔ
  set W := C' • A with hW
  have hD' : (D : ℂ) ≠ 0 := fun h0 => hD (Subtype.ext h0)
  have hvD : V.valuation (D : ℂ) ≠ 0 := by simpa using hD'
  rw [map_Δ] at hΔ
  have hΔ' : V.valuation ((W.Δ : F) : ℂ) = V.valuation (D : ℂ) := hΔ
  have hW0 : W.Δ ≠ 0 := by
    intro h0
    rw [h0] at hΔ'
    exact hvD (by simpa using hΔ'.symm)
  have hx : W.Δ / D ∈ w.valuationSubringAtPrime F := by
    rw [← hV, ← V.valuation_le_one_iff]
    push_cast
    rw [map_div₀, hΔ', div_self hvD]
  have hy : D / W.Δ ∈ w.valuationSubringAtPrime F := by
    rw [← hV, ← V.valuation_le_one_iff]
    push_cast
    rw [map_div₀, hΔ', div_self hvD]
  refine ⟨C', ⟨⟨_, hx⟩, ⟨_, hy⟩, ?_, ?_⟩, ?_, ?_⟩
  · apply Subtype.ext
    show W.Δ / D * (D / W.Δ) = 1
    field_simp
  · apply Subtype.ext
    show D / W.Δ * (W.Δ / D) = 1
    field_simp
  · refine ⟨⟨⟨⟨W.a₁, (hV _).1 h1⟩, ⟨W.a₂, (hV _).1 h2⟩, ⟨W.a₃, (hV _).1 h3⟩, ⟨W.a₄, (hV _).1 h4⟩,
      ⟨W.a₆, (hV _).1 h6⟩⟩, ?_⟩⟩
    ext <;> rfl
  · show W.Δ = W.Δ / D * D
    field_simp

end GlobalTheory.CMModel
