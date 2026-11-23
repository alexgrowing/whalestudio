import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisModN
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_lift_basis_modN : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (N : ℕ), 0 < N → ∃ e : Fin (D.p + D.q) → D.La,
      (∀ a : D.La, ∃ c : Fin (D.p + D.q) → 𝓞 E, D.ModN N (a - ∑ i, c i • e i)) ∧
      ∀ c : Fin (D.p + D.q) → 𝓞 E, D.ModN N (∑ i, c i • e i) → ∀ i, ∃ b : 𝓞 E, c i = N • b := by
  intro E _ _ _ H D N hN
  haveI := D.fin
  haveI := D.proj
  have hN0 : (N : 𝓞 E) ≠ 0 := by exact_mod_cast hN.ne'
  obtain ⟨e, h1, h2⟩ := GlobalTheory.ModNBasis.exists_basis_modN (M := D.La) hN0
  rw [← D.rank]
  refine ⟨e, fun a => ?_, fun c hc i => ?_⟩
  · obtain ⟨c, w, hw⟩ := h1 a
    exact ⟨c, w, by rw [hw, Nat.cast_smul_eq_nsmul]⟩
  · obtain ⟨w, hw⟩ := hc
    obtain ⟨b, hb⟩ := h2 c ⟨w, by rw [hw, Nat.cast_smul_eq_nsmul]⟩ i
    exact ⟨b, by rw [hb, nsmul_eq_mul]⟩

end GlobalTheory
