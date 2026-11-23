import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemOfAevalEqZero

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht.Diag

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
open GlobalTheory.CompanionTheory.Ar.Flat.UnitChart

section General

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem hasVal_unique {y : (Σ k, ι k) → Ω} {a : K → ℤ} {s : Ω} {L : Type} [Field L] {z : (Σ k, ι k) → L}
    (hz : z ∈ ptsOver L (mCoordIdeal y)) {w w' : L} (h : HasVal y a s z w) (h' : HasVal y a s z w') : w = w' := by
  obtain ⟨dg, dh, g, h₁, hg, hh, hd, hy, hz0, hzw⟩ := h
  obtain ⟨dg', dh', g', h₁', hg', hh', hd', hy', hz0', hzw'⟩ := h'
  have e : dg + dh' = dg' + dh := by
    funext k
    simp only [Pi.add_apply]
    have h1 := hd k
    have h2 := hd' k
    omega
  have hh2 : IsMultiHomog (g' * h₁) (dg + dh') := by
    rw [e]
    exact GlobalTheory.CompanionTheory.Ar.Flat.UnitChart.homog_mul hg' hh
  have hF : g * h₁' - g' * h₁ ∈ mCoordIdeal y := by
    refine GlobalTheory.CompanionTheory.Ar.Flat.UnitChart.mem_of_aeval_eq_zero
      (GlobalTheory.CompanionTheory.Ar.Flat.UnitChart.homog_sub (GlobalTheory.CompanionTheory.Ar.Flat.UnitChart.homog_mul hg hh') hh2) ?_
    rw [map_sub, map_mul, map_mul, hy, hy']
    ring
  have h0 := hz.2 _ hF
  rw [map_sub, map_mul, map_mul, hzw, hzw'] at h0
  have h2 : (w - w') * ((MvPolynomial.aeval z) h₁ * (MvPolynomial.aeval z) h₁') = 0 := by
    linear_combination h0
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact sub_eq_zero.mp h3
  · exact absurd h3 (mul_ne_zero hz0 hz0')

end General

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

end GlobalTheory.CompanionTheory.Ar.Ht.Diag
