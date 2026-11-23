import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTransportEllipticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointGaloisConjugateStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet

theorem modelConj_of_deRham : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ModelConj := by
  intro hPC hDR hDC K _ _ d δ io hK hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E _ _ _ _ I _ φ hφ hres c y hc 𝔠 X₀ δ₀ N T hover
  obtain ⟨X', p, U', hp, he, hcc, hh, hdiff, hend⟩ := GlobalTheory.T.torsion_transport_elliptic hPC hDR hDC K d δ io hK hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E I φ hφ hres c y hc 𝔠 T
  have hΩ₀ : Ω₀ ≠ 0 := hT.1
  have hΩ₁ : Ω₁ ≠ 0 := hT.2.1
  have hgΩ₀ : g Ω₀ ≠ 0 := by simpa using hΩ₀
  have hκ : g Ω₀ / Ω₁ ≠ 0 := div_ne_zero hgΩ₀ hΩ₁
  obtain ⟨T', hT'o, hC, hA'⟩ := GlobalTheory.T.complex_point_galois_conjugate hPC hDR hDC E I 𝔠 φ (lattice c y) (lattice c (y * (upIdele K E t)⁻¹)) T Qb (algebraMap Qb ℂ) X₀ δ₀ N
    hover g X' p U' (g Ω₀ / Ω₁) hp hκ he hcc (by
      intro w v v' h1 h2
      have h3 := hdiff w v v' h1 h2
      have e : (fun j ↦ g (Ω₀ * w j) / Ω₁) = (fun j ↦ g Ω₀ / Ω₁ * g (w j)) := by
        funext j; rw [map_mul]; field_simp
      rwa [e] at h3) hend
  refine ⟨T', hT'o, ?_, ?_⟩
  · have hC' : T'.C = g T.C / (g Ω₀ / Ω₁) ^ Fintype.card I := by
      rw [← hC]; field_simp
    have hn : T'.C / Ω₁ ^ Fintype.card I = g (T.C / Ω₀ ^ Fintype.card I) := by
      rw [hC', map_div₀, map_pow, div_pow]
      field_simp
    rw [hn]
  · intro i
    obtain ⟨hhi, hsw⟩ := hA' i
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have key := hh i
    unfold CxPt.A
    rw [hhi]
    have e1 : (Real.pi : ℂ) * (T.U.h i : ℂ) * T.s i * T.w i ^ 2 * Ω₀ ^ 2 * ((Real.sqrt d : ℝ) : ℂ) / (2 * Real.pi) =
        ((T.U.h i : ℂ) * ((Real.sqrt d : ℝ) : ℂ)) * (T.s i * T.w i ^ 2) * Ω₀ ^ 2 / 2 := by
      field_simp
    have e2 : (Real.pi : ℂ) * (U'.h i : ℂ) * T'.s i * T'.w i ^ 2 * Ω₁ ^ 2 * ((Real.sqrt d : ℝ) : ℂ) / (2 * Real.pi) =
        ((U'.h i : ℂ) * ((Real.sqrt d : ℝ) : ℂ)) * (T'.s i * T'.w i ^ 2) * Ω₁ ^ 2 / 2 := by
      field_simp
    rw [e1, e2, hsw, map_div₀, map_mul, map_mul, map_pow, key]
    have g2 : g (2 : ℂ) = 2 := map_ofNat g 2
    rw [g2]
    field_simp

end GlobalTheory.LatJet
