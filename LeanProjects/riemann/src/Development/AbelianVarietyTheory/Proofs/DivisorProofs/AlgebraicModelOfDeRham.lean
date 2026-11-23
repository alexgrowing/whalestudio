import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPeriodFromEllipticLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCorrespondenceDifferentialsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeDifferentialsAlgebraicStatement

set_option autoImplicit false

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ModelAlgProof

theorem modelAlg : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ModelAlg := by
  intro hPC hDR hDC K _ _ d δ io hK hd hδ Λ₀ Ω₀ hΛ hΩ E _ _ _ _ I _ φ hφ hio c y hc
  obtain ⟨𝔠, X₀, X, p, U, v₀, v, a, hp, hh, hv, hex, hdesc⟩ :=
    GlobalTheory.T.cm_period_from_elliptic_lattice hPC hDR hDC K d δ io hK hd hδ Λ₀ Ω₀ hΛ hΩ E I φ hφ hio c y hc
  obtain ⟨δ₀, δX, C, hDCr, hdet, hCa⟩ :=
    GlobalTheory.T.lie_correspondence_differentials E I φ _ 𝔠 X₀ X p U v₀ v a hp fun i ↦ ⟨(hv i).1, (hv i).2.1⟩
  obtain ⟨N, m, ψ, yv, w, hpol, hAdm, hvec⟩ := GlobalTheory.T.cm_type_differentials_algebraic hPC hDR hDC E I φ _ 𝔠 X₀ X p U v₀ v a hφ hp
    (fun i ↦ ⟨(hv i).1, (hv i).2.1, (hv i).2.2.1⟩) hex hdesc

  have hσ : ∀ x : Qb, IsAlgebraic ℚ (algebraMap Qb ℂ x) := fun x ↦ by
    have := x.2
    rwa [mem_algebraicClosure_iff] at this
  have toQ : ∀ z : ℂ, IsAlgebraic ℚ z → z ∈ (algebraicClosure ℚ ℂ) := fun z hz ↦ by
    rwa [mem_algebraicClosure_iff]
  have ofQ : ∀ z : ℂ, z ∈ (algebraicClosure ℚ ℂ) → IsAlgebraic ℚ z := fun z hz ↦ by
    rwa [mem_algebraicClosure_iff] at hz
  let T : CxPt 𝔠 φ (lattice c y) :=
    { X := X, U := U, δ := δX, C := C, det := hdet, ψ := ψ, pol := hpol, y := yv, w := w, s := fun _ ↦ 1,
      cm := fun i ↦ (hvec i).1 }
  have ha0 : ∀ i, a i ≠ 0 := fun i ↦ (hv i).2.2.1
  refine ⟨𝔠, X₀, δ₀, N, T, hAdm, ⟨p, m, hp, hDCr, fun i x₀ x hx ↦ ?_⟩, ?_, fun i ↦ ⟨?_, ?_⟩⟩
  · have := (hvec i).2.2.2 x₀ x hx
    simpa [T, CxPt.low] using this
  · have hprod : (∏ i, a i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦ ha0 i
    have e : C / Ω₀ ^ Fintype.card I = (C * ∏ i, a i) / ∏ i, (a i * Ω₀) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, mul_comm (∏ x, a x) _,
        mul_div_mul_right _ _ hprod]
    change IsAlgebraic ℚ (C / Ω₀ ^ Fintype.card I)
    rw [e]
    apply ofQ
    exact div_mem (toQ _ hCa) (prod_mem fun i _ ↦ toQ _ (hv i).2.2.2)
  · have hw := (hvec i).2.1
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    change (Real.pi : ℂ) * (U.h i : ℂ) * 1 * w i ^ 2 ≠ 0
    have := (hh i).1
    simp only [_root_.mul_one]
    exact mul_ne_zero (mul_ne_zero hpi (Complex.ofReal_ne_zero.2 this)) (pow_ne_zero _ hw)
  · have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    have e : T.A i * Ω₀ ^ 2 * ((Real.sqrt d : ℝ) : ℂ) / (2 * Real.pi) =
        ((U.h i : ℂ) * (Real.sqrt d : ℝ)) * (w i / a i) ^ 2 * (a i * Ω₀) ^ 2 / 2 := by
      change (Real.pi : ℂ) * (U.h i : ℂ) * 1 * w i ^ 2 * Ω₀ ^ 2 * ((Real.sqrt d : ℝ) : ℂ) / (2 * Real.pi) = _
      field_simp [ha0 i]
    rw [e]
    apply ofQ
    refine div_mem (mul_mem (mul_mem (toQ _ (hh i).2) (pow_mem (toQ _ (hvec i).2.2.1) _))
      (pow_mem (toQ _ (hv i).2.2.2) _)) ?_
    simpa using (algebraicClosure ℚ ℂ).algebraMap_mem (2 : ℚ)

end GlobalTheory.ModelAlgProof
