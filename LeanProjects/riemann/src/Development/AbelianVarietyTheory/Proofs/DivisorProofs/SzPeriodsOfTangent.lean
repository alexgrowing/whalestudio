import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIntegralityRamifiedOfExpansion

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel

variable {E : Type} [Field E] [NumberField E] {I : Type} {𝔠 : FracId (FR E)} {R : Subring ℂ}

theorem sz_period_of_tangent {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} {φ : I → E →+* ℂ} {L : Set E}
    {X₀ : Obj (FR E) 𝔠 (Sp R)} {X : Obj (FR E) 𝔠 (Sp ℂ)} {U : Unif φ L 0 X} {p : X.A.left ⟶ X₀.A.left} {i : I}
    {e : X₀.Lie →ₗ[R] R} {a Ω : ℂ} {r : ℝ} (hR : IsPlaceRing E l lam R) (he : IsPeriodGen X₀ U p i e a)
    {v : X₀.Lie} {v' : X.Lie} {W : Fin (Module.finrank ℚ (FR E)) → ℂ} (hv : Obj.LieCorr R.subtype p v v')
    (hW : U.u.IsDiff W v'.hom) (hW0 : W (U.e.symm i) ≠ 0) (hs : Sz l lam r ((W (U.e.symm i) * Ω)⁻¹)) :
    Sz l lam r (a / Ω) := by
  have h := he v v' W hv hW
  have ha : a / Ω = ((e v : R) : ℂ) * (W (U.e.symm i) * Ω)⁻¹ := by
    rw [h, _root_.mul_inv, div_eq_mul_inv,
      show a * W (U.e.symm i) * ((W (U.e.symm i))⁻¹ * Ω⁻¹) = a * Ω⁻¹ * (W (U.e.symm i) * (W (U.e.symm i))⁻¹) by ring,
      mul_inv_cancel₀ hW0, _root_.mul_one]
  rw [ha]
  simpa using GlobalTheory.LatValRam.sz_mul (hR.2.1 _ (e v).2) hs

end GlobalTheory.LatModel
