import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.MetFam GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.CxPts
open scoped ComplexOrder

namespace GlobalTheory

theorem PPAS.RiemannData.snd_valR_tangent : ∀ (T : Scheme.{0}) (P : PPAS T) (y₀ : Sp ℂ ⟶ T) (d : P.RiemannData y₀) (X : Scheme.{0}) (θ : P.A.left ⟶ X) (W : X.Opens), ⊤ ≤ (y₀ ≫ LieVB.unitSec P.A) ⁻¹ᵁ (θ ⁻¹ᵁ W) → ∀ (f : Γ(X, W)) (v : epsR ℂ ⟶ d.B) (w : Fin P.g → ℂ), IsTangent v → d.u.IsDiff w v → TrivSqZeroExt.snd (valR (v.left ≫ d.φ ≫ θ) W f) = ∑ a, w a * d.cov (θ ⁻¹ᵁ W) (θ.appLE W (θ ⁻¹ᵁ W) le_rfl f) a := by
  intro T P y₀ d X θ W hW f v w hv hd
  have h0 : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left ≫ d.φ) ⁻¹ᵁ (θ ⁻¹ᵁ W) := by
    rw [← Category.assoc, hv, ← d.ex_zero, (d.u.ker 0).2 (zero_mem _)] at *
    rw [← MonObj.one_eq_one d.B] at hW
    exact hW
  have hs : Subsingleton (PrimeSpectrum (DualNumber ℂ)) := by
    have key : ∀ p : PrimeSpectrum (DualNumber ℂ), p.asIdeal = IsLocalRing.maximalIdeal _ := fun p => by
      refine le_antisymm (IsLocalRing.le_maximalIdeal p.2.ne_top) fun a ha => ?_
      have ha0 : a.fst = 0 := by
        by_contra ha0
        exact ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (IsUnit.mk0 _ ha0))
      refine p.2.mem_of_pow_mem 2 ?_
      have : a ^ 2 = 0 := by ext <;> simp [ha0, pow_two]
      rw [this]; exact p.asIdeal.zero_mem
    exact ⟨fun p q => PrimeSpectrum.ext ((key p).trans (key q).symm)⟩
  have h1 : ⊤ ≤ v.left ⁻¹ᵁ (d.φ ⁻¹ᵁ (θ ⁻¹ᵁ W)) := by
    intro x _
    have hx : x = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom (IsLocalRing.closedPoint ℂ) :=
      Subsingleton.elim (α := PrimeSpectrum (DualNumber ℂ)) _ _
    rw [hx]
    exact h0 (Set.mem_univ _)
  have h2 := hd _ h1 (d.φ.app _ (θ.app W f))
  have h3 : valR (v.left ≫ d.φ ≫ θ) W f = valR v.left (d.φ ⁻¹ᵁ (θ ⁻¹ᵁ W)) (d.φ.app _ (θ.app W f)) := by
    rw [← Category.assoc, Points.valR_comp, Points.valR_comp]
  rw [h3, Points.valR_eq _ _ h1]
  refine h2.trans ?_
  have h4 : (fun z => valAt' (d.u.ex z).left _ (d.φ.app _ (θ.app W f))) =
      d.fn (θ ⁻¹ᵁ W) (θ.appLE W (θ ⁻¹ᵁ W) le_rfl f) := by
    funext z
    rw [Scheme.Hom.appLE_eq_app]
    exact (Points.valR_comp _ _ _ _).symm
  rw [h4]
  conv_lhs => rw [← Finset.univ_sum_single w, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [PPAS.RiemannData.cov, ← smul_eq_mul, ← map_smul, ← Pi.single_smul, smul_eq_mul, mul_one]

end GlobalTheory
