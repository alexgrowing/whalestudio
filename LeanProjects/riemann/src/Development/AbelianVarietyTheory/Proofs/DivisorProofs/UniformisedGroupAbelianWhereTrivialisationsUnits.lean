import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFixedUnramifiedCompleteTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointMemAbelianLocusOfFixedTorsionStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.PsiUnitAb

theorem subset_abLocus_of_psiUnitOn : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → (W : Set (Sp R)) ⊆ abLocus G := by
  have hI1 := @GlobalTheory.T.torsion_fixed_unramified_complete_trait
  have hI2 := @GlobalTheory.T.closedPoint_mem_abelianLocus_of_fixedTorsion
  intro R _ _ _ hR D A G _ _ hG U W hW x hx
  have := hR.1.1
  have := hR.2
  obtain ⟨n, hn, hu⟩ : ∃ n : ℕ, 2 ≤ n ∧ IsUnit (n : R) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := (3 : R)) (b := -2) (by norm_num) with h | h
    · exact ⟨3, by norm_num, by exact_mod_cast h⟩
    · exact ⟨2, le_rfl, by exact_mod_cast (IsUnit.neg_iff _).1 h⟩
  have := x.isPrime
  obtain ⟨V, _, _, _, φ, hV, hφ, hc⟩ := GlobalTheory.PrimeUnif.exists_cdvr R x.asIdeal
  have hcx : spMap φ (closedPoint V) = x := PrimeSpectrum.ext hc
  have huV : IsUnit (n : V) := by simpa using hu.map φ
  have h1 := hI1 R hR D A G hG U W hW V φ hV hφ (hcx ▸ hx) n hn huV
  have h2 := hI2 R hR D A G hG U V φ hV hφ n hn huV h1
  have key := abLocus_pullback (G' := (Over.pullback (spMap φ)).obj G) abLocusOne hG (isGrpPullback_pullback G (spMap φ)).1 (closedPoint V)
  rw [← hcx]
  exact key.2 h2

end GlobalTheory.Mum.PsiUnitAb
