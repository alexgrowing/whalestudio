import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.RegCodimOne

theorem regAt_iff_ord_nonneg {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] {z : X} (hz : Order.coheight z = 1) {g : X.functionField} (hg : g ≠ 0) :
    RegAt z g ↔ 0 ≤ Scheme.ord g z := by
  haveI := IsNormalScheme.isDiscreteValuationRing_stalk hz
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk z)
  have h := le_ordTop_vw_iff (F := X.functionField) ht 0 g
  rw [ordTop_vw_of_ne_zero _ hg, WithTop.coe_le_coe] at h
  have e : Scheme.ord g z = WithZero.log (Ring.ordFrac (X.presheaf.stalk z) g) :=
    (Scheme.ord_eq_iff hz hg).2 (WithZero.exp_log ((map_ne_zero _).2 hg)).symm
  rw [e]
  refine Iff.trans ⟨fun ⟨a, ha⟩ => ⟨a, by simp [ha]⟩, fun ⟨a, ha⟩ => ⟨a, by simp [ha]⟩⟩ h.symm

theorem regularAt_iff_forall_specializes : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (D : CartierDiv X) (x : X) (f : X.functionFieldˣ), D.RegularAt x (f : X.functionField) ↔ ∀ z, z ⤳ x → 0 ≤ Scheme.ord (f : X.functionField) z + D.mult z := by
  intro X _ _ _ D x f
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  obtain ⟨U, hU, hgU⟩ := hg.exists_nhds
  have hne : (f : X.functionField) * (g : X.functionField) ≠ 0 := mul_ne_zero f.ne_zero g.ne_zero
  have key : ∀ z, z ⤳ x → Scheme.ord (f : X.functionField) z + D.mult z =
      Scheme.ord ((f : X.functionField) * (g : X.functionField)) z := fun z hz => by
    rw [(hgU z (hz.mem_open U.isOpen hU)).mult_eq, Scheme.ord_mul f.ne_zero g.ne_zero]
  rw [hg.regularAt_iff]
  refine ⟨fun h z hz => ?_, fun h => regAt_of_forall_coheight_eq_one fun z hz h1 => ?_⟩
  · rw [key z hz]
    by_cases h1 : Order.coheight z = 1
    · exact (regAt_iff_ord_nonneg h1 hne).1 (GlobalTheory.Discrepancy.regAt_of_specializes hz h)
    · rw [Scheme.ord_eq_zero_of_coheight_neq_one h1]
  · exact (regAt_iff_ord_nonneg h1 hne).2 (key z hz ▸ h z hz)

end GlobalTheory.RegCodimOne
