import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAtIffForallSpecializesStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.MultEff

open CartierDiv

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

theorem ord_one (z : X) : Scheme.ord (1 : X.functionField) z = 0 := (unitAt_one z).ord_eq_zero

theorem mult_zero (z : X) : (0 : CartierDiv X).mult z = 0 := by
  rw [(isEqn_zero z).mult_eq, Units.val_one, ord_one]

theorem mult_neg (D : CartierDiv X) (z : X) : (-D).mult z = - D.mult z := by
  have h := mult_add D (-D) z
  rw [add_neg_cancel, mult_zero] at h
  omega

theorem ord_inv (u : X.functionFieldˣ) (z : X) :
    Scheme.ord ((u⁻¹ : X.functionFieldˣ) : X.functionField) z = - Scheme.ord (u : X.functionField) z := by
  have h := Scheme.ord_mul (x := z) u.ne_zero (u⁻¹).ne_zero
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, ord_one] at h
  omega

theorem IsEqn.of_specializes {D : CartierDiv X} {x z : X} {g : X.functionFieldˣ} (h : D.IsEqn x g)
    (hz : z ⤳ x) : D.IsEqn z g := by
  obtain ⟨U, hU, hg⟩ := h.exists_nhds
  exact hg z (hz.mem_open U.isOpen hU)

variable [GlobalTheory.IsNormalScheme X]

theorem regAt_iff_ord (x : X) (u : X.functionFieldˣ) :
    RegAt x (u : X.functionField) ↔ ∀ z, z ⤳ x → 0 ≤ Scheme.ord (u : X.functionField) z := by
  rw [← regularAt_zero_iff, GlobalTheory.T.regularAt_iff_forall_specializes_ord_add_mult_nonneg X (0 : CartierDiv X) x u]
  simp only [mult_zero, add_zero]

theorem unitAt_of_ord (x : X) (u : X.functionFieldˣ)
    (h : ∀ z, z ⤳ x → Scheme.ord (u : X.functionField) z = 0) : UnitAt x (u : X.functionField) := by
  rw [unitAt_iff u.ne_zero, ← Units.val_inv_eq_inv_val, regAt_iff_ord, regAt_iff_ord]
  exact ⟨fun z hz => (h z hz).ge, fun z hz => by rw [ord_inv, h z hz, neg_zero]⟩

theorem eff_supp_eq_of_mult : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (D : CartierDiv X), (D.Eff ↔ ∀ z, 0 ≤ D.mult z) ∧ (∀ x, x ∈ D.supp ↔ ∃ z, z ⤳ x ∧ D.mult z ≠ 0) ∧ (∀ E : CartierDiv X, (∀ z, D.mult z = E.mult z) → D = E) ∧ ∀ (x : X) (g : X.functionFieldˣ), (∀ z, z ⤳ x → Scheme.ord (g : X.functionField) z = D.mult z) → D.IsEqn x g := by
  intro X _ _ _ D
  have hEff : ∀ F : CartierDiv X, F.Eff ↔ ∀ z, 0 ≤ F.mult z := by
    intro F
    refine ⟨fun h z => ?_, fun h x => ?_⟩
    · have := (GlobalTheory.T.regularAt_iff_forall_specializes_ord_add_mult_nonneg X F z 1).1 (h z) z (specializes_refl z)
      simpa [Units.val_one, ord_one] using this
    · have := (GlobalTheory.T.regularAt_iff_forall_specializes_ord_add_mult_nonneg X F x 1).2 fun z _ => by simpa [Units.val_one, ord_one] using h z
      simpa using this
  refine ⟨hEff D, fun x => ⟨fun hx => ?_, fun ⟨z, hz, hm⟩ => ?_⟩, fun E h => ?_, fun x g h => ?_⟩
  · by_contra hne
    push_neg at hne
    obtain ⟨g, hg⟩ := D.exists_isEqn x
    refine (hg.mem_supp_iff.1 hx) (unitAt_of_ord x g fun z hz => ?_)
    rw [← (IsEqn.of_specializes hg hz).mult_eq]
    exact hne z hz
  · exact hz.mem_closed D.supp.isClosed (mem_supp_of_mult_ne_zero hm)
  · have h1 : (D - E).Eff := (hEff _).2 fun z => by
      rw [sub_eq_add_neg, mult_add, mult_neg, h z]; omega
    have h2 : (-(D - E)).Eff := (hEff _).2 fun z => by
      rw [mult_neg, sub_eq_add_neg, mult_add, mult_neg, h z]; omega
    exact sub_eq_zero.1 (h1.eq_zero h2)
  · obtain ⟨g', hg'⟩ := D.exists_isEqn x
    refine hg'.iff_unitAt.2 ?_
    have e : ((g / g' : X.functionFieldˣ) : X.functionField) = (g : X.functionField) / g' :=
      Units.val_div_eq_div_val g g'
    rw [← e]
    refine unitAt_of_ord x _ fun z hz => ?_
    have hm := (IsEqn.of_specializes hg' hz).mult_eq
    rw [Units.val_div_eq_div_val, div_eq_mul_inv, Scheme.ord_mul g.ne_zero (inv_ne_zero g'.ne_zero),
      ← Units.val_inv_eq_inv_val, ord_inv, h z hz, hm]
    ring

end GlobalTheory.Cartier.MultEff
