import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowDegreeSection
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowDegreeClosedPoint
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsReductionModP
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSectionCycleModP
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsPointLengthModP
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsMultiProjPrime geoNum divSupp multAt)

theorem perfectField_of_intCast_surjective (F : Type) [Field F] (p : ℕ) (hp : p.Prime)
    (hs : Function.Surjective (Int.castRingHom F)) (h0 : ((p : ℤ) : F) = 0) : PerfectField F := by
  have := Fact.mk hp
  have : CharP F p := (CharP.charP_iff_prime_eq_zero hp).mpr (by exact_mod_cast h0)
  have hcomp : (ZMod.castHom (dvd_refl p) F).comp (Int.castRingHom (ZMod p)) = Int.castRingHom F :=
    RingHom.ext_int _ _
  have hsurj : Function.Surjective (ZMod.castHom (dvd_refl p) F) := by
    refine Function.Surjective.of_comp (g := Int.castRingHom (ZMod p)) ?_
    rw [← RingHom.coe_comp, hcomp]
    exact hs
  have : Finite F := Finite.of_surjective _ hsurj
  infer_instance

theorem linForm_single {F : Type} [Field F] {n : ℕ} (i : Fin n) : linForm (Pi.single i (1 : F)) = X i := by
  simp [linForm, Pi.single_apply]

theorem isMultiHomog_X {n : ℕ} (i : Fin n) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (X ⟨(), i⟩ : MRing (PBlk n)) (fun _ => 1) := by
  intro m hm k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hj (eq_of_heq (Sigma.mk.inj_iff.mp h).2).symm
  · simp

theorem divSupp_X {n e : ℕ} {W W' : Ideal (MRing (PBlk n))} {i : Fin n} (hW : IsMultiProjPrime W)
    (hdim : ringKrullDim (MRing (PBlk n) ⧸ W) = ((e + 1 + 1 : ℕ) : WithBot ℕ∞))
    (hi : (X ⟨(), i⟩ : MRing (PBlk n)) ∉ W) (hW' : W' ∈ divSupp W (X ⟨(), i⟩)) :
    IsMultiProjPrime W' ∧ W ≤ W' ∧ ringKrullDim (MRing (PBlk n) ⧸ W') = ((e + 1 : ℕ) : WithBot ℕ∞) := by
  have := hW.1
  refine ⟨⟨hW'.1.1.1, ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomogIdeal_of_mem_minimalPrimes hW.2.1 (isMultiHomog_X i)
    hW'.1, hW'.2⟩, le_sup_left.trans hW'.1.1.2, ?_⟩
  exact ReciprocityTheory.ChartRestriction.G.Geo.withBot_eq_of_add_one
    ((ReciprocityTheory.ChartRestriction.G.Geo.dim_quot_minimal_add_one W W' _ hi hW'.1).trans hdim)

theorem ChowDegreeGeoNum.proof (hS : ChowDegreeSection.Statement) (hP : ChowDegreeClosedPoint.Statement)
    (hR : ReductionModP.Statement) (hC : SectionCycleModP.Statement) (hL : PointLengthModP.Statement) :
    ChowDegreeGeoNum.Statement := by
  intro n e p W F _ hp hW hpW hdim hsurj h0
  have := perfectField_of_intCast_surjective F p hp hsurj h0
  induction e generalizing W with
  | zero =>
    obtain ⟨hI, hIdim, hX⟩ := hR n p W F hp hW hpW hsurj h0
    have hrel := hW.2.2
    have hiW : (X ⟨(), (hrel ()).choose⟩ : MRing (PBlk n)) ∉ W := (hrel ()).choose_spec
    have hpt := hP F n _ (hrel ()).choose hI (hIdim.trans hdim) (by rwa [hX])
    rw [geoNum, dif_pos hrel]
    have hrange : Set.range (fun k : Unit => (X ⟨k, (hrel k).choose⟩ : MRing (PBlk n)) - 1) =
        {(X ⟨(), (hrel ()).choose⟩ : MRing (PBlk n)) - 1} := by
      rw [Set.range_unique]
    rw [hrange, hL n p W F hp hW hpW hsurj h0 (hrel ()).choose]
    exact_mod_cast hpt
  | succ e ih =>
    obtain ⟨hI, hIdim, hX⟩ := hR n p W F hp hW hpW hsurj h0
    have hrel := hW.2.2
    have hiW : (X ⟨(), (hrel ()).choose⟩ : MRing (PBlk n)) ∉ W := (hrel ()).choose_spec
    have hXi : linForm (Pi.single (hrel ()).choose (1 : F)) ∉
        (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W).map (MvPolynomial.map (Int.castRingHom F)) := by
      rw [linForm_single, hX]
      exact hiW
    have hsec := hS F n e _ _ hI (hIdim.trans hdim) hXi
    rw [hC n p W F hp hW hpW hsurj h0 _ hiW,
      Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)] at hsec
    show (chowDegree _ (e + 2) : ℤ) = _
    rw [hsec, geoNum, dif_pos hrel]
    simp only [Fintype.sum_unique, one_mul, Finsupp.sum, Nat.cast_sum, Nat.cast_mul]
    have hfin := ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite W (X ⟨(), (hrel ()).choose⟩ : MRing (PBlk n))
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    classical
    have hval : ∀ W', ReciprocityTheory.ChartRestriction.G.Geo.divCycle W (X ⟨(), (hrel ()).choose⟩) W' =
        if W' ∈ divSupp W (X ⟨(), (hrel ()).choose⟩) then
          multAt (W ⊔ Ideal.span {(X ⟨(), (hrel ()).choose⟩ : MRing (PBlk n))}) W' else 0 := by
      intro W'
      simp [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe]
    refine Finset.sum_subset (fun W' hW' => ?_) (fun W' _ hW' => ?_) |>.trans (Finset.sum_congr rfl ?_)
    · rw [Set.Finite.mem_toFinset]
      by_contra h
      exact Finsupp.mem_support_iff.mp hW' (by rw [hval, if_neg h])
    · rw [Finsupp.notMem_support_iff.mp hW', Nat.cast_zero, zero_mul]
    · intro W' hW'
      rw [Set.Finite.mem_toFinset] at hW'
      obtain ⟨hW'p, hle, hW'dim⟩ := divSupp_X hW hdim hiW hW'
      rw [hval, if_pos hW', ih W' hW'p (hle hpW) hW'dim]
      rfl

end ObjectsChow

end GroundTheory.Heights₂.Heights
