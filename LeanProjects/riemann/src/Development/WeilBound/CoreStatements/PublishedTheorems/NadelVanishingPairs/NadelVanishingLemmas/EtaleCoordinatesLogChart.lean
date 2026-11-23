import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSubsingletonCohTwistTensLbPow
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtFnOfOfNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularLocalStatement
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsLocalizedModuleGermLinearPointOfPrime
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FractionFieldCoordinatesDlog
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RootOfMonomialQuotientIntegral
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.UnitOfHeightOnePrimesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtLog

variable {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U)

include hU in

theorem unitAt_fnOf_iff_not_mem {y : X} (hy : y ∈ U) (s : Γ(X, U)) :
    UnitAt y (fnOf U (gen_mem hy) s) ↔ s ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal := by
  rw [unitAt_fnOf_iff hy, GlobalTheory.DetHT.RegLoc.mem_basicOpen_iff hU hy]

include hU in

theorem regAt_iff_frac {y : X} (hy : y ∈ U) (g : X.functionField) :
    RegAt y g ↔ ∃ a b : Γ(X, U), b ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal ∧
      g * fnOf U (gen_mem hy) b = fnOf U (gen_mem hy) a := by
  constructor
  · intro hg
    exact GlobalTheory.FieldPair.regAt_exists_fraction hU hy hg
  · rintro ⟨a, b, hb, e⟩
    have hu := GlobalTheory.FieldPair.unitAt_fnOf_of_not_mem hU hy hb
    have eg : g = fnOf U (gen_mem hy) a * (fnOf U (gen_mem hy) b)⁻¹ := by
      rw [← e, mul_inv_cancel_right₀ hu.ne_zero]
    rw [eg]
    exact (regAt_fnOf hy _ a).mul hu.inv.regAt

include hU in

theorem unitAt_iff_frac {y : X} (hy : y ∈ U) (g : X.functionField) :
    UnitAt y g ↔ ∃ a b : Γ(X, U), a ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal ∧
      b ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal ∧ g * fnOf U (gen_mem hy) b = fnOf U (gen_mem hy) a := by
  constructor
  · intro hg
    obtain ⟨a, b, hb, e⟩ := (regAt_iff_frac hU hy g).1 hg.regAt
    refine ⟨a, b, ?_, hb, e⟩
    rw [← unitAt_fnOf_iff_not_mem hU hy, ← e]
    exact hg.mul (GlobalTheory.FieldPair.unitAt_fnOf_of_not_mem hU hy hb)
  · rintro ⟨a, b, ha, hb, e⟩
    have hu := GlobalTheory.FieldPair.unitAt_fnOf_of_not_mem hU hy hb
    have hua := GlobalTheory.FieldPair.unitAt_fnOf_of_not_mem hU hy ha
    have eg : g = fnOf U (gen_mem hy) a * (fnOf U (gen_mem hy) b)⁻¹ := by
      rw [← e, mul_inv_cancel_right₀ hu.ne_zero]
    rw [eg]
    exact hua.mul hu.inv

include hU in

theorem primeIdealOf_le_of_specializes {y z : X} (hy : y ∈ U) (hz : z ∈ U) (hzy : z ⤳ y) :
    (hU.primeIdealOf ⟨z, hz⟩).asIdeal ≤ (hU.primeIdealOf ⟨y, hy⟩).asIdeal := by
  intro s hs
  by_contra hs'
  rw [← GlobalTheory.DetHT.RegLoc.mem_basicOpen_iff hU hy] at hs'
  exact (GlobalTheory.DetHT.RegLoc.mem_basicOpen_iff hU hz s).1 (hzy.mem_open (X.basicOpen s).isOpen hs') hs

include hU in

theorem exists_specializes_of_le {y : X} (hy : y ∈ U) (Q : Ideal Γ(X, U)) (hQ : Q.IsPrime)
    (hQP : Q ≤ (hU.primeIdealOf ⟨y, hy⟩).asIdeal) :
    ∃ (z : X) (hz : z ∈ U), z ⤳ y ∧ (hU.primeIdealOf ⟨z, hz⟩).asIdeal = Q := by
  refine ⟨(GlobalTheory.QCoh.pointOfPrime hU ⟨Q, hQ⟩ : X), (GlobalTheory.QCoh.pointOfPrime hU ⟨Q, hQ⟩).2, ?_, ?_⟩
  · have h1 := ((PrimeSpectrum.le_iff_specializes ⟨Q, hQ⟩ (hU.primeIdealOf ⟨y, hy⟩)).mp hQP).map
      hU.fromSpec.continuous
    rw [hU.fromSpec_primeIdealOf ⟨y, hy⟩] at h1
    exact h1
  · rw [GlobalTheory.QCoh.primeIdealOf_pointOfPrime]

theorem isLogChart_of_isEtCoord : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsIntegral X]
    (f : X ⟶ Sp (ZMod p)) (U : X.Opens) (h : genericPoint X ∈ U) {n : ℕ} (t : Fin n → Γ(X, U))
    (x : Fin n → X.functionFieldˣ) (J : Finset (Fin n)) (Z : Set X), IsAffineOpen U →
    IsEtCoord f U t → (∀ j, (x j : X.functionField) = fnOf U h (t j)) →
    (∀ y ∈ U, y ∈ Z ↔ ∃ j ∈ J, ¬ UnitAt y (x j : X.functionField)) → IsLogChart Z U x J := by
  intro p _ X _ f U h n t x J Z hU hEt hx hZ
  haveI : Nonempty U := ⟨⟨_, h⟩⟩
  letI : Algebra (ZMod p) Γ(X, U) := (cstOn f U).toAlgebra
  haveI : IsFractionRing Γ(X, U) X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  have hEt' : (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale := hEt
  have hA : ∀ s : Γ(X, U), algebraMap Γ(X, U) X.functionField s = fnOf U h s := fun _ => rfl
  have ht : ∀ j, algebraMap Γ(X, U) X.functionField (t j) ≠ 0 := fun j => by
    rw [hA, ← hx j]; exact (x j).ne_zero
  have hxt : x = fun j => Units.mk0 _ (ht j) := funext fun j => Units.ext (hx j)
  have hB := GlobalTheory.T.fraction_field_coordinates_dlog p Γ(X, U) t hEt' X.functionField ht
  have hprod : ∀ S : Finset (Fin n),
      algebraMap Γ(X, U) X.functionField (∏ j ∈ S, t j) = ∏ j ∈ S, (x j : X.functionField) :=
    fun S => by rw [map_prod]; exact Finset.prod_congr rfl fun j _ => (hx j).symm
  refine ⟨fun y hy => ⟨fun i => ?_, ?_, ?_, ?_⟩, fun y hy g => ?_⟩
  · rw [hx i]; exact regAt_fnOf hy h (t i)
  · rw [hxt]; exact hB.1
  · intro g hg
    obtain ⟨a, b, hb, e⟩ := (regAt_iff_frac hU hy g).1 (mem_locRing.1 hg)
    obtain ⟨ca, hca⟩ := hB.2 a
    obtain ⟨cb, hcb⟩ := hB.2 b
    have hu := GlobalTheory.FieldPair.unitAt_fnOf_of_not_mem hU hy hb
    refine ⟨fun i => (fnOf U h b)⁻¹ * (fnOf U h (ca i) - g * fnOf U h (cb i)), fun i => ?_, ?_⟩
    · exact mul_mem (mem_locRing.2 hu.inv.regAt) (sub_mem (mem_locRing.2 (regAt_fnOf hy h _))
        (mul_mem hg (mem_locRing.2 (regAt_fnOf hy h _))))
    · have hB0 : fnOf U h b ≠ 0 := hu.ne_zero
      have key : dK g = (fnOf U h b)⁻¹ • (dK (fnOf U h a) - g • dK (fnOf U h b)) := by
        have e' : g * fnOf U h b = fnOf U h a := e
        rw [← e']
        simp only [dK, Derivation.leibniz]
        rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hB0, one_smul]
      simp only [hA] at hca hcb
      rw [key]
      simp only [dK] at hca hcb ⊢
      rw [hca, hcb, Finset.smul_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hx i, smul_smul, ← sub_smul, smul_smul, mul_comm g]
  · intro S g m hm hg
    obtain ⟨a, b, hb, e⟩ := GlobalTheory.T.root_of_monomial_quotient_integral p Γ(X, U) t hEt' (hU.primeIdealOf ⟨y, hy⟩).asIdeal
      X.functionField S g m hm (by
        obtain ⟨a, b, hb, e⟩ := (regAt_iff_frac hU hy _).1 (mem_locRing.1 hg)
        exact ⟨a, b, hb, by rw [hprod]; exact e⟩)
    exact mem_locRing.2 ((regAt_iff_frac hU hy _).2 ⟨a, b, hb, by rw [← hprod]; exact e⟩)
  · have hZc : ∀ z (hz : z ∈ U), z ∉ Z ↔ ∀ j ∈ J, t j ∉ (hU.primeIdealOf ⟨z, hz⟩).asIdeal := by
      intro z hz
      rw [hZ z hz]
      simp only [not_exists, not_and, not_not]
      refine forall₂_congr fun j _ => ?_
      rw [hx j]
      exact unitAt_fnOf_iff_not_mem hU hz (t j)
    have hU' := GlobalTheory.T.unit_of_height_one_primes p Γ(X, U) t hEt' (hU.primeIdealOf ⟨y, hy⟩).asIdeal X.functionField J ht g
    refine Iff.trans ?_ (hU'.trans ?_)
    · constructor
      · intro hL Q hQ hQP hJ
        obtain ⟨z, hz, hzy, rfl⟩ := exists_specializes_of_le hU hy Q hQ hQP
        exact (unitAt_iff_frac hU hz g).1 (hL z hzy ((hZc z hz).2 hJ))
      · intro hL z hzy hzZ
        have hz : z ∈ U := hzy.mem_open U.isOpen hy
        exact (unitAt_iff_frac hU hz g).2 (hL _ inferInstance
          (primeIdealOf_le_of_specializes hU hy hz hzy) ((hZc z hz).1 hzZ))
    · subst hxt
      exact exists_congr fun u => exists_congr fun m => and_congr_left' (unitAt_iff_frac hU hy u).symm

end GlobalTheory.EtLog
