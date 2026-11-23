import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.AmpleDominates

open GlobalTheory.CechPic GlobalTheory.AbLaw

variable {X : Scheme.{0}} {M N : LB X}

theorem eventually_isGenerated {R : Type} [CommRing R] (f : X ⟶ Sp R) [IsProper f] (hM : IsAmpleLB M)
    (hN : N.IsLB) : ∀ᶠ t : ℕ in Filter.atTop, IsGenerated (LB.div (lbPow M t) N) := by
  obtain ⟨d, hd, m, s, hs⟩ := hM.exists_veryAmpleBy f
  have hH := isLB_lbPow hM.isLB d
  have hD : ∀ i, (LB.div (lbPow M i) N).IsLB := fun i => LB.isLB_div (isLB_lbPow hM.isLB i) hN
  choose t₀ ht₀ using fun i => TwistGen.twist_generated R X f _ m s hH hs _ (hD i)
  refine Filter.eventually_atTop.2 ⟨d * (Finset.range d).sup fun i => (t₀ i).toNat, fun t ht => ?_⟩
  have h₁ : (t₀ (t % d)).toNat ≤ t / d :=
    (Finset.le_sup (f := fun i => (t₀ i).toNat) (Finset.mem_range.2 (Nat.mod_lt t hd))).trans
      ((Nat.le_div_iff_mul_le hd).2 (by rwa [Nat.mul_comm]))
  obtain ⟨n, u, hu⟩ := ht₀ (t % d) (t / d : ℕ) (Int.toNat_le.1 h₁)
  have hG : IsGenerated (tw (LB.div (lbPow M (t % d)) N) (lbPow M d) (t / d : ℕ)) := ⟨_, u, hu⟩
  refine hG.of_lbIso (hD t) ((cls_eq_iff (hD t) hG.isLB).1 ?_)
  have e : cls _ hG.isLB = cls _ (hD (t % d)) - cls _ (isLB_pw hH (-((t / d : ℕ) : ℤ))) :=
    cls_div (hD _) (isLB_pw hH _) _
  rw [e, AmpleStabFinite.cls_pw hH, cls_div (isLB_lbPow hM.isLB t) hN, cls_div (isLB_lbPow hM.isLB _) hN,
    cls_lbPow hM.isLB, cls_lbPow hM.isLB, cls_lbPow hM.isLB]
  generalize cls M hM.isLB = a
  generalize cls N hN = b
  conv_lhs => rw [← Nat.mod_add_div t d]
  module

theorem eventually_isAmpleLB {R : Type} [CommRing R] (f : X ⟶ Sp R) [IsProper f] (hM : IsAmpleLB M)
    (hN : N.IsLB) : ∀ᶠ t : ℕ in Filter.atTop, IsAmpleLB (LB.div (lbPow M t) N) := by
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 (eventually_isGenerated f hM hN)
  refine Filter.eventually_atTop.2 ⟨a + 1, fun t ht => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  have hG := ha k (by omega)
  have h₀ := LB.isLB_div (isLB_lbPow hM.isLB (k + 1)) hN
  have h₁ := LB.isLB_div h₀ hM.isLB
  refine hM.tensor_isGenerated hG h₀ ((cls_eq_zero_iff (LB.isLB_div h₁ hG.isLB)).1 ?_)
  rw [cls_div h₁ hG.isLB, cls_div h₀ hM.isLB, cls_div (isLB_lbPow hM.isLB _) hN,
    cls_div (isLB_lbPow hM.isLB _) hN, cls_lbPow hM.isLB, cls_lbPow hM.isLB]
  module

theorem exists_sec_ne_zero [Nonempty X] {L : LB X} (h : IsGenerated L) : ∃ s : L.Sec, ∃ j, s.f j ≠ 0 := by
  obtain ⟨s, hs⟩ := h.exists_mem (Classical.arbitrary X)
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hs
  refine ⟨s, j, fun e => ?_⟩
  rw [e, Scheme.basicOpen_zero] at hj
  exact hj

theorem eventually_sec_and_relAmple : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M N : LB P.A.left), M.IsLB → N.IsLB → Out.RelAmple P.A M → ∀ᶠ t : ℕ in Filter.atTop, (∃ s : (LB.div (lbPow M t) N).Sec, ∃ j, s.f j ≠ 0) ∧ Out.RelAmple P.A (LB.div (lbPow M t) N) := by
  intro K _ _ P M N hM hN h
  have := P.isAb.proper
  have := polAV_isIntegral_of_isAlgClosed K P
  have hA := isAmpleLB_of_relAmple_of_isAffine P.A hM h
  filter_upwards [eventually_isGenerated P.A.hom hA hN, eventually_isAmpleLB P.A.hom hA hN] with t h₁ h₂
  exact ⟨exists_sec_ne_zero h₁, (relAmple_iff_isAmpleLB_of_isAffine P.A h₂.isLB).2 h₂⟩

end GlobalTheory.AmpleDominates
