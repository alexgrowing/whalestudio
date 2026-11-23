import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoSidedHeckePartnerInertPrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdjoinSplitHeckeGeneratorsDualsSpherical
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeConjPlaceEqDualLabelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvectorAdjointIntertwinerNormalOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightCocharacterEqOfGoodPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftIntegOfCuspRapidDecay
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3.SplitLabels

open GlobalTheory.Hk3 GlobalTheory.Hk3.LabDet

theorem evC_single_lab {D : D7} (V : HSp D) (P : Pl D.host.E) (a : List ℤ → ℂ) (d : List ℤ) (hd : IsLab V P d) :
    evC V P a (Finsupp.single d 1) = a d := by
  unfold evC
  rw [Finsupp.sum_single_index (by simp), if_pos hd, one_mul]

theorem eq_of_split_vec : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (t : T) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ R.HE.H), (∀ P, GlobalTheory.Hk3.Good R t P → ∀ c x, R.HE.e (h P c x) = postOn (R.MY 0) (GlobalTheory.Hk3.hk (Yc D 0) P c) (R.HE.e x)) → ∀ P, GlobalTheory.Hk3.Good R t P → Formalism.DivisionValues.conjPl P ≠ P → ∀ (c : Pl D.host.E → List ℤ → ℂ) (x w : R.HE.H), x ≠ 0 → (∀ P', GlobalTheory.Hk3.Good R t P' → ∀ cc, h P' cc x = GlobalTheory.Hk3.evC (Yc D 0) P' (fun d => c P' (dualLab d)) cc • x) → (∀ k ≤ (Yc D 0).rank, h P (Finsupp.single (splitLab (Yc D 0).rank k) 1) w = GlobalTheory.Hk3.evC (Yc D 0) P (fun d => c P (dualLab d)) (Finsupp.single (splitLab (Yc D 0).rank k) 1) • w ∧ h (Formalism.DivisionValues.conjPl P) (Finsupp.single (splitLab (Yc D 0).rank k) 1) w = GlobalTheory.Hk3.evC (Yc D 0) (Formalism.DivisionValues.conjPl P) (fun d => c (Formalism.DivisionValues.conjPl P) (dualLab d)) (Finsupp.single (splitLab (Yc D 0).rank k) 1) • w) → ∀ d, GlobalTheory.Hk3.IsLab (Yc D 0) P d → h P (Finsupp.single d 1) w = c P (dualLab d) • w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t h hh P hP hcP c x w hx0 hxe hw d hd
  obtain ⟨-, hgood, -, -⟩ := GlobalTheory.T.theta_lift_levels_good_primes_properties R F hC.lev
  have hPA : Good R A.μ0 P := (hgood t P hP).2.2
  have hPc : Good R t (Formalism.DivisionValues.conjPl P) := (hgood t P hP).2.1
  obtain ⟨n, hβ⟩ := hC.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  have hlev := GlobalTheory.T.level_operators_at_prime_off_level_datum (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hβ P
    (by rw [Nat.cast_pow]; exact fun hm => (hgood _ P hPA).1 (P.isPrime.mem_of_pow_mem n hm))
    (fun PP hPP => hPA PP (hPP.imp id fun h => absurd h (Finset.notMem_empty _)))
  have inj : Function.Injective R.HE.e := hC.models.HE.1
  have hmem : ∀ y, R.HE.e y ∈ Mult R.θ (R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) :=
    fun y => goodPart_le _ _ _ _ _ (hC.models.HE.2.1 ▸ LinearMap.mem_range_self _ y)
  have hfix : ∀ y, ∀ k ∈ hyp (Yc D 0) P, rRep (R.MY 0) k (R.HE.e y) = R.HE.e y := fun y k hk =>
    mult_lev _ _ _ _ _ (hmem y) k (hlev.1 k hk).1 (hlev.1 k hk).2
  have hop : ∀ P', Good R t P' → ∀ e y, opOf (rRep (R.MY 0)) P' (Finsupp.single e 1) (R.HE.e y) =
      R.HE.e (h P' (Finsupp.single e 1) y) := by
    intro P' hP' e y
    rw [opOf_single, sum_rRep, hh P' hP', GlobalTheory.Hk3.OpsRows.hk_single]
    rfl
  have hu : R.HE.e x ≠ 0 := fun h0 => hx0 (inj (by rw [h0, map_zero]))
  obtain ⟨a, ha, hae⟩ := GlobalTheory.SplitGen.gen_split (Yc D 0) P hcP (MMap (R.MY 0)) (rRep (R.MY 0)) d
  obtain ⟨l, h1, h2⟩ := adjoin_common _ (R.HE.e x) (R.HE.e w) (by
    rintro y ⟨k, hk, rfl | rfl⟩
    · refine ⟨evC (Yc D 0) P (fun d => c P (dualLab d)) (Finsupp.single (splitLab (Yc D 0).rank k) 1), ?_, ?_⟩
      · rw [hop P hP, hxe P hP, map_smul]
      · rw [hop P hP, (hw k hk).1, map_smul]
    · have hc := (GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel (Yc D 0) P).2.2 (Finsupp.single (splitLab (Yc D 0).rank k) 1) _ (rRep (R.MY 0))
      have hdc : dualC (Finsupp.single (splitLab (Yc D 0).rank k) 1) =
          Finsupp.single (dualLab (splitLab (Yc D 0).rank k)) 1 := by
        unfold dualC
        rw [Finsupp.mapDomain_single]
      rw [hdc] at hc
      rw [← hc _ (hfix x), ← hc _ (hfix w)]
      refine ⟨evC (Yc D 0) (Formalism.DivisionValues.conjPl P) (fun d => c (Formalism.DivisionValues.conjPl P) (dualLab d))
        (Finsupp.single (splitLab (Yc D 0).rank k) 1), ?_, ?_⟩
      · rw [hop _ hPc, hxe _ hPc, map_smul]
      · rw [hop _ hPc, (hw k hk).2, map_smul]) a ha
  rw [hae _ (hfix x), hop P hP, hxe P hP, evC_single_lab _ _ _ _ hd, map_smul] at h1
  have hl : l = c P (dualLab d) := (smul_left_injective ℂ hu h1).symm
  rw [hae _ (hfix w), hop P hP, hl, ← map_smul] at h2
  exact inj h2

end GlobalTheory.Hk3.SplitLabels

end
