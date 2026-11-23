import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedWeilDivisorSumSymmNoCommonDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightOneIffPointClosureDimProjArithStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithAmbientVerticalOrArithmeticVarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchRestrictedEqZeroOfNoComplexPointsStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

set_option autoImplicit false

theorem mixRecVal_cons_eq_resCyc_sub_resArch {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} (hA : IsAmb q) {e : ℕ} (hdim : topologicalKrullDim Y = (e + 1 + 1 : ℕ))
    {T : ∀ d : ℕ, (Fin d → HermLB q) → Y → ℝ} (hT : IsMix q (e + 1) T) (N : HermLB q) (L : Fin e → HermLB q)
    (t : N.B.Sec) {z : Y} (hz : Order.coheight z = 1) (hzt : z ∈ nonzeroLocus t) :
    T (e + 1) (Fin.cons N L) z = resCyc N.isLB t (T e L) z - resArch L N t z := by
  have hg : genericPoint (clo z) ∈ nonzeroLocus (secPull t (cloι z)) := by
    rw [GlobalTheory.nonzeroLocus_secPull]
    show cloι z (genericPoint (clo z)) ∈ nonzeroLocus t
    rw [cloι_genericPoint]
    exact hzt
  have hd : topologicalKrullDim (clo z) = ((e + 1 : ℕ) : WithBot ℕ∞) :=
    ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Y q hA (e + 1) hdim).2 z (genericPoint (clo z)) hz).1
  have h := hT.recur (clo z) (cloι z ≫ q) (cloι z) rfl e le_rfl hd N L (N.restr (cloι z))
    (fun a => (L a).restr (cloι z)) (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) _
    (isRatSec_ratOfSec _ hg)
  rw [cloι_genericPoint] at h
  rw [h, resCyc, resArch, dif_pos hg, dif_pos hg]
  rfl

end GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem finite_support_mult_mul {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [CompactSpace Y]
    (D : CartierDiv Y) (g : Y → ℝ) : (Function.support fun z => (D.mult z : ℝ) * g z).Finite :=
  D.finite_support_mult.subset fun z hz => by
    simp only [Function.mem_support] at hz ⊢
    intro h
    simp [h] at hz

theorem recVal_cons_recip : ArchRecip → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T, IsMix q (e + 1) T → ∀ (M N : HermLB q) (L : Fin e → HermLB q) (s : M.B.Sec) (t : N.B.Sec) (hs : genericPoint Y ∈ nonzeroLocus s) (ht : genericPoint Y ∈ nonzeroLocus t), (∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M (isRatSec_ratOfSec s hs) = recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N (isRatSec_ratOfSec t ht) := by
  intro hAR k _ Y _ _ q hA e hdim T hT M N L s t hs ht hcov
  have : IsNoetherian Y := hA.isNoetherian
  have key (A B : HermLB q) (a : A.B.Sec) (b : B.B.Sec) (ha : genericPoint Y ∈ nonzeroLocus a)
      (hab : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus a ∨ z ∈ nonzeroLocus b) (z : Y) :
      ((divOfSec A.isLB a ha).mult z : ℝ) * T (e + 1) (Fin.cons B L) z =
        ((divOfSec A.isLB a ha).mult z : ℝ) * resCyc B.isLB b (T e L) z -
          ((divOfSec A.isLB a ha).mult z : ℝ) * resArch L B b z := by
    by_cases h0 : (divOfSec A.isLB a ha).mult z = 0
    · simp [h0]
    · have hz := CartierDiv.coheight_eq_one_of_mult_ne_zero h0
      have hza : z ∉ nonzeroLocus a := fun h =>
        (notMem_supp_divOfSec.2 h) (CartierDiv.mem_supp_of_mult_ne_zero h0)
      rw [mixRecVal_cons_eq_resCyc_sub_resArch hA hdim hT B L b hz ((hab z hz).resolve_left hza), mul_sub]
  have hL : recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M (isRatSec_ratOfSec s hs) =
      (∑ᶠ z, ((divOfSec M.isLB s hs).mult z : ℝ) * resCyc N.isLB t (T e L) z -
        ∑ᶠ z, ((divOfSec M.isLB s hs).mult z : ℝ) * resArch L N t z) -
        mixArch (Fin.cons N L : Fin (e + 1) → HermLB q) M (isRatSec_ratOfSec s hs) := by
    rw [recVal, finsum_congr (key M N s t hs hcov), finsum_sub_distrib (finite_support_mult_mul _ _)
      (finite_support_mult_mul _ _)]
  have hR : recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N (isRatSec_ratOfSec t ht) =
      (∑ᶠ z, ((divOfSec N.isLB t ht).mult z : ℝ) * resCyc M.isLB s (T e L) z -
        ∑ᶠ z, ((divOfSec N.isLB t ht).mult z : ℝ) * resArch L M s z) -
        mixArch (Fin.cons M L : Fin (e + 1) → HermLB q) N (isRatSec_ratOfSec t ht) := by
    rw [recVal, finsum_congr (key N M t s ht fun z hz => (hcov z hz).symm),
      finsum_sub_distrib (finite_support_mult_mul _ _) (finite_support_mult_mul _ _)]
  have hC := GlobalTheory.T.iteratedWeilDivisorSum_symm_no_common_divisor k Y q hA M.B N.B M.isLB N.isLB s t hs ht hcov (T e L)
  rw [hL, hR, hC]
  rcases GlobalTheory.T.projArithAmbient_vertical_or_arithmeticVariety k Y q hA (e + 1 + 1) hdim with ⟨l, _, _, hno⟩ | ⟨e', he', hav⟩
  · have z₀ := GlobalTheory.T.mixedArch_restricted_eq_zero_of_no_complexPoints k Y q hno
    rw [(z₀ (e + 1) (Fin.cons N L) M).1, (z₀ (e + 1) (Fin.cons M L) N).1]
    simp only [(z₀ e L N).2, (z₀ e L M).2, mul_zero, finsum_zero]
  · obtain rfl : e' = e + 1 := by omega
    have hA' := hAR k Y q e hav M N L s t hs ht hcov
    linarith

end GlobalTheory.MixHt
