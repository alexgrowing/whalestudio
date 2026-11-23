import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsSmallOfArVolPPos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTopConstantTwist
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBirationalModelExists
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionPointHeight
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionOrderAtPoint
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCurvePointsFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefOnGenericOfSemipos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology
open GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.LatticeWithoutBigness

noncomputable section

theorem Z2.proof (hMo : MoriwakiBigStatement) : SuccessiveMinimaUpperBound := by
  have hG : ArithmeticVolumeBig.Statement := ArithmeticVolumeBig.of_moriwakiBig NefOnGenericOfSemipos.proof hMo
  have hT : TopConstantTwist.Statement := TopConstantTwist.proof
  have hM : BirationalModelExists.Statement := BirationalModelExists.proof
  have hS : SmallSectionPointHeight.Statement := SmallSectionPointHeight.proof SectionOrderAtPoint.proof
  have hfin : CurvePointsFinite.Statement := CurvePointsFinite.proof
  intro K _ ι _ P P0 D A e' F II hII har hP0 hsemi hnef hconj hF hdense
  have hA : IsSmoothHerm A := hsemi.1
  have : Nonempty K := har.1

  have hdeg : ∀ W : Ideal (MRing ι), IsArithVar W 1 → (0 : ℝ) < degC W := by
    intro W hW
    have : Finite (projPts W) := hfin K ι W hW
    obtain ⟨z, hz⟩ := IndefiniteRowSideFullHecke.HeightsSet.CurveComplexPoint.full K ι W hW
    have : Nonempty (projPts W) := ⟨Quot.mk _ ⟨z, hz⟩⟩
    have : 0 < Nat.card (projPts W) := Nat.card_pos
    exact_mod_cast this

  have hmc : ∀ W : Ideal (MRing ι), IsArithVar W 1 → ∀ c : ℝ, II K ι W 1 ![A.tensor (constLine c)] =
      II K ι W 1 ![A] - ptsIntegral (e := 0) W (pot (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι))
        (fun _ => c) := by
    intro W hW c
    have h := metricChange K ι (II K ι) (hII K ι) W 0 ![] A (fun _ => c) (fun _ _ _ => rfl) hW
      (fun j => j.elim0) hA contDiffOn_const
    have e1 : ∀ B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι,
        (Fin.snoc (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) B : Fin (0 + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
          = ![B] := fun B => by
      funext i
      fin_cases i
      rfl
    rw [e1, e1] at h
    exact h
  have hlow : ∀ W : Ideal (MRing ι), IsArithVar W 1 → ∀ c : ℝ,
      c * degC W ≤ ptsIntegral (e := 0) W (pot (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)) (fun _ => c) := by
    intro W hW c
    exact PtsIntegralZeroLowerNE.proof K ι W _ (fun _ => c) c hW.2.1.2.1 (hfin K ι W hW)
      (fun _ _ _ _ => rfl) (fun _ _ => le_rfl)
  have h1P : (1 : MRing ι) ∉ P := fun h => har.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  have hfun : ∀ B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, (fun _ : Fin 1 => B) = ![B] := fun B => by
    funext i
    fin_cases i
    rfl
  rcases Nat.eq_zero_or_pos D with hD | hD
  ·
    subst hD
    obtain ⟨W, hWF, -⟩ := hdense 1 ⟨fun _ => 0, ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_one⟩ h1P
    obtain ⟨hW, hPW, hle⟩ := hF W hWF
    have : P.IsPrime := har.2.1.1
    have hWP : P = W :=
      CurveIsOrbit.eq_of_le_of_ringKrullDim_eq (d := 1 + Fintype.card K) hPW har.2.2.2 hW.2.2.2
    rw [← hWP] at hle
    have htw : II K ι P 1 (fun _ => A.tensor (constLine e')) =
        II K ι P 1 (fun _ => A) - ((1 : ℕ) : ℝ) * e' * geomDeg P A 0 := hT K ι P 0 A e' II hII har hA
    rw [hfun, hfun] at htw
    have hm := hmc P har e'
    have hl := hlow P har e'
    show II K ι P 1 (fun _ => A) ≤ ((1 : ℕ) : ℝ) * e' * geomDeg P A 0
    rw [hfun]
    push_cast at htw ⊢
    linarith
  ·
    obtain ⟨Ω, _, y, hyP, hbir⟩ := hM K ι P (D + 1) har
    subst hyP
    by_contra hlt
    push Not at hlt
    obtain ⟨e'', hgt, htop⟩ := exists_gt_of_lt (N := ((D + 1 : ℕ) : ℝ)) (by positivity) hlt
    have htw := hT K ι (mCoordIdeal y) D A e'' II hII har hA
    have hvol := hG K ι Ω y D (A.tensor (constLine e'')) P0 II hD hII har hbir hP0
      (isSemipositiveRel_twist hsemi e'') (nefOnFibres_twist hnef e'') (isConjInvariantH_twist hconj e'')
    have hpos : 0 < arVolP (IsSmallH (mCoordIdeal y) y (A.tensor (constLine e'')))
        (chartLat y (A.tensor (constLine e'')).a) 1 D := by
      linarith
    obtain ⟨τ, hτ, s, hsL, hs0, hsm⟩ := exists_small_section_of_arithmeticVolume_pos hpos
    obtain ⟨f, hfh, hfP, hfW⟩ := hS K ι Ω y D (A.tensor (constLine e'')) τ s II hII har hbir
      (isSmoothHerm_twist hA e'') hτ (SmallSectionPointHeight.chartLat_le_chartLatNm _ _ _ hsL) hs0 hsm
    obtain ⟨W, hWF, hfW'⟩ := hdense f hfh hfP
    obtain ⟨hW, hPW, hle⟩ := hF W hWF
    have h0 := hfW W hW hPW hfW'
    have hm := hmc W hW e''
    have hl := hlow W hW e''
    have hd := hdeg W hW
    nlinarith [mul_pos (sub_pos.mpr hgt) hd]

end

end GroundTheory.Heights₂.Heights.ForSecondHalf
