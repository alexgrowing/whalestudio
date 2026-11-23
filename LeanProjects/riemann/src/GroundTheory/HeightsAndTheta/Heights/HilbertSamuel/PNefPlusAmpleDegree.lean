import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefPlusAmpleDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenDegAmple
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftDegreePolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefAmpleGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCurvePointsFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegTwist
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

namespace NefPlusAmpleDegree

theorem genDeg_one_pos (hA : GenDegAmple.Statement) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {W : Ideal (MRing ι)} {d : ℕ} (hW : IsArithVar W (d + 1)) :
    0 < genDeg W d 1 := by
  have : W.IsPrime := hW.2.1.1
  have hEq := CurvePointsFinite.mCoordIdeal_genericPt W hW.2.1.2.1
  have hV : IsArithVar (mCoordIdeal (CurvePointsFinite.genericPt W)) (d + 1) := by rw [hEq]; exact hW
  have h := hA K ι _ (CurvePointsFinite.genericPt W) d 1 hV fun _ => le_rfl
  rwa [hEq] at h

open Classical in

theorem nefOnF_of_nefOnGenericDeg {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {b : K → ℤ} (hb : NefOnGenericDeg P b) :
    KH.NefOnF (fun V _ L => NumbersDVR.intNum ℚ V L) (P.map (MvPolynomial.map (Int.castRingHom ℚ))) b := by
  intro W hW hle
  obtain ⟨hWar, hWmap⟩ := NefAmpleGeneric.isArithVar_comap_of_isProjVarF hW
  have hPW : P ≤ W.comap (MvPolynomial.map (Int.castRingHom ℚ)) := Ideal.map_le_iff_le_comap.mp hle
  have h := hb _ hWar hPW
  rw [genDeg, hWmap] at h
  have hL : (fun _ : Fin 1 => b) = ![b] := by
    funext j
    fin_cases j
    rfl
  rw [hL] at h
  exact h

end NefPlusAmpleDegree

theorem NefPlusAmpleDegree.proof (hK : KH.KleimanNefFStatement) (hA : GenDegAmple.Statement) :
    NefPlusAmpleDegree.Statement := by
  classical
  intro K _ ι _ P D a hP hnef q
  have : Nonempty K := hP.1
  set Q := P.map (MvPolynomial.map (Int.castRingHom ℚ)) with hQ
  obtain ⟨hprime, hdimq⟩ := ShiftDegreePolynomial.genericFibre hP
  have hd : FieldNumbers.relDim Q = D := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq _ _ hdimq]
    simp only [Nat.cast_add, add_sub_cancel_right]
    rfl
  let f : (Fin D → K → ℤ) → ℤ := fun bs => NumbersDVR.intNum ℚ Q bs
  have hadd : ∀ (bs : Fin D → K → ℤ) (j : Fin D) (x y : K → ℤ),
      f (Function.update bs j (x + y)) = f (Function.update bs j x) + f (Function.update bs j y) :=
    fun bs j x y => FieldNumbers.IntNumAdd.full ℚ K ι Q hprime.multiHomog hprime.relevant D hd bs j x y
  let I : IFamily ℚ ι := fun V _ L => NumbersDVR.intNum ℚ V L
  have hI : IsFieldIntersection I := NumbersDVR.IntNumIsFieldIntersection.full ℚ K ι
  have hPV : IsProjVarF Q D := isProjVarF_map_of_isArithVar hP
  have hnefA : KH.NefOnF I Q a := NefPlusAmpleDegree.nefOnF_of_nefOnGenericDeg hnef
  have hnefH : KH.NefOnF I Q 1 := NefPlusAmpleDegree.nefOnF_of_nefOnGenericDeg fun W hW _ =>
    (NefPlusAmpleDegree.genDeg_one_pos hA hW).le
  have hterm : ∀ s : Finset (Fin D), 0 ≤ f (s.piecewise (fun _ => a) (fun _ => 1)) := by
    intro s
    refine hK ℚ K ι I Q D _ hI hPV fun i => ?_
    by_cases hi : i ∈ s
    · simpa [Finset.piecewise, hi] using hnefA
    · simpa [Finset.piecewise, hi] using hnefH
  have hg : genDeg P D ((q : ℤ) • a + 1) = f (fun _ => (q : ℤ) • a + 1) := rfl
  rw [hg, ShiftDegreePolynomial.expand f hadd (q : ℤ) a 1]
  refine Finset.sum_pos' (fun s _ => mul_nonneg (pow_nonneg (Int.natCast_nonneg q) _) (hterm s))
    ⟨∅, Finset.mem_univ _, ?_⟩
  rw [Finset.card_empty, pow_zero, one_mul, Finset.piecewise_empty]
  exact NefPlusAmpleDegree.genDeg_one_pos hA hP

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
