import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GenMass

open Formalism.MainNotions.S.Loc

section General

theorem linInd_of_change {R W ι : Type} [CommRing R] [AddCommGroup W] [Module R W] [Fintype ι] [DecidableEq ι]
    {v w : ι → W} (B : Matrix ι ι R) (hB : IsUnit B.det) (hv : LinearIndependent R v)
    (hw : ∀ j, w j = ∑ i, B i j • v i) : LinearIndependent R w := by
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro g hg
  have h1 : ∑ i, (B.mulVec g) i • v i = 0 := by
    rw [← hg]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, hw, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  have h2 : B.mulVec g = 0 := funext (hv _ h1)
  have h3 : g = B⁻¹.mulVec (B.mulVec g) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hB, Matrix.one_mulVec]
  intro i
  rw [h3, h2, Matrix.mulVec_zero, Pi.zero_apply]

theorem isUnit_ringInverse_of_ne {R : Type} [CommRing R] {y : R} (h : Ring.inverse y ≠ 0) :
    IsUnit (Ring.inverse y) := by
  by_cases hy : IsUnit y
  · obtain ⟨u, rfl⟩ := hy
    rw [Ring.inverse_unit]
    exact Units.isUnit _
  · exact absurd (Ring.inverse_non_unit y hy) h

theorem det_uni_eq_one {K : Type} [CommRing K] {n : ℕ} {A : Matrix (Fin n) (Fin n) K} (hA : Uni A) :
    A.det = 1 := by
  obtain ⟨hlow, hdiag⟩ := hA
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => hlow i j hij)]
  simp [hdiag]

end General

section Main

variable {D : D7}

theorem exists_place (D : D7) : Nonempty (PlF D) := by
  obtain ⟨P, hne, hP⟩ :=
    Ring.not_isField_iff_exists_prime.1 (NumberField.RingOfIntegers.not_isField D.host.F)
  exact ⟨⟨P, hP, hne⟩⟩

private theorem linearIndependent_frameD_of_T_ne_zero {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}
    (Fr : LocNG.FrameD H r) (hT : Fr.T ≠ 0) : LinearIndependent E Fr.f := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have key : ∀ y, H.h (∑ i, g i • Fr.f i) y = ∑ i, g i * H.h (Fr.f i) y := by
    intro y
    have hs : ∀ s : Finset (Fin (r + 1)),
        H.h (∑ i ∈ s, g i • Fr.f i) y = ∑ i ∈ s, g i * H.h (Fr.f i) y := by
      intro s
      refine Finset.induction_on s (by simp [H.h_zero_left]) ?_
      intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]
    exact hs Finset.univ
  have hlast : g (Fin.last r) = 0 := by
    have hz := key (Fr.f (Fin.last r))
    rw [hg, H.h_zero_left, Fin.sum_univ_castSucc] at hz
    have hoff : ∀ i : Fin r, H.h (Fr.f i.castSucc) (Fr.f (Fin.last r)) = 0 :=
      fun i => Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last i))
    simp only [hoff, mul_zero, Finset.sum_const_zero, zero_add, Fr.h_zz] at hz
    have hu : IsUnit (-(algebraMap F E Fr.T)) := ((Ne.isUnit hT).map (algebraMap F E)).neg
    exact hu.mul_left_eq_zero.1 hz.symm
  intro i
  refine Fin.lastCases hlast (fun j => ?_) i
  have he := key (Fr.es j)
  rw [hg, H.h_zero_left, Fin.sum_univ_castSucc, hlast, zero_mul, add_zero] at he
  simp only [Fr.h_es, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at he
  exact he.symm

theorem local_pair_linInd (Z : LocDat D) (p : PlF D) (P : LocNG.FPair (locH Z p) D.R.rS)
    (hR : P.RelG (LocNG.theta (Z.M p))) :
    LinearIndependent (D.s.atP p).Ep (Sum.elim P.A.f P.B.f) := by
  obtain ⟨hX, -, -, -, -, -, hN⟩ := hR
  obtain ⟨-, hT, -, hT', -⟩ := hN
  exact LinearIndependent.sum_type (linearIndependent_frameD_of_T_ne_zero P.A hT) (linearIndependent_frameD_of_T_ne_zero P.B hT')
    (disjoint_iff.2 hX)

end Main

section Final

variable {D : D7}

theorem base_frames_linInd (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ)
    (F : LFlag (VS D) D.R.rS (Tn : D.host.E)) (F' : LFlag (VS D) D.R.rS (T'n : D.host.E))
    (hB : Based Z FP Tn T'n F F') (hR : ∀ p, (FP p).RelG (LocNG.theta (Z.M p))) :
    LinearIndependent D.host.E (Sum.elim (frame F) (frame F')) := by
  obtain ⟨p⟩ := exists_place D
  have hloc := local_pair_linInd Z p (FP p) (hR p)
  obtain ⟨hA, hA', -, -⟩ := hB p
  have hu : ∀ i, Sum.elim (FP p).A.f (FP p).B.f i =
      Sum.elim (frFac Z.δ p) (frFac Z.δ p) i • baseChange₂ D p (Sum.elim (frame F) (frame F') i) := by
    rintro (a | a)
    · simp only [Sum.elim_inl, hA]
    · simp only [Sum.elim_inr, hA']
  have hs : ∀ i, Ring.inverse (Sum.elim (frFac Z.δ p) (frFac Z.δ p) i) *
      Sum.elim (frFac Z.δ p) (frFac Z.δ p) i = 1 := by
    intro i
    have hne : Sum.elim (frFac Z.δ p) (frFac Z.δ p) i ≠ 0 := by
      intro h0
      apply hloc.ne_zero i
      rw [hu i, h0, zero_smul]
    refine Ring.inverse_mul_cancel _ ?_
    rcases i with a | a
    · exact isUnit_ringInverse_of_ne hne
    · exact isUnit_ringInverse_of_ne hne
  rw [Fintype.linearIndependent_iff] at hloc ⊢
  intro g hg
  have h1 : ∑ i, ((D.s.atP p).ιE (g i) * Ring.inverse (Sum.elim (frFac Z.δ p) (frFac Z.δ p) i)) •
      Sum.elim (FP p).A.f (FP p).B.f i = 0 := by
    have hmap := congrArg (baseChange₂ D p) hg
    rw [map_sum, map_zero] at hmap
    rw [← hmap]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hu i, smul_smul, mul_assoc, hs i, mul_one, baseChange_smul₂]
  intro i
  have h2 := hloc _ h1 i
  have h3 : (D.s.atP p).ιE (g i) = 0 := by
    have h4 := congrArg (· * Sum.elim (frFac Z.δ p) (frFac Z.δ p) i) h2
    simpa only [mul_assoc, hs i, mul_one, zero_mul] using h4
  exact (map_eq_zero_iff _ (D.s.atP p).ιE.injective).1 h3

theorem changed_frames_linInd : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ) (F G : LFlag (VS D) D.R.rS (Tn : D.host.E)) (F' G' : LFlag (VS D) D.R.rS (T'n : D.host.E)), Based Z FP Tn T'n F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → Tri D.host.E (frame F) (frame G) → Tri D.host.E (frame F') (frame G') → LinearIndependent D.host.E (Sum.elim (frame G) (frame G')) := by
  intro D Z FP Tn T'n F G F' G' hB hR hG hG'
  have hbase := base_frames_linInd Z FP Tn T'n F F' hB hR
  obtain ⟨A, hA, hcA⟩ := hG
  obtain ⟨A', hA', hcA'⟩ := hG'
  refine linInd_of_change (Matrix.fromBlocks A 0 0 A') ?_ hbase ?_
  · rw [Matrix.det_fromBlocks_zero₂₁, det_uni_eq_one hA, det_uni_eq_one hA', mul_one]
    exact isUnit_one
  · rintro (b | b)
    · simp only [Sum.elim_inl, Fintype.sum_sum_type, Sum.elim_inr, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
      exact hcA b
    · simp only [Sum.elim_inr, Fintype.sum_sum_type, Sum.elim_inl, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_smul, Finset.sum_const_zero, zero_add]
      exact hcA' b

end Final
end GlobalTheory.GenMass
