import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitriangularFramesGramEqCellPointStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeRationalFlagIffRationalUnipot
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalisedBaseFramesRelevantPairStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnsignedLocalTermRowLatticeIsTerm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinitePlacesNotPrimeToBaseFrameInvariantsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitriangularFrameChangeLocalScalings
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDatumOfTwoCongruentFramesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameWitnessIntegralChangeStatement

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.BaseTerm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tri_symm {K W : Type} [CommRing K] [AddCommGroup W] [Module K W] {n : ℕ} {f g : Fin n → W}
    (h : Tri K f g) : Tri K g f := by
  obtain ⟨A, hA, hc⟩ := h
  have hinv := inv_unitri A hA.1 hA.2
  have hbt : A.BlockTriangular id := fun i j hij => hA.1 i j hij
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_upperTriangular hbt]; simp [hA.2]
  have hu : IsUnit A.det := by rw [hdet]; exact isUnit_one
  refine ⟨A⁻¹, hinv, fun b => ?_⟩
  have hm := Matrix.mul_nonsing_inv A hu
  have key : ∀ c, ∑ a, A c a * A⁻¹ a b = if c = b then (1 : K) else 0 := fun c => by
    rw [← Matrix.mul_apply, hm, Matrix.one_apply]
  calc f b = ∑ c, (if c = b then (1 : K) else 0) • f c := by simp
    _ = ∑ c, (∑ a, A c a * A⁻¹ a b) • f c := by simp only [key]
    _ = ∑ a, A⁻¹ a b • ∑ c, A c a • f c := by
      simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by rw [mul_comm]
    _ = ∑ a, A⁻¹ a b • g a := Finset.sum_congr rfl fun a _ => by rw [hc a]

theorem tri_refl (K : Type) {W : Type} [CommRing K] [AddCommGroup W] [Module K W] {n : ℕ} (f : Fin n → W) :
    Tri K f f := by
  refine ⟨1, ⟨fun a b h => Matrix.one_apply_ne (ne_of_lt h).symm, fun a => Matrix.one_apply_eq a⟩, fun b => ?_⟩
  simp [Matrix.one_apply, ite_smul, Finset.sum_ite_eq']

theorem finrank_Vp_eq {D : D7} (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  unfold Ranks.r Ranks.rS
  obtain ⟨j, hj⟩ := D.R.m_even
  have := D.R.two_le_m
  omega

end GlobalTheory.BaseTerm

namespace GlobalTheory.BaseTerm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem base_data_of_global_term : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E), PD D Λ (lf D F0) u' F' → Gval (lf D F0) F' ≠ 0 → ∀ w : Point D.host.E (D.R.rS + 1), IsInCell (ZhatOM (ZhatL (lf D F0) F')) w → ∃ (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 F'1 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (d0 : ∀ p, LocNG.Datum (FP p)), (∃ n ∈ Formalism.L2.SG.NGData.NRat (lf D F0), ∀ a, frame F00 a = n (frame (lf D F0) a)) ∧ ZhatOM (ZhatL F00 F'0) = ptMat w ∧ Gval F00 F'0 ≠ 0 ∧ IsInCell (ZhatOM (ZhatL (lf D F0) F'1)) w ∧ (∀ p, AtBase Z p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Z.M p)) ∧ LocNG.IsTermOver (FP p) (d0 p) (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) ∧ (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f' = scaled Z p (frame F'1)) ∧ {p : PlF D | ¬ ((FP p).PrimeTo ∧ LocNG.IsTermOver (FP p) (d0 p) ⟨lattice₂ D Z.M p Λ, scaled Z p (frame F00), scaled Z p (frame F'0), ((Tu D u : ℕ) : (D.s.atP p).Fp), ((Tu D u' : ℕ) : (D.s.atP p).Fp)⟩)}.Finite := by
  intro D Z u u' F0 Λ hR F' hPD hG w hw
  have hT : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (Formalism.L2.SG.GramJoint.Tu_pos D u).ne'
  have hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (Formalism.L2.SG.GramJoint.Tu_pos D u').ne'

  have hu := admissibility_witness_unitriangular Λ (lf D F0) F'
  have hinv := inv_unitri _ hu.1 hu.2
  have hA1 : Uni ((admXi D Λ (lf D F0) F')⁻¹.map (fun x : 𝓞 D.host.E => (x : D.host.E))) :=
    ⟨fun a b h => by simp [hinv.1 a b h], fun a => by simp [hinv.2 a]⟩
  obtain ⟨F'1, hF'1⟩ := (GlobalTheory.FlagChange.flag_change D F' hT').1 _ hA1
  have hfr1 : frame F'1 = frameAct (frame F') (admXi D Λ (lf D F0) F')⁻¹ := funext fun b => (hF'1 b).trans rfl
  have hTri1 : Tri D.host.E (frame F') (frame F'1) := ⟨_, hA1, hF'1⟩

  obtain ⟨-, hB1⟩ := GlobalTheory.T.exists_unitriangular_frames_gram_eq_cell_point D (lf D F0) F' w hT hT' hw
  obtain ⟨hw1, hG1⟩ := hB1 (lf D F0) F'1 (tri_refl _ _) hTri1
  obtain ⟨⟨F00, F'0, hTa, hTb, hpt⟩, hB2⟩ := GlobalTheory.T.exists_unitriangular_frames_gram_eq_cell_point D (lf D F0) F'1 w hT hT' hw1
  have hG0 : Gval F00 F'0 ≠ 0 := by rw [(hB2 F00 F'0 hTa hTb).2, hG1]; exact hG
  obtain ⟨n, hn, hnf⟩ := ((GlobalTheory.FlagChange.flag_change D (lf D F0) hT).2 F00).1 hTa

  have hFP := GlobalTheory.T.localisedBaseFrames_relevantPair D Z u u' w F00 F'0 hpt hG0
  choose FP hFPb using fun p => (hFP p).1
  have hFPr : ∀ p, (FP p).RelG (LocNG.theta (Z.M p)) := fun p => (hFP p).2 _ (hFPb p)
  have hIT := GlobalTheory.LocOver.locU_isTerm D Z u u' F0 Λ hR F' hPD hG
  have hf'eq : ∀ p, (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f' = scaled Z p (frame F'1) := by
    intro p
    funext b
    show frFac Z.δ p b • baseChange₂ D p (frameAct (frame F') (admXi D Λ (lf D F0) F')⁻¹ b) =
      frFac Z.δ p b • baseChange₂ D p (frame F'1 b)
    rw [hfr1]

  obtain ⟨Ba, hBa, hBac⟩ := tri_symm hTa
  obtain ⟨Bb, hBb, hBbc⟩ := tri_symm hTb
  obtain ⟨Pa, hPa, -⟩ := GlobalTheory.LocOver.tri_scaled D Z _ _ Ba hBa hBac
  obtain ⟨Pb, hPb, -⟩ := GlobalTheory.LocOver.tri_scaled D Z _ _ Bb hBb hBbc
  have hd : ∀ p, ∃ d : LocNG.Datum (FP p), LocNG.IsTermOver (FP p) d (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) := by
    intro p
    refine GlobalTheory.T.exists_datum_of_two_congruent_frames (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS (FP p) _ (hIT p).1 ?_ ?_ ?_ ?_
    · exact (hFPb p).2.2.1.symm
    · exact (hFPb p).2.2.2.symm
    · rw [(hFPb p).1]; exact ⟨Pa p, (hPa p).1, (hPa p).2⟩
    · rw [(hFPb p).2.1, hf'eq p]; exact ⟨Pb p, (hPb p).1, (hPb p).2⟩
  choose d0 hd0 using hd
  refine ⟨F00, F'0, F'1, FP, d0, ⟨n, hn, hnf⟩, hpt, hG0, hw1, fun p => ⟨hFPb p, hFPr p, hd0 p, hf'eq p⟩, ?_⟩

  obtain ⟨Aa, hAa, hAac⟩ := hTa
  obtain ⟨Ab, hAb, hAbc⟩ := hTb
  obtain ⟨Qa, hQa, hQaf⟩ := GlobalTheory.LocOver.tri_scaled D Z _ _ Aa hAa hAac
  obtain ⟨Qb, hQb, hQbf⟩ := GlobalTheory.LocOver.tri_scaled D Z _ _ Ab hAb hAbc
  have hPr := GlobalTheory.T.finite_places_not_primeTo_baseFrameInvariants D Z u u' F00 F'0 hG0 FP hFPb
  refine ((hPr.union hQaf).union hQbf).subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp
  simp only [Set.mem_union, Set.mem_setOf_eq]
  by_contra hc
  push_neg at hc
  obtain ⟨⟨hpr, hqa⟩, hqb⟩ := hc
  apply hp
  refine ⟨hpr, ?_⟩
  have hsplit : (Z.M p).split = none := hpr.1
  have hth : LocNG.theta (Z.M p) = 1 := by unfold LocNG.theta; rw [hsplit]
  refine GlobalTheory.T.hermitian_frame_witness_integral_change (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) (finrank_Vp_eq p) (hFPr p) (d0 p)
    (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) (hd0 p) (Qa p) (Qb p) _ _ (hQa p).1 (hQb p).1 ?_ (hQa p).2 ?_
  · intro a b
    refine ⟨hqa a b, hqb a b, ?_⟩
    rw [hth, map_one]
    exact Submodule.mem_span_singleton.mpr ⟨⟨Qa p a b - Qb p a b, sub_mem (hqa a b) (hqb a b)⟩, by
      first
        | exact (Subring.smul_def _ _).trans (mul_one _)
        | exact mul_one _
        | (show _ * _ = _; exact mul_one _)
        | rfl⟩
  · rw [hf'eq p]; exact (hQb p).2

end GlobalTheory.BaseTerm
