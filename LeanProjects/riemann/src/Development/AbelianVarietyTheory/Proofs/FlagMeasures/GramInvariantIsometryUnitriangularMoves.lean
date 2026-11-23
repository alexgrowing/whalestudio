import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentGroupsLatticesGlobalCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsOrbitsHeightsAmplitudesInCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDatumOfTwoCongruentFramesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnsignedLocalTermRowLatticeIsTerm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitriangularFrameChangeLocalScalings
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDatumEquivariantFlagIsometries
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL

theorem leadMinor_triMul {E : Type} [Field E] {m : ℕ} (A B Z : Matrix (Fin m) (Fin m) E)
    (hA : ∀ i j, i < j → A i j = 0) (hA1 : ∀ i, A i i = 1)
    (hB : ∀ i j, j < i → B i j = 0) (hB1 : ∀ i, B i i = 1) (l : ℕ) :
    leadMinorE (A * Z * B) l = leadMinorE Z l := by
  unfold leadMinorE
  by_cases hl : l ≤ m
  · rw [dif_pos hl, dif_pos hl]
    have red : ∀ g : Fin m → E, (∀ i : Fin m, l ≤ (i : ℕ) → g i = 0) →
        ∑ i, g i = ∑ i : Fin l, g (Fin.castLE hl i) := by
      intro g hg
      refine (Finset.sum_of_injOn (Fin.castLE hl) (Fin.castLE_injective hl).injOn
        (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) (fun i _ hi => hg i ?_) (fun _ _ => rfl)).symm
      by_contra h
      exact hi ⟨⟨i, by omega⟩, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩
    have key : (A * Z * B).submatrix (Fin.castLE hl) (Fin.castLE hl) =
        A.submatrix (Fin.castLE hl) (Fin.castLE hl) * Z.submatrix (Fin.castLE hl) (Fin.castLE hl) *
          B.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
      ext a b
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      rw [red]
      · refine Finset.sum_congr rfl fun d _ => ?_
        rw [red]
        intro i hi
        rw [hA _ _ (by simp [Fin.lt_def]; omega), zero_mul]
      · intro i hi
        rw [hB _ _ (by simp [Fin.lt_def]; omega), mul_zero]
    have hdA : (A.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
      rw [Matrix.det_of_lowerTriangular]
      · simp [hA1]
      · intro i j hij
        have h2 : i < j := OrderDual.toDual_lt_toDual.1 hij
        exact hA _ _ (Fin.lt_def.2 (Fin.lt_def.1 h2))
    have hdB : (B.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
      rw [Matrix.det_of_upperTriangular]
      · simp [hB1]
      · intro i j hij
        have h2 : j < i := hij
        exact hB _ _ (Fin.lt_def.2 (Fin.lt_def.1 h2))
    rw [key, Matrix.det_mul, Matrix.det_mul, hdA, hdB, one_mul, mul_one]
  · rw [dif_neg hl, dif_neg hl]

variable {D : D7}

theorem zhat_movesTo {T T' : D.host.E} (F0 : LFlag (VS D) D.R.rS T) (F0' : LFlag (VS D) D.R.rS T')
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (U U' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (h : MovesTo F0 F0' F F' ρ U U') :
    Zhat F.fl F'.fl = U.conjTranspose * Zhat F0.fl F0'.fl * U' := by
  obtain ⟨hρ, -, -, hU, hU'⟩ := h
  have hρ' : ∀ x y, (VS D).hT (ρ x) (ρ y) = (VS D).hT x y := hρ
  refine Matrix.ext fun a b => ?_
  have e1 : Zhat F.fl F'.fl a b = (VS D).hT (ρ (frame F a)) (ρ (frame F' b)) := by
    rw [hρ']; rfl
  rw [e1, hU a, hU' b]
  simp only [Zhat, brS, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, LinearMap.sum_apply,
    map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
  simp only [RingHom.id_apply, frame, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem gval_movesTo : ∀ {D : D7} {T T' : D.host.E} (F0 : LFlag (VS D) D.R.rS T) (F0' : LFlag (VS D) D.R.rS T') (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U U' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), MovesTo F0 F0' F F' ρ U U' → Gval F F' = Gval F0 F0' := by
  intro D T T' F0 F0' F F' ρ U U' h
  have hZ := zhat_movesTo F0 F0' F F' ρ U U' h
  obtain ⟨-, hu, hu', -, -⟩ := h
  have hl : ∀ l, Dl F.fl F'.fl l = Dl F0.fl F0'.fl l := by
    intro l
    show leadMinorE (Zhat F.fl F'.fl) l = leadMinorE (Zhat F0.fl F0'.fl) l
    rw [hZ]
    refine leadMinor_triMul _ _ _ (fun i j hij => ?_) (fun i => ?_) (fun i j hij => (hu' i j).1 hij)
      (fun i => (hu' i i).2 rfl) l
    · simp [Matrix.conjTranspose_apply, (hu j i).1 hij]
    · simp [Matrix.conjTranspose_apply, (hu i i).2 rfl]
  show Gflag F.fl F'.fl = Gflag F0.fl F0'.fl
  unfold Gflag
  rw [hl, hl]

end GlobalTheory.HL
