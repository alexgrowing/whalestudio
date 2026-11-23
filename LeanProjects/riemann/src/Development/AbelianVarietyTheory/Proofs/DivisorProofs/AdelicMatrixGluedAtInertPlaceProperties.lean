import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InLat2
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertBigCell

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)}

theorem gl_iotaW_apply (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    iotaW hw x = GlobalTheory.InertLocField.liftT E v ((InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm x) := rfl

theorem gl_iotaW_mul (hw : Formalism.UG.IsInertAt F E v w) (x y : w.adicCompletion E) :
    iotaW hw (x * y) = iotaW hw x * iotaW hw y := by
  rw [gl_iotaW_apply, gl_iotaW_apply, gl_iotaW_apply, map_mul, GlobalTheory.InertLocField.liftT_mul]

theorem gl_iotaW_injective (hw : Formalism.UG.IsInertAt F E v w) : Function.Injective (iotaW hw) := fun x y hxy =>
  (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm.injective (GlobalTheory.InertLocField.liftT_injective v hxy)

theorem gl_idem_mul_iotaW (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) * iotaW hw x = iotaW hw x := by
  rw [← Algebra.smul_def, GlobalTheory.InertLocField.liftV_one_smul, gl_iotaW_apply, GlobalTheory.InertLocField.evT_liftT]

theorem gl_iotaW_one (hw : Formalism.UG.IsInertAt F E v w) :
    iotaW hw 1 = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) := by
  have h := GlobalTheory.InertLocField.liftV_one_smul (E := E) v 1
  rw [Algebra.smul_def, mul_one, _root_.map_one (GlobalTheory.InertLocField.evT E v)] at h
  rw [gl_iotaW_apply, _root_.map_one]
  exact h.symm

theorem gl_compl_mul_iotaW (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) * iotaW hw x = 0 := by
  rw [sub_mul, one_mul, gl_idem_mul_iotaW, sub_self]

theorem gl_compl_idem (hw : Formalism.UG.IsInertAt F E v w) :
    (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) * (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) =
      1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) := by
  have h := gl_idem_mul_iotaW hw 1
  rw [gl_iotaW_one] at h
  rw [mul_sub, mul_one, sub_mul, one_mul, h, sub_self, sub_zero]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem gl_compl_smul_map (hw : Formalism.UG.IsInertAt F E v w) (P : Matrix ι ι (w.adicCompletion E)) :
    (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • P.map (iotaW hw) = 0 := by
  ext i j
  rw [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, gl_compl_mul_iotaW, Matrix.zero_apply]

theorem gl_map_mul_map (hw : Formalism.UG.IsInertAt F E v w) (P Q : Matrix ι ι (w.adicCompletion E)) :
    P.map (iotaW hw) * Q.map (iotaW hw) = (P * Q).map (iotaW hw) := by
  ext i k
  rw [Matrix.mul_apply, Matrix.map_apply, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.map_apply, Matrix.map_apply, gl_iotaW_mul]

theorem gl_map_one_eq (hw : Formalism.UG.IsInertAt F E v w) :
    (1 : Matrix ι ι (w.adicCompletion E)).map (iotaW hw) =
      algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) • (1 : Matrix ι ι (AE F E)) := by
  ext i j
  rw [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [gl_iotaW_one, smul_eq_mul, mul_one]
  · rw [map_zero, smul_zero]

theorem gl_glueW_sub_one (hw : Formalism.UG.IsInertAt F E v w) (P : Matrix ι ι (w.adicCompletion E)) :
    glueW hw P - 1 = (P - 1).map (iotaW hw) := by
  rw [Matrix.map_sub _ (map_sub (iotaW hw)), gl_map_one_eq, glueW, sub_smul, one_smul]
  abel

theorem glueW_props : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
    {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) {ι : Type} [Fintype ι] [DecidableEq ι],
  (∀ P Q : Matrix ι ι (w.adicCompletion E), GlobalTheory.InertBigCell.glueW hw (P * Q) = GlobalTheory.InertBigCell.glueW hw P * GlobalTheory.InertBigCell.glueW hw Q) ∧
  GlobalTheory.InertBigCell.glueW hw (1 : Matrix ι ι (w.adicCompletion E)) = 1 ∧
  Function.Injective (GlobalTheory.InertBigCell.glueW hw (ι := ι)) ∧
  (∀ P : Matrix ι ι (w.adicCompletion E), At (evFin F v) (GlobalTheory.InertBigCell.glueW hw P - 1)) ∧
  (∀ M : Matrix ι ι (AE F E), At (evFin F v) (M - 1) → ∃ P, GlobalTheory.InertBigCell.glueW hw P = M) ∧
  (∀ (P : Matrix ι ι (w.adicCompletion E)) (u : ι → w.adicCompletion E),
    GlobalTheory.InertBigCell.glueW hw P *ᵥ (fun i => GlobalTheory.InertBigCell.iotaW hw (u i)) = fun i => GlobalTheory.InertBigCell.iotaW hw ((P *ᵥ u) i)) := by
  intro F E _ _ _ _ _ v w hw ι _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P Q
    have h1 : ∀ B : Matrix ι ι (AE F E), ((1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • (1 : Matrix ι ι (AE F E))) * B =
        (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • B := fun B => by
      rw [Matrix.smul_mul, Matrix.one_mul]
    have h2 : ∀ A : Matrix ι ι (AE F E), A * ((1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • (1 : Matrix ι ι (AE F E))) =
        (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • A := fun A => by
      rw [Matrix.mul_smul, Matrix.mul_one]
    rw [glueW, glueW, glueW, add_mul, mul_add, mul_add, h1, h1, h2, smul_smul, gl_compl_idem hw, gl_compl_smul_map,
      gl_compl_smul_map, gl_map_mul_map, add_zero, zero_add]
  · rw [glueW, gl_map_one_eq, ← add_smul, sub_add_cancel, one_smul]
  · intro P Q hPQ
    have h : P.map (iotaW hw) = Q.map (iotaW hw) := add_left_cancel hPQ
    exact Matrix.ext fun i j => gl_iotaW_injective hw (congrFun (congrFun h i) j)
  · intro P u hu
    rw [gl_glueW_sub_one]
    ext i j
    rw [Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply, gl_iotaW_apply]
    exact GlobalTheory.InertLocField.at_liftT v _ u hu
  · intro M hM
    have hent : ∀ i j, ∃ y, GlobalTheory.InertLocField.liftT E v y = (M - 1) i j := fun i j =>
      (GlobalTheory.InertLocField.at_iff v _).1 (fun u hu => by
        have := congrFun (congrFun (hM u hu) i) j
        rwa [Matrix.smul_apply] at this)
    choose y hy using hent
    refine ⟨1 + Matrix.of fun i j => InertChart.complEquiv hw (under_eq_of_isInertAt hw) (y i j), ?_⟩
    have hX : (Matrix.of fun i j => InertChart.complEquiv hw (under_eq_of_isInertAt hw) (y i j)).map (iotaW hw) = M - 1 := by
      ext i j
      rw [Matrix.map_apply, Matrix.of_apply, gl_iotaW_apply, RingEquiv.symm_apply_apply, hy]
    have h := gl_glueW_sub_one hw (1 + Matrix.of fun i j => InertChart.complEquiv hw (under_eq_of_isInertAt hw) (y i j))
    rw [add_sub_cancel_left, hX] at h
    exact sub_left_inj.mp h
  · intro P u
    have hd : ∀ x : ι → AE F E, ((1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • (1 : Matrix ι ι (AE F E))) *ᵥ x =
        (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • x := fun x => by
      funext i
      simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
    funext i
    rw [glueW, Matrix.add_mulVec, hd, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      gl_compl_mul_iotaW, zero_add, Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.map_apply, gl_iotaW_mul]

end GlobalTheory.InertBigCell
