import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HkSum
open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin GlobalTheory.LFun Formalism.UG Formalism.UG.P
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem fst_finGL (k : GL (Fin a) (Af E)) :
    Matrix.GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing E) (Af E)) (finGL E a k) = 1 :=
  map_cornerGL_of_zero _ _ (fun _ => rfl) k

private theorem det_finGL_any (k : GL (Fin a) (Af E)) :
    Matrix.GeneralLinearGroup.det (finGL E a k) = finId E (Matrix.GeneralLinearGroup.det k) := by
  refine Units.ext (Prod.ext ?_ ?_)
  · have h := GlobalTheory.CuspRep.det_map (RingHom.fst (InfiniteAdeleRing E) (Af E)) (finGL E a k)
    rw [fst_finGL] at h
    refine h.symm.trans ?_
    change _ = RingHom.fst (InfiniteAdeleRing E) (Af E) ((1 : Ad E) - sFin E 1 + sFin E _)
    have hz : ∀ x, (sFin E x).1 = 0 := fun _ => rfl
    simp [hz]
    rfl
  · have h := GlobalTheory.CuspRep.det_map (pFin E) (finGL E a k)
    rw [pFin_finGL] at h
    refine h.symm.trans ?_
    change _ = (1 : Af E) - 1 + (Matrix.GeneralLinearGroup.det k : (Af E)ˣ)
    simp

private theorem norm_of_val_one {w : Pl E} {y : w.adicCompletion E} (h : Valued.v y = 1) : ‖y‖ = 1 := by
  rw [FinitePlace.norm_def, h, map_one, NNReal.coe_one]

private theorem norm_unif {w : Pl E} {ϖ : w.adicCompletion E} (hu : IsUnifV E w ϖ) : ‖ϖ‖ = (qV E w : ℝ)⁻¹ := by
  have h0 : Valued.v ϖ ≠ 0 := by
    rw [show Valued.v ϖ = _ from hu]; exact WithZero.coe_ne_zero
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ h0]
  have e : Multiplicative.toAdd (WithZero.unzero h0) = -1 := by
    have : ((WithZero.unzero h0 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = _ :=
      (WithZero.coe_unzero h0).trans hu
    exact congrArg Multiplicative.toAdd (WithZero.coe_injective this)
  rw [e, zpow_neg_one]
  simp [qV]

end

theorem UpperTheory.detModule_satakeTset_eq_inv_pow :
    ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (r a : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → a ≤ r → ∀ x ∈ satakeTset (n := r) w ϖ a,
      (detModule E r (finGL E r (locGL E r w x)) : ℝ) = ((qV E w : ℝ) ^ a)⁻¹ := by
  intro E _ _ w r a ϖ hu ha x hx
  obtain ⟨k₁, h₁, k₂, h₂, e⟩ := hx
  have hm : (Matrix.GeneralLinearGroup.det x : (w.adicCompletion E)ˣ).val =
      (Matrix.GeneralLinearGroup.det k₁).val * ϖ ^ a * (Matrix.GeneralLinearGroup.det k₂).val := by
    change x.val.det = k₁.val.det * _ * k₂.val.det
    rw [e, Matrix.det_mul, Matrix.det_mul, GlobalTheory.SphGal.det_diagJ ϖ ha]
  have hid : Matrix.GeneralLinearGroup.det (finGL E r (locGL E r w x)) =
      GroundTheory.Global.IdeleGroup.finiteEmbedding w (Matrix.GeneralLinearGroup.det x) :=
    (det_finGL_any _).trans (finId_det_locGL w x)
  have hmod : (detModule E r (finGL E r (locGL E r w x)) : ℝ) =
      ‖((Matrix.GeneralLinearGroup.det x : (w.adicCompletion E)ˣ) : w.adicCompletion E)‖ := by
    change ((GroundTheory.Global.IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det (finGL E r (locGL E r w x))) : {r : ℝ // 0 < r}) : ℝ) = _
    rw [hid, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding]
  have n₁ : ‖(Matrix.GeneralLinearGroup.det k₁).val‖ = 1 :=
    norm_of_val_one (GlobalTheory.SphGal.isUnitAt_det_of_mem (k := k₁) h₁)
  have n₂ : ‖(Matrix.GeneralLinearGroup.det k₂).val‖ = 1 :=
    norm_of_val_one (GlobalTheory.SphGal.isUnitAt_det_of_mem (k := k₂) h₂)
  rw [hmod, hm, norm_mul, norm_mul, n₁, n₂, norm_pow, norm_unif hu, one_mul, mul_one, inv_pow]
