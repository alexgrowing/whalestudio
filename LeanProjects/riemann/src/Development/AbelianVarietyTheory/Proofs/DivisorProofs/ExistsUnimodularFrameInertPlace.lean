import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InLat2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationAlgebraMapEqOfInertPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedFiniteMapsRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseFieldGeneratorLocalDifferentInertPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianLatticeSelfDualSmulTransposeInertStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertFrameUnimod

theorem selfDual_scaled : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), W.IsSkew σ B r s →
  ∀ {v : Pl F} {w : HeightOneSpectrum (𝓞 E)}, Formalism.UG.IsInertAt F E v w →
  ∃ t : F, t ≠ 0 ∧ GlobalTheory.AdelicU.IsSelfDualAt σ (algebraMap F E t • W.Jᵀ) W.L v := by
  intro F E _ _ _ _ _ σ B d W r s hW v w hw
  obtain ⟨t, ht0, s₁, s₂, h1, h2, c1, c2⟩ := GlobalTheory.T.exists_baseField_generator_localDifferent_inertPlace hw
  exact ⟨t, ht0, GlobalTheory.T.skewHermitianLattice_selfDual_smul_transpose_inert σ B W r s hW hw t ht0 s₁ s₂ h1 h2 c1 c2⟩

theorem isConjAt_conjW {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) :
    IsConjAt σ (under_eq_of_isInertAt hw) (GlobalTheory.InertBigCell.conjW σ hw) := fun y =>
  congrArg (fun z => toCompl (under_eq_of_isInertAt hw) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ z))
    ((InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm_apply_apply y)

theorem exists_frame_unimod : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
  ∀ {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w),
  ∃ (b : GL (Fin d) (w.adicCompletion E)) (δ : w.adicCompletion E),
    (∀ u, u ∈ GlobalTheory.LFun.latAt w W.L ↔ GlobalTheory.InertBigCell.InLat (w.adicCompletionIntegers E) b u) ∧
    GlobalTheory.InertBigCell.conjW σ hw δ = δ ∧
    (∀ i j, (δ • ((b : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) *
      (b : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw))) i j ∈ w.adicCompletionIntegers E) ∧
    (δ • ((b : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) *
      (b : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw))).det ≠ 0 ∧
    (δ • ((b : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) *
      (b : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw))).det⁻¹ ∈ w.adicCompletionIntegers E := by
  intro F E _ _ _ _ _ σ B d W r s _hB hW v w hw
  have hc := isConjAt_conjW σ hw
  obtain ⟨t, ht0, hsd⟩ := selfDual_scaled σ B W r s hW hw
  haveI := hW.lat
  obtain ⟨a, ha⟩ := InertChart.exists_isFrameAt (L := W.L) hw Submodule.IsLattice.fg Submodule.IsLattice.span_eq_top
  have hdet : (algebraMap F E t • W.Jᵀ).det ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ ((map_ne_zero _).2 ht0)) (GlobalTheory.FinUniq.det_ne_zero_skew hW)
  obtain ⟨B0, hB0, eB0⟩ := InertChart.exists_gram hw hc hdet hsd ha
  obtain ⟨C, hC⟩ := hB0
  set δ : w.adicCompletion E := algebraMap E (w.adicCompletion E) (algebraMap F E t) with hδdef
  have hδ : GlobalTheory.InertBigCell.conjW σ hw δ = δ := by
    rw [hδdef, InertChart.conj_algebraMap hc, AlgHom.commutes]
  have key : δ • ((a : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) *
      (a : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw)) =
      (B0 : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ := by
    rw [eB0, Matrix.transpose_mul, Matrix.transpose_mul]
    have e1 : ((algebraMap F E t • W.Jᵀ).map (algebraMap E (w.adicCompletion E)))ᵀ =
        δ • W.J.map (algebraMap E (w.adicCompletion E)) := by
      ext i j
      simp only [hδdef, Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    have e2 : (Formalism.UG.cT (GlobalTheory.InertBigCell.conjW σ hw) (a : Matrix (Fin d) (Fin d) (w.adicCompletion E)))ᵀ =
        (a : Matrix (Fin d) (Fin d) (w.adicCompletion E)).map (GlobalTheory.InertBigCell.conjW σ hw) := by
      simp [Formalism.UG.cT]
    rw [e1, e2, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  have hBC : (B0 : Matrix (Fin d) (Fin d) (w.adicCompletion E)) =
      (C : Matrix (Fin d) (Fin d) (Formalism.UG.Ov E w)).map (Formalism.UG.Ov E w).subtype := by
    rw [← hC]; rfl
  have hdetB : (B0 : Matrix (Fin d) (Fin d) (w.adicCompletion E)).det =
      (Formalism.UG.Ov E w).subtype (C : Matrix (Fin d) (Fin d) (Formalism.UG.Ov E w)).det := by
    rw [hBC, ← RingHom.mapMatrix_apply, RingHom.map_det]
  have hCu : IsUnit (C : Matrix (Fin d) (Fin d) (Formalism.UG.Ov E w)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 C.isUnit
  refine ⟨a, δ, fun u => ?_, hδ, fun i j => ?_, ?_, ?_⟩
  · have h1 := ha ((a⁻¹ : GL (Fin d) (w.adicCompletion E)).1 *ᵥ u)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at h1
    exact h1.symm
  · rw [key, Matrix.transpose_apply, hBC, Matrix.map_apply]
    exact (C.1 j i).2
  · rw [key, Matrix.det_transpose, hdetB]
    intro h0
    exact hCu.ne_zero (Subtype.ext h0)
  · rw [key, Matrix.det_transpose, hdetB]
    obtain ⟨u, hu⟩ := hCu
    have : (Formalism.UG.Ov E w).subtype (C : Matrix (Fin d) (Fin d) (Formalism.UG.Ov E w)).det *
        (Formalism.UG.Ov E w).subtype (u⁻¹ : (Formalism.UG.Ov E w)ˣ) = 1 := by
      rw [← map_mul, ← hu, Units.mul_inv, map_one]
    rw [inv_eq_of_mul_eq_one_right this]
    exact (u⁻¹ : (Formalism.UG.Ov E w)ˣ).1.2

end GlobalTheory.InertFrameUnimod
