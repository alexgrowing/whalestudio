import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ThGramIncM
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitDict
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThRatIffK

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem th_gram_incM_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X : Matrix (Fin d.m) (Fin d.n) E) :
    d.gram (incM F X) (incM F X) = incM F (Xᵀ * d.A.J * X.map σ) := by
  have h1 : (incM F X).map (cA σ) = incM F (X.map σ) := by
    ext i j; simp only [incM, Matrix.map_apply]; exact th_cA_incl _
  rw [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, h1]
  simp only [incM, Matrix.transpose_map, Matrix.map_mul]
theorem th_gramE_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (η : E) (X : Matrix (Fin d.m) (Fin d.n) E) :
    HeckeCharacterZeroLocus.SiegelWeilU.gramE σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) Xᵀ = η • (Xᵀ * d.A.J * X.map σ)ᵀ := by
  ext a b
  simp only [HeckeCharacterZeroLocus.SiegelWeilU.gramE, HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k, Matrix.transpose_apply,
    Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, RingHom.coe_coe]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
theorem th_gram_iff_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) (T₀ : Matrix (Fin d.n) (Fin d.n) E)
    (X : Matrix (Fin d.m) (Fin d.n) E) :
    d.gram (incM F X) (incM F X) = (-2 : ℤ) • incM F T₀ ↔ HeckeCharacterZeroLocus.SiegelWeilU.gramE σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) Xᵀ = Td η T₀ := by
  have hs : ((-2 : ℤ) • incM F T₀ : Matrix (Fin d.n) (Fin d.n) (AE F E)) = incM F ((-2 : ℤ) • T₀) := by
    ext i j; simp only [incM, Matrix.map_apply, Matrix.smul_apply, map_zsmul]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_gram_incM_k, _root_.PositivityTheory.SiegelWeilFormula.KWhit.th_gramE_k, Td, hs]
  constructor
  · intro h
    rw [th_incM_injective h]
    ext i j
    simp only [Matrix.smul_apply, Matrix.transpose_apply]
    simp only [zsmul_eq_mul, smul_eq_mul]; push_cast; ring
  · intro h
    congr 1
    ext i j
    have := congrFun (congrFun h j) i
    simp only [Matrix.smul_apply, Matrix.transpose_apply] at this ⊢
    simp only [zsmul_eq_mul, smul_eq_mul] at this ⊢
    push_cast at this ⊢
    apply mul_left_cancel₀ hη
    rw [this]; ring
theorem th_toMx_act_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (M : GL (Fin d.m) (AE F E)) (X : Matrix (Fin d.m) (Fin d.n) E) :
    toMx (HeckeCharacterZeroLocus.SiegelWeilU.actTup (AF F) M (HeckeCharacterZeroLocus.SiegelWeilU.ratTup (AF F) Xᵀ)) =
      (M : Matrix (Fin d.m) (Fin d.m) (AE F E)) * incM F X := by
  ext a j
  simp only [toMx, HeckeCharacterZeroLocus.SiegelWeilU.actTup, HeckeCharacterZeroLocus.SiegelWeilU.ratTup, Matrix.of_apply, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, incM, Matrix.map_apply, Matrix.transpose_apply, th_inclR_eq]
theorem thetaDict_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.ThetaDict_k := by
  intro F E _ _ _ _ _ σ d η hη _
  refine ⟨d.μ.map (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη), _root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη '' d.D, _root_.PositivityTheory.SiegelWeilFormula.KWhit.th_haar_k d hη, _root_.PositivityTheory.SiegelWeilFormula.KWhit.th_fd_k d hη, ?_⟩
  intro T T₀ hT Φ _
  rw [_root_.PositivityTheory.SiegelWeilFormula.SD_k.orb, setAverage_eq, HeckeCharacterZeroLocus.SiegelWeilU.meanC, MeasurableEquiv.map_apply, (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη).preimage_image,
    (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη).restrict_map, (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη).preimage_image, integral_map_equiv, measureReal_def]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  simp only [HeckeCharacterZeroLocus.SiegelWeilU.thetaS]
  let e : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1} ≃
      {X : Fin d.n → Fin d.m → E | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) X = Td η T₀} :=
    { toFun := fun X => ⟨X.1ᵀ, (_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_gram_iff_k d hη T₀ X.1).1 (hT ▸ X.2)⟩
      invFun := fun Y => ⟨Matrix.transpose (Y.1 : Matrix (Fin d.n) (Fin d.m) E), by
        rw [hT]; exact (_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_gram_iff_k d hη T₀ _).2 Y.2⟩
      left_inv := fun X => Subtype.ext (Matrix.transpose_transpose _)
      right_inv := fun Y => Subtype.ext (Matrix.transpose_transpose (Y.1 : Matrix (Fin d.n) (Fin d.m) E)) }
  rw [← e.tsum_eq]
  refine tsum_congr fun X => ?_
  simp only [e, Equiv.coe_fn_mk]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_toMx_act_k]
  rfl
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
