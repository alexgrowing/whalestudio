import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GFrames

theorem lead_last_eq_det {R : Type} [CommRing R] {N : ℕ} (Z : Matrix (Fin N) (Fin N) R) :
    lead Z (Fin.last N) = Z.det := by
  unfold lead
  congr 1

theorem Zh_map_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F)) :
    G.Zh.map (A.loc p).ιE =
      Matrix.diagonal (fun a : Fin (r + 1) =>
          algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (a : ℕ)))) *
        (G.S p).Zh *
      Matrix.diagonal (fun a : Fin (r + 1) =>
          algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (a : ℕ)))) := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
  have h := (GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p).2.2.2.2.1 G.Hm (G.f' b) (G.f a)
  have hZ : G.Zh a b = ∑ i, ∑ j, G.f' b i * G.Hm i j * sig (G.f a j) := rfl
  rw [hZ, ← h, ← G.f_eq p a, ← G.f'_eq p b, ← G.Hm_eq p]
  simp only [Frames.Zh, Frames.h, Matrix.of_apply, hf, Pi.smul_apply, smul_eq_mul, map_mul,
    AlgEquiv.commutes, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem Zh_inv_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) : G.Zh⁻¹ * G.Zh = 1 := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  let p : HeightOneSpectrum (𝓞 F) := ⟨P, hP.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
  haveI := GlobalTheory.HL.PlacesInt.nontrivial_Ep (A.loc p)
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  have hS : IsUnit ((G.S p).Zh.det) := by
    have := (GlobalTheory.FrameBasic.main (A.L p) r k (G.S p)).2.2.2.1
    rwa [Frames.D, lead_last_eq_det] at this
  have hd : IsUnit (Matrix.diagonal (fun a : Fin (r + 1) =>
      algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (a : ℕ))))).det := by
    rw [Matrix.det_diagonal, ← map_prod]
    exact (IsUnit.prod_univ_iff.2 fun a => ((G.c p).isUnit.pow _)).map (algebraMap (A.loc p).Fp (A.loc p).Ep)
  have hι : IsUnit ((A.loc p).ιE G.Zh.det) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Zh_map_eq, Matrix.det_mul, Matrix.det_mul]
    exact (hd.mul hS).mul hd
  have hne : G.Zh.det ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hι
    exact not_isUnit_zero hι
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hne)

end GlobalTheory.HL.GFrames
