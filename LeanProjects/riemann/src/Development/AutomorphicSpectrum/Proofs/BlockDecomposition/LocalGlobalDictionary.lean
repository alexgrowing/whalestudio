import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
import Development.WeilBound.ThetaLifts.SmallCones.TateAbs

noncomputable section

namespace GlobalTheory.CompanionTheory.EisDict

open scoped TensorProduct NNReal Matrix NumberField.AdeleRing
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open PositivityTheory.RgEis

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F E) in

def sec : (Af F ⊗[F] E) →+ AE F E :=
  (TensorProduct.map (LinearMap.inr F (Ainf F) (Af F)) (LinearMap.id : E →ₗ[F] E)).toAddMonoidHom

theorem sec_tmul (a : Af F) (x : E) : sec F E (a ⊗ₜ[F] x) = ((0, a) : AF F) ⊗ₜ[F] x := rfl

theorem sec_finPart (z : AE F E) : sec F E (HeckeCharacterZeroLocus.ThmBIn.finPart F E z) = finOne F • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]
  | tmul a x =>
    change sec F E (HeckeCharacterZeroLocus.ThmBIn.sndA F a ⊗ₜ[F] x) = _
    rw [sec_tmul, TensorProduct.smul_tmul']
    congr 1
    refine Prod.ext ?_ ?_
    · change (0 : Ainf F) = 0 * a.1
      simp
    · change a.2 = 1 * a.2
      simp

theorem finPart_finOne_smul (z : AE F E) :
    HeckeCharacterZeroLocus.ThmBIn.finPart F E (finOne F • z) = HeckeCharacterZeroLocus.ThmBIn.finPart F E z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy]
  | tmul a x =>
    rw [TensorProduct.smul_tmul']
    change HeckeCharacterZeroLocus.ThmBIn.sndA F (finOne F • a) ⊗ₜ[F] x = HeckeCharacterZeroLocus.ThmBIn.sndA F a ⊗ₜ[F] x
    congr 1
    change 1 * a.2 = a.2
    simp

theorem sec_mem {y : Af F ⊗[F] E} (hy : y ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E) : sec F E y ∈ intHat F E := by
  induction hy using AddSubgroup.closure_induction with
  | mem y h =>
    obtain ⟨a, ha, x, rfl⟩ := h
    refine AddSubgroup.subset_closure ⟨(0, a), ?_, fun v => ha v, x, ?_⟩
    · exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    · rw [sec_tmul]
      change _ = pairA F 0 a • ((1 : AF F) ⊗ₜ[F] (x : E))
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rfl
  | zero => simpa using (intHat F E).zero_mem
  | add x y _ _ hx hy => simpa using (intHat F E).add_mem hx hy
  | neg x _ hx => simpa using (intHat F E).neg_mem hx

theorem finPart_mem {z : AE F E} (hz : z ∈ intHat F E) : HeckeCharacterZeroLocus.ThmBIn.finPart F E z ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  induction hz using AddSubgroup.closure_induction with
  | mem z h =>
    obtain ⟨a, -, ha, o, rfl⟩ := h
    refine AddSubgroup.subset_closure ⟨HeckeCharacterZeroLocus.ThmBIn.sndA F a, fun v => ha v, o, ?_⟩
    change HeckeCharacterZeroLocus.ThmBIn.finPart F E (a • ((1 : AF F) ⊗ₜ[F] (o : E))) = _
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl
  | zero => simpa using (HeckeCharacterZeroLocus.ThmBIn.intAE F E).zero_mem
  | add x y _ _ hx hy => simpa using (HeckeCharacterZeroLocus.ThmBIn.intAE F E).add_mem hx hy
  | neg x _ hx => simpa using (HeckeCharacterZeroLocus.ThmBIn.intAE F E).neg_mem hx

theorem mem_intAd_iff (z : AE F E) :
    eqv F E z ∈ intAd E ↔ HeckeCharacterZeroLocus.ThmBIn.finPart F E z ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  rw [GroundTheory.BlockD.ThmBHecke.mem_intAE_iff, ← GroundTheory.BlockD.ThmBHecke.adeleEquiv_snd,
    GroundTheory.Global.mem_integralFiniteAdeles]
  simp only [intAd, Subring.mem_iInf, Subring.mem_comap]
  rfl

theorem dict : Dict := by
  intro F E _ _ _ _ _
  refine ⟨GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv, GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv_symm,
    GroundTheory.BlockD.ThmBHecke.adeleEquiv_incA, fun z => ?_, fun x => ?_⟩
  · rw [mem_intAd_iff]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [← sec_finPart]
      exact sec_mem h
    · rw [← finPart_finOne_smul]
      exact finPart_mem h
  · exact (PositivityTheory.ThKCT.Tate.absE_eq x).symm

end GlobalTheory.CompanionTheory.EisDict
