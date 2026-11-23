import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFieldAdicCompletionTensorOfInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HoweLocal.Fld

open Polynomial
open scoped IntermediateField

theorem isField_tensor_of_isEmpty_algHom {F K E : Type} [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra F E] (h2 : Module.finrank F E = 2) (hE : IsEmpty (E →ₐ[F] K)) :
    IsField (K ⊗[F] E) := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  have hne : (⊥ : IntermediateField F E) ≠ ⊤ := by
    intro h
    rw [IntermediateField.bot_eq_top_iff_finrank_eq_one] at h
    omega
  obtain ⟨a, ha⟩ : ∃ a : E, a ∉ (⊥ : IntermediateField F E) := by
    by_contra h
    push_neg at h
    exact hne (eq_top_iff.2 fun z _ => h z)
  have hint : IsIntegral F a := Algebra.IsIntegral.isIntegral a
  have hnot : a ∉ (algebraMap F E).range := fun h => ha (IntermediateField.mem_bot.2 h)
  have hge : 2 ≤ (minpoly F a).natDegree := (minpoly.two_le_natDegree_iff hint).2 hnot
  have hle : (minpoly F a).natDegree ≤ 2 := h2 ▸ minpoly.natDegree_le a
  obtain ⟨b, c, hbc⟩ := isMonicOfDegree_two_iff.1
    (⟨by omega, minpoly.monic hint⟩ : IsMonicOfDegree (minpoly F a) 2)
  have hq : a ^ 2 + algebraMap F E b * a + algebraMap F E c = 0 := by
    have := minpoly.aeval F a
    rw [hbc] at this
    simpa [Algebra.smul_def] using this
  refine GlobalTheory.InertField.isField_tensor_of_no_root h2 a (fun x hx => hnot ⟨x, hx⟩) b c hq
    fun x hx => hE.false ?_
  have hroot : aeval x (minpoly F a) = 0 := by
    rw [hbc]
    simpa [Algebra.smul_def] using hx
  have htop : F⟮a⟯ = ⊤ := by
    refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
    rw [IntermediateField.adjoin.finrank hint, IntermediateField.finrank_top', h2]
    omega
  exact ((IntermediateField.adjoin.powerBasis hint).lift x
      (by rwa [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen])).comp
    ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv).symm.toAlgHom

theorem isField_of_isEmpty : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → IsField (Fv F v ⊗[F] E) := by
  intro F E _ _ _ _ _ σ hCM v hv
  exact isField_tensor_of_isEmpty_algHom hCM.2.2.1 hv

end GlobalTheory.HoweLocal.Fld
