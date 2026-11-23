import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftECompFinOfAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HoweLocal

theorem map_div_mem_normGroup {F E A B : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] (f : A →ₐ[F] B) (x : Aˣ) (t : Fˣ) (z : (A ⊗[F] E)ˣ)
    (h : x = Units.map (algebraMap F A).toMonoidHom t * Units.map (Algebra.norm A : A ⊗[F] E →* A) z)
    (y : Bˣ) (hy : f (x : A) = y) :
    (GlobalTheory.QuadSymbol.toUnits F B t)⁻¹ * y ∈ GlobalTheory.QuadSymbol.normGroup F E B := by
  refine ⟨Units.map (Algebra.TensorProduct.map f (AlgHom.id F E) : A ⊗[F] E →* B ⊗[F] E) z, ?_⟩
  rw [eq_inv_mul_iff_mul_eq]
  ext
  rw [← hy, h]
  change algebraMap F B t * Algebra.norm B (Algebra.TensorProduct.map f (AlgHom.id F E) (z : A ⊗[F] E)) =
    f (algebraMap F A t * Algebra.norm A (z : A ⊗[F] E))
  rw [norm_map_tensor, map_mul, AlgHom.commutes]

theorem mem_localNorms_of_liftUF_eq (hC : GlobalTheory.Published.QuadraticClassFieldTheory)
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (h2 : Module.finrank F E = 2)
    (v : Pl F) (a : (Fv F v)ˣ) (t : Fˣ) (z : (AE F E)ˣ)
    (h : GlobalTheory.HoweLocal.liftUF v a =
      Units.map (algebraMap F (AF F)).toMonoidHom t * Units.map (Algebra.norm (AF F) : AE F E →* AF F) z) :
    a ∈ (Units.map (Algebra.norm (Fv F v) : Fv F v ⊗[F] E →* Fv F v)).range := by
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hP := ((hC.1 F E).2.2.2 t).2
  have hfin : ∀ u : Pl F, u ≠ v →
      GlobalTheory.QuadSymbol.eta F E (u.adicCompletion F) (GlobalTheory.QuadSymbol.finDiag F t u) = 1 := by
    intro u hu
    have := map_div_mem_normGroup (evFin F u) _ t z h 1 (by
      rw [liftUF_val, map_add, map_one,
        show evFin F u (GlobalTheory.LatVac.liftV v ((a : Fv F v) - 1)) = 0 from evalV_singleFin_ne hu _, add_zero]
      rfl)
    rw [mul_one, inv_mem_iff] at this
    exact GlobalTheory.QuadSymbol.eta_eq_one_iff.2 this
  have hinf : ∀ w : InfinitePlace F,
      GlobalTheory.QuadSymbol.eta F E w.Completion (GlobalTheory.QuadSymbol.infDiag F t w) = 1 := by
    intro w
    have := map_div_mem_normGroup (evInf F w) _ t z h 1 (by
      rw [liftUF_val, map_add, map_one,
        show evInf F w (GlobalTheory.LatVac.liftV v ((a : Fv F v) - 1)) = 0 from map_zero (GlobalTheory.AutFunCompare.evW w), add_zero]
      rfl)
    rw [mul_one, inv_mem_iff] at this
    exact GlobalTheory.QuadSymbol.eta_eq_one_iff.2 this
  unfold GlobalTheory.QuadSymbol.etaProd at hP
  rw [Finset.prod_eq_one fun w _ => hinf w, mul_one, finprod_eq_single _ v hfin] at hP
  have ht := GlobalTheory.QuadSymbol.eta_eq_one_iff.1 hP
  have hv := map_div_mem_normGroup (evFin F v) _ t z h a (by
    rw [liftUF_val, map_add, map_one, GlobalTheory.LatVac.evFin_liftV, add_sub_cancel])
  have := mul_mem ht hv
  rw [show GlobalTheory.QuadSymbol.finDiag F t v = GlobalTheory.QuadSymbol.toUnits F (Fv F v) t from rfl, mul_inv_cancel_left] at this
  exact this

end GlobalTheory.HoweLocal
