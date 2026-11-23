import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftECompFinOfAt

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal.NormLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adele_ext {a b : AF F} (hf : ∀ u, evFin F u a = evFin F u b) (hi : ∀ w, evInf F w a = evInf F w b) :
    a = b :=
  Prod.ext (funext fun w => hi w) (GlobalTheory.AdelicU.af_ext fun u => hf u)

theorem evFin_liftV_ne {u v : Pl F} (h : u ≠ v) (b : Fv F v) : evFin F u (GlobalTheory.LatVac.liftV v b) = 0 :=
  GlobalTheory.AdelicU.evalV_singleFin_ne h b

theorem evInf_liftV (w : InfinitePlace F) (v : Pl F) (b : Fv F v) : evInf F w (GlobalTheory.LatVac.liftV v b) = 0 := rfl

theorem map_liftE_eq_zero {B : Type} [CommRing B] [Algebra F B] (f : AF F →ₐ[F] B) (v : Pl F)
    (hf : ∀ b, f (GlobalTheory.LatVac.liftV v b) = 0) (y : Fv F v ⊗[F] E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (GlobalTheory.HoweLocal.liftE v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | tmul a e =>
    simp only [GlobalTheory.HoweLocal.liftE, TensorProduct.map_tmul, LinearMap.id_coe, id_eq]
    rw [Algebra.TensorProduct.map_tmul, hf, TensorProduct.zero_tmul]

theorem comp_away {B : Type} [CommRing B] [Algebra F B] (f : AF F →ₐ[F] B) (v : Pl F)
    (hf : ∀ b, f (GlobalTheory.LatVac.liftV v b) = 0) (y : Fv F v ⊗[F] E) (a : Fv F v) :
    f (Algebra.norm (AF F) (1 + GlobalTheory.HoweLocal.liftE v y : AF F ⊗[F] E)) = f (1 + GlobalTheory.LatVac.liftV v a) := by
  rw [← GlobalTheory.HoweLocal.norm_map_tensor, map_add (Algebra.TensorProduct.map f (AlgHom.id F E)),
    map_liftE_eq_zero f v hf, add_zero, map_one, map_one, map_add f, hf, add_zero, map_one]

theorem norm_liftU (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F)
    (z : (Fv F v ⊗[F] E)ˣ) :
    Units.map (Algebra.norm (AF F) : AE F E →* AF F) (GlobalTheory.HoweLocal.liftU v z) =
      GlobalTheory.HoweLocal.liftUF v (Units.map (Algebra.norm (Fv F v) : Fv F v ⊗[F] E →* Fv F v) z) := by
  refine Units.ext ?_
  rw [Units.coe_map, GlobalTheory.HoweLocal.liftU_val, GlobalTheory.HoweLocal.liftUF_val, Units.coe_map]
  refine adele_ext (fun u => ?_) (fun w => comp_away _ v (evInf_liftV w v) _ _)
  by_cases h : u = v
  · subst h
    have h1 := GlobalTheory.HoweLocal.norm_map_tensor (evFin F u)
      (1 + GlobalTheory.HoweLocal.liftE u ((z : Fv F u ⊗[F] E) - 1) : AF F ⊗[F] E)
    have h2 : Algebra.TensorProduct.map (evFin F u) (AlgHom.id F E)
        (GlobalTheory.HoweLocal.liftE u ((z : Fv F u ⊗[F] E) - 1)) = (z : Fv F u ⊗[F] E) - 1 :=
      GlobalTheory.HoweLocal.LocCoords.compFin_liftE u _
    rw [map_add, map_one, h2, add_sub_cancel] at h1
    rw [map_add (evFin F u), map_one, GlobalTheory.LatVac.evFin_liftV, add_sub_cancel]
    exact h1.symm
  · exact comp_away _ v (evFin_liftV_ne h) _ _

end GlobalTheory.HoweLocal.NormLift
