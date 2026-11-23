import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped Classical

namespace GlobalTheory.HoweLocal

theorem isContOn_locOps_member_nonsplit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (a b : ℕ)
    (JA : Matrix (Fin a) (Fin a) E) (B : Spc F E b) (κ : Type) [Fintype κ]
    (dA : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F B.J)) κ) (ψ : AddChar (AF F) ℂ)
    (omB : UA σ B.J →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsStd ψ → IsUSplitting (adeleClass F) ψ dA (actB (cA σ)) omB →
    ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → ∀ [Invertible (2 : Fv F v)],
    ∀ (eB : UAtGrp σ B (evFin F v) ≃* UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v B.J)),
      GlobalTheory.HoweLocal.IsCompIso σ B v eB →
    ∀ omL : UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v B.J) →* Module.End ℂ ((κ → Fv F v) → ℂ),
      (∀ g, ∀ φ ∈ SB (κ → Fv F v), omL g φ ∈ SB (κ → Fv F v) ∧
        Acts (evFin F v) (omB (eB.symm g).1) φ (omL g φ)) →
    ∀ co : Darboux (symp (R := Fv F v) (GlobalTheory.HoweLocal.cv σ v) (-1) (GlobalTheory.HoweLocal.Jv v JA)
        (GlobalTheory.HoweLocal.Jv v B.J)) κ,
      (∀ x, co.e x = GlobalTheory.LatVac.locCo dA v (x.map (GlobalTheory.HoweLocal.liftE v))) →
    IsContOn (sbClass (Fv F v)) omL := by
  intro F E _ _ _ _ _ σ a b JA B κ _ dA ψ omB _ hsp v _ _ eB heB omL hom _ _
  have hcomp : omL = (omL.comp eB.toMonoidHom).comp eB.symm.toMonoidHom := by
    ext g : 1
    simp
  rw [hcomp]
  refine IsContOn.comp ?_ heB.2.2
  intro l _ φ hφ
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  let lift : (κ → Fv F v) → (κ → AF F) := fun t i => GlobalTheory.LatVac.liftV v (t i)
  let L : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ := (R 0)⁻¹ • l.comp (LinearMap.funLeft ℂ ℂ lift)
  have hL : L ∈ (adeleClass F).adm κ := by
    intro g _
    refine ⟨((R 0)⁻¹ * l (fun t => g (fun i => (lift t i).2))) •
      ((BoundedContinuousFunction.evalCLM ℂ 0).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
    have e : (fun t => pureA F f g (lift t)) = f 0 • fun t => g (fun i => (lift t i).2) := by
      funext t
      have h0 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (lift t i).1) = 0 := by
        funext i
        show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
        exact map_zero _
      simp only [pureA, h0, Pi.smul_apply, smul_eq_mul]
    show (R 0)⁻¹ • l (fun t => pureA F f g (lift t)) = _
    rw [e, map_smul]
    simp [smul_eq_mul, mul_comm, mul_assoc, mul_left_comm]
  have hc0 : IsContOn (adeleClass F) omB := hsp.cont
  have hc := (hc0 L hL _ (hR φ hφ).2).comp
    (continuous_subtype_val (p := (· ∈ UAtGrp σ B (evFin F v))))
  refine hc.congr fun q => ?_
  have hq := (hom (eB q) φ hφ).2 R (hR φ hφ)
  rw [MulEquiv.symm_apply_apply] at hq
  simp only [Function.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [hq]
  have e : (fun t => tens (evFin F v) (omL (eB q) φ) R (lift t)) = R 0 • omL (eB q) φ := by
    funext t
    have hz : At (evFin F v) (lift t) := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
    have hrz : R (lift t) = R 0 := by simpa using (hR φ hφ).1 0 _ hz
    simp only [tens, lift, GlobalTheory.LatVac.evFin_liftV, Pi.smul_apply, smul_eq_mul]
    rw [show (fun i => GlobalTheory.LatVac.liftV v (t i)) = lift t from rfl, hrz, mul_comm]
  show (R 0)⁻¹ • l (fun t => tens (evFin F v) (omL (eB q) φ) R (lift t)) = _
  rw [e, map_smul, smul_smul, inv_mul_cancel₀ hR0, one_smul]

end GlobalTheory.HoweLocal
