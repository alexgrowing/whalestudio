import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped Classical

namespace GlobalTheory.HoweLocal

theorem isContOn_locOps_nonsplit : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → ∀ [Invertible (2 : Fv F v)],
      ∀ om' : UAtGrp σ X (evFin F v) × UAtGrp σ W (evFin F v) →* Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ),
        (∀ g h, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), om' (g, h) φ ∈ SB (Fin n × Fin d → Fv F v) ∧
          Acts (evFin F v) (om (g.1, h.1)) φ (om' (g, h) φ)) →
      ∀ (eX : UAtGrp σ X (evFin F v) ≃* UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v X.J)),
        GlobalTheory.HoweLocal.IsCompIso σ X v eX →
      ∀ (eW : UAtGrp σ W (evFin F v) ≃* UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v W.J)),
        GlobalTheory.HoweLocal.IsCompIso σ W v eW →
      ∀ (co : Darboux (symp (R := Fv F v) (GlobalTheory.HoweLocal.cv σ v) (-1) (GlobalTheory.HoweLocal.Jv v X.J) (GlobalTheory.HoweLocal.Jv v W.J))
        (Fin n × Fin d)), GlobalTheory.HoweLocal.IsLocCo σ M v co →
      ∀ χXv χWv : (Fv F v ⊗[F] E)ˣ →* Circle, GlobalTheory.HoweLocal.IsLocChr χX v χXv → GlobalTheory.HoweLocal.IsLocChr χW v χWv →
      IsContOn (sbClass (Fv F v)) (om'.comp (eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom)) := by
  intro _ F E _ _ _ _ _ σ _ n d X W M ψ χX χW om _ _ _ _ _ _ _ _ _ hWeil v _ _ om' hom' eX heX eW heW _ _ χXv χWv _ _
  refine IsContOn.comp ?_ (f := eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom) (heX.2.2.prodMap heW.2.2)
  intro l _ φ hφ
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (Fin n × Fin d) v
  let lift : (Fin n × Fin d → Fv F v) → (Fin n × Fin d → AF F) := fun t i => GlobalTheory.LatVac.liftV v (t i)
  let L : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ := (R 0)⁻¹ • l.comp (LinearMap.funLeft ℂ ℂ lift)
  have hL : L ∈ (adeleClass F).adm (Fin n × Fin d) := by
    intro g _
    refine ⟨((R 0)⁻¹ * l (fun t => g (fun i => (lift t i).2))) •
      ((BoundedContinuousFunction.evalCLM ℂ 0).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
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
  have hc0 : IsContOn (adeleClass F) om := hWeil.2.2
  have hc := (hc0 L hL _ (hR φ hφ).2).comp ((continuous_subtype_val (p := (· ∈ UAtGrp σ X (evFin F v)))).prodMap
    (continuous_subtype_val (p := (· ∈ UAtGrp σ W (evFin F v)))))
  refine hc.congr fun q => ?_
  simp only [Function.comp_apply, Prod.map]
  rw [(hom' q.1 q.2 φ hφ).2 R (hR φ hφ)]
  have e : (fun t => tens (evFin F v) (om' q φ) R (lift t)) = R 0 • om' q φ := by
    funext t
    have hz : At (evFin F v) (lift t) := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
    have hrz : R (lift t) = R 0 := by simpa using (hR φ hφ).1 0 _ hz
    simp only [tens, lift, GlobalTheory.LatVac.evFin_liftV, Pi.smul_apply, smul_eq_mul]
    rw [show (fun i => GlobalTheory.LatVac.liftV v (t i)) = lift t from rfl, hrz, mul_comm]
  show (R 0)⁻¹ • l (fun t => tens (evFin F v) (om' q φ) R (lift t)) = _
  rw [e, map_smul, smul_smul, inv_mul_cancel₀ hR0, one_smul]

end GlobalTheory.HoweLocal
