import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableIdelesPowerDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalPartProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerIntegralBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigASchwartzEvalCompare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPartNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

noncomputable section

namespace GlobalTheory.ThK.ConeInfMeas

theorem measurable_coneInfInt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), GlobalTheory.FunPr.Hypotheses₂ → ∀ (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (e : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F b (b + a')), IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ),
    (ei ≠ 0 ∧ (∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _) ∧
      ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G₁.M.IsGood B.ψ →
    ∀ (f : SInf F (Fin (b + 2) × Fin (b + 2 + a'))) (y : Fin b × Fin (b + a') → mixedEmbedding.mixedSpace F),
      Measurable (fun p : KAt K (evI F) × idelesAt E (evI F) =>
        coneInfInt B G.M om ei (shiftA H H') X.ν ((b + 2 - a') / 2) f p.1.1 p.2.1 y) := by
  intro F E _ _ _ _ _ σ hP B b a' G G₁ H H' hC e hE ei ev hev3 K hK X om om' hT hM₁ f y
  obtain ⟨-, hev, hloc⟩ := hev3
  have hM := hT.geo.hM
  have hψ := hT.base.std
  have hSB : ∀ v, G.M.vac v ∈ SB _ := fun v => (hM.vac v).1
  have hei : ∀ g, e (pure g G.M.vac) = pure (ei g) G₁.M.vac := fun g => by
    rw [hloc g _ hSB (Eventually.of_forall fun _ => rfl)]
    exact congrArg _ (funext fun v => (hev v).1)
  obtain ⟨t1, t2, t3, t4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ _ G.V.J
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evI F)
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  haveI : TopologicalSpace.MetrizableSpace (UA σ G.V.J) := GlobalTheory.ConeMeasSmall.metrizable_group _ t1 t4 t3
  haveI : TopologicalSpace.MetrizableSpace (KAt K (evI F)) := Topology.IsEmbedding.subtypeVal.metrizableSpace
  haveI : SecondCountableTopology (KAt K (evI F)) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : BorelSpace (KAt K (evI F)) := Subtype.borelSpace _
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsModuleTopology (AF F) (Matrix (Fin (b + 2)) (Fin (b + 2 + a')) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin (b + 2) → Fin (b + 2 + a') → AE F E))
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.EvZeroInf.exists_finPart_ne_zero G₁.M.vac (fun v => (hM₁.vac v).2.1) hM₁.std
  let x : Fin b × Fin (b + a') → AF F := fun i =>
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) (x₀ i)
  have hI : (fun i => evI F (x i)) = y :=
    funext fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (y i)
  have hc : GlobalTheory.EvZeroInf.finPart G₁.M.vac x ≠ 0 := hx₀ x fun _ => rfl
  have hadm := GlobalTheory.ConeMeasV.comp_ev_mem_adm hM hM₁ hE (GlobalTheory.ThK.ConeIntCont.proj_mem_adm F _ x)
  have key : ∀ (g : SInf F (Fin (b + 2) × Fin (b + 2 + a'))) (u : Matrix (Fin (b + 2)) (Fin (b + 2 + a')) (AE F E)),
      ei (locOpInf (G.M.co.rho B.ψ (partInf F u)) g) y = (GlobalTheory.EvZeroInf.finPart G₁.M.vac x)⁻¹ *
        (LinearMap.proj x ∘ₗ e) (schr B.ψ (G.M.co.e (partInf F u)) (pure g G.M.vac)) := by
    intro g u
    have h1 : G.M.co.rho B.ψ (partInf F u) (pure g G.M.vac) = pure (locOpInf (G.M.co.rho B.ψ (partInf F u)) g) G.M.vac :=
      (locOpInf_rho G.M.co hψ u g).1 _ ⟨fun x z hz => GlobalTheory.EvZeroInf.finPart_add _ x z hz,
        GlobalTheory.TensUniq.pure_mem_schA g _ hSB hM.std⟩
    change _ = _ * e (G.M.co.rho B.ψ (partInf F u) (pure g G.M.vac)) x
    rw [h1, hei]
    change _ = _ * (ei _ (fun i => evI F (x i)) * GlobalTheory.EvZeroInf.finPart G₁.M.vac x)
    rw [hI, mul_comm (ei _ y), inv_mul_cancel_left₀ hc]
  have hco : Continuous G.M.co.e := IsModuleTopology.continuous_of_linearMap G.M.co.e.toLinearMap
  have hsh0 : Continuous (shiftA (F := F) H H') := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact Units.continuous_val.mul continuous_const
  have hsh : Continuous fun l : (AE F E)ˣ => G.M.co.e (partInf F (shiftA H H' l)) :=
    hco.comp ((continuous_const_smul (realAd F 1)).comp hsh0)
  have hν0 : Continuous X.ν := hT.chars.heckeα.1.div' hT.chars.heckeβ.1
  have hν : Continuous fun l : (AE F E)ˣ => ((X.ν l : Circle) : ℂ) := continuous_subtype_val.comp hν0
  have habs : Continuous fun l : (AE F E)ˣ => (((absE F E l : NNReal) : ℝ) : ℂ) ^ ((b + 2 - a') / 2) :=
    (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE)).pow _
  have cl : ∀ k : KAt K (evI F), Continuous fun l : idelesAt E (evI F) =>
      coneInfInt B G.M om ei (shiftA H H') X.ν ((b + 2 - a') / 2) f k.1 l.1 y := by
    intro k
    simp only [coneInfInt_apply, key]
    have h1 := (GlobalTheory.ConeMeasSmall.continuous_schr hψ hadm
      (GlobalTheory.TensUniq.pure_mem_schA (locOpInf (om (k.1, 1)) f) _ hSB hM.std)).comp hsh
    exact (((h1.const_mul _).mul hν).mul habs).comp continuous_subtype_val
  have hk : Continuous fun k : KAt K (evI F) => locOpInf (om (k.1, 1)) f :=
    (GlobalTheory.ArchWeilCont.continuousOn_locOpInf hP G.M hT.base.cm hψ hT.weil f).comp_continuous continuous_subtype_val
      fun k => k.2.2
  have hevy : Continuous fun g : SInf F (Fin b × Fin (b + a')) => g y :=
    by
    classical
    exact ((BoundedContinuousFunction.evalCLM ℂ y).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin b × Fin (b + a') → mixedEmbedding.mixedSpace F) ℂ)).continuous
  have ck : ∀ l : idelesAt E (evI F), Continuous fun k : KAt K (evI F) =>
      coneInfInt B G.M om ei (shiftA H H') X.ν ((b + 2 - a') / 2) f k.1 l.1 y := by
    intro l
    have h1 := hevy.comp (((ei.continuous.comp
      (GlobalTheory.ArchWeilCont.continuous_locOpInf_rho G.M.co hψ (shiftA H H' l.1))).comp hk).const_smul
        (((X.ν l.1 : Circle) : ℂ) * (((absE F E l.1 : NNReal) : ℝ) : ℂ) ^ ((b + 2 - a') / 2)))
    refine h1.congr fun k => ?_
    rfl
  exact measurable_uncurry_of_continuous_of_measurable
    (u := fun (k : KAt K (evI F)) (l : idelesAt E (evI F)) =>
      coneInfInt B G.M om ei (shiftA H H') X.ν ((b + 2 - a') / 2) f k.1 l.1 y) ck fun k => (cl k).measurable

end GlobalTheory.ThK.ConeInfMeas

end
