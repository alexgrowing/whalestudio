import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftDef
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LiftConst

noncomputable section
namespace GlobalTheory.ThK.LiftConst

theorem ratU_countable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  have hE : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable
  have hM : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  have hG : Countable (GL (Fin n) E) :=
    Function.Injective.countable (f := fun x : GL (Fin n) E => (x : Matrix (Fin n) (Fin n) E)) Units.val_injective
  have hR : Countable (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range :=
    (MonoidHom.rangeRestrict_surjective _).countable
  refine Function.Injective.countable (f := fun x : ratU σ J =>
    (⟨x.1.1, x.2⟩ : (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range)) ?_
  intro x y hxy
  apply Subtype.ext; apply Subtype.ext
  simpa using congrArg Subtype.val hxy

theorem thLift_mul_right {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
    (om : Rep σ X W) (Ψ : (Fin n × Fin d → AF F) → ℂ) (μ : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J))
    (hμ : μ.IsHaarMeasure) (hμr : μ.IsMulRightInvariant) (h𝓕 : IsFundamentalDomain (ratU σ W.J) 𝓕 μ)
    (f : UA σ W.J → ℂ) (hf : ∀ γ ∈ ratU σ W.J, ∀ h, f (γ * h) = f h)
    (h₁ : UA σ W.J) (hθ : ∀ γ ∈ ratU σ W.J, ∀ g h,
      theta om (om (1, h₁⁻¹) Ψ) g (γ * h) = theta om (om (1, h₁⁻¹) Ψ) g h)
    (g : UA σ X.J) :
    thLift om Ψ μ 𝓕 (fun h => f (h * h₁)) g = thLift om (om (1, h₁⁻¹) Ψ) μ 𝓕 f g := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalRing (Matrix (Fin d) (Fin d) (AE F E)) := Matrix.topologicalRing
  haveI : IsTopologicalGroup (GL (Fin d) (AE F E)) := inferInstance
  haveI : IsTopologicalGroup (UA σ W.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI : MeasurableMul (UA σ W.J) :=
    ⟨fun g => (continuous_const.mul continuous_id).measurable, fun g => (continuous_id.mul continuous_const).measurable⟩
  haveI : Countable (ratU σ W.J) := ratU_countable W.J
  haveI : MeasurableConstSMul (ratU σ W.J) (UA σ W.J) := ⟨fun γ => measurable_const_mul (γ : UA σ W.J)⟩
  haveI : μ.IsMulLeftInvariant := hμ.toIsMulLeftInvariant
  haveI : SMulInvariantMeasure (UA σ W.J) (UA σ W.J) μ := Measure.IsMulLeftInvariant.smulInvariantMeasure
  haveI : SMulInvariantMeasure (ratU σ W.J) (UA σ W.J) μ := Subgroup.smulInvariantMeasure _
  set Ψ' := om (1, h₁⁻¹) Ψ with hΨ'
  set G : UA σ W.J → ℂ := fun u => f u * starRingEnd ℂ (theta om Ψ' g u) with hG
  have key : ∀ h, theta om Ψ g h = theta om Ψ' g (h * h₁) := by
    intro h
    simp only [theta, hΨ']
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, mul_inv_cancel_right]
  have hL : thLift om Ψ μ 𝓕 (fun h => f (h * h₁)) g = ∫ h in 𝓕, G (h * h₁) ∂μ := by
    simp only [thLift_def, hG, key]
  rw [hL, thLift_def]
  have hmp : MeasurePreserving (fun x : UA σ W.J => x * h₁) μ μ := measurePreserving_mul_right μ h₁
  have hme : MeasurableEmbedding (fun x : UA σ W.J => x * h₁) := (MeasurableEquiv.mulRight h₁).measurableEmbedding
  set T := (fun x : UA σ W.J => x * h₁⁻¹) ⁻¹' 𝓕 with hTdef
  have hT : (fun x : UA σ W.J => x * h₁) ⁻¹' T = 𝓕 := by
    ext x; simp [hTdef]
  have h1 : ∫ h in 𝓕, G (h * h₁) ∂μ = ∫ u in T, G u ∂μ := by
    rw [← hT]; exact hmp.setIntegral_preimage_emb hme G T
  have hTf : IsFundamentalDomain (ratU σ W.J) T μ :=
    h𝓕.preimage_of_equiv (measurePreserving_mul_right μ h₁⁻¹).quasiMeasurePreserving (e := id) Function.bijective_id
      (fun γ x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc])
  rw [h1, hTf.setIntegral_eq h𝓕]
  intro γ x
  simp only [hG, Subgroup.smul_def, smul_eq_mul, hf γ γ.2, hθ γ γ.2]

end GlobalTheory.ThK.LiftConst
