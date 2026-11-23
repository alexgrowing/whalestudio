import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IncMDblR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledDarbouxCoordsCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniquenessStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.DiagUniq

open MeasureTheory GlobalTheory.DiagForm

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem continuous_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply v.1)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply v.1)

theorem glue_shiftOf (x : κ → AF F) : glue (shiftOf x) = x := by
  have h := glue_add_shiftOf (0 : Vi F κ × Vf F κ) x
  rwa [zero_add, GlobalTheory.DiagNonvan.glue_zero, zero_add] at h

theorem shiftOf_glue (p : Vi F κ × Vf F κ) : shiftOf (glue p) = p := by
  refine Prod.ext ?_ rfl
  refine (eI F κ).injective ?_
  show eI F κ ((eI F κ).symm _) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  funext i
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

theorem continuous_shiftOf : Continuous (shiftOf : (κ → AF F) → Vi F κ × Vf F κ) :=
  ((eI F κ).symm.continuous.comp (continuous_pi fun i =>
    continuous_toMixed.comp (continuous_fst.comp (continuous_apply i)))).prodMk
    (continuous_pi fun i => continuous_snd.comp (continuous_apply i))

variable (F κ) in

def glueE : (Vi F κ × Vf F κ) ≃ₜ+ (κ → AF F) where
  toFun := glue
  invFun := shiftOf
  left_inv := shiftOf_glue
  right_inv := glue_shiftOf
  map_add' := GlobalTheory.DiagNonvan.glue_add
  continuous_toFun := GlobalTheory.DiagNonvan.continuous_glue
  continuous_invFun := continuous_shiftOf

theorem lDiag_eq (μ : @Measure (κ → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∃ c : ℂ, ∀ Φ ∈ schA F (κ ⊕ κ), lDiag F κ Φ = c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : ((mu F κ).map (glueE F κ)).IsAddHaarMeasure := (glueE F κ).isAddHaarMeasure_map _
  have h := Measure.isAddLeftInvariant_eq_smul ((mu F κ).map (glueE F κ)) μ
  refine ⟨((Measure.addHaarScalarFactor ((mu F κ).map (glueE F κ)) μ : ℝ) : ℂ), fun Φ hΦ => ?_⟩
  have e := (glueE F κ).toHomeomorph.measurableEmbedding.integral_map (μ := mu F κ) (fun u => Φ (Sum.elim u u))
  rw [lDiag, LinearMap.comp_apply, Lext_apply _ (integrable_resD hΦ)]
  refine e.symm.trans ?_
  change ∫ u, Φ (Sum.elim u u) ∂((mu F κ).map (glueE F κ)) = _
  conv_lhs => rw [h]
  rw [integral_smul_nnreal_measure]
  rfl

variable (F κ) in

def diagL : ((κ → F) × (κ → F)) →ₗ[F] ((κ ⊕ κ → F) × (κ ⊕ κ → F)) where
  toFun p := (Sum.elim p.1 p.1, Sum.elim p.2 (-p.2))
  map_add' p q := by
    refine Prod.ext ?_ ?_ <;> funext i <;> cases i <;> simp [add_comm]
  map_smul' c p := by
    refine Prod.ext ?_ ?_ <;> funext i <;> cases i <;> simp

omit [NumberField F] [Fintype κ] in
theorem diagL_injective : Function.Injective (diagL F κ) := by
  intro p q h
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · exact congrFun (congrArg Prod.fst h) (Sum.inl i)
  · exact congrFun (congrArg Prod.snd h) (Sum.inl i)

theorem eq_mul_diagInt : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ] (l : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] ℂ), l ∈ (adeleClass F).adm (κ ⊕ κ) →
      (∀ x y : κ → AF F, ∀ Φ ∈ schA F (κ ⊕ κ), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) = l Φ) →
      ∀ μ : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∃ c : ℂ, ∀ Φ ∈ schA F (κ ⊕ κ), l Φ = c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  intro F _ _ ψ hψ κ _ l hl hinv μ hμ
  have key : ∀ l' : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] ℂ,
      (∀ x y : κ → AF F, ∀ Φ ∈ schA F (κ ⊕ κ), l' (schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) = l' Φ) →
      ∀ (t : AF F), ∀ w ∈ LinearMap.range (diagL F κ), ∀ φ ∈ schA F (κ ⊕ κ),
        l' (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l' φ := by
    rintro l' h t _ ⟨p, rfl⟩ φ hφ
    have e : t • ((fun i => algebraMap F (AF F) ((diagL F κ p).1 i)), (fun i => algebraMap F (AF F) ((diagL F κ p).2 i))) =
        (Sum.elim (fun i => t * algebraMap F (AF F) (p.1 i)) (fun i => t * algebraMap F (AF F) (p.1 i)),
          Sum.elim (fun i => t * algebraMap F (AF F) (p.2 i)) (-fun i => t * algebraMap F (AF F) (p.2 i))) := by
      refine Prod.ext ?_ ?_ <;> funext i <;> cases i <;> simp [diagL]
    rw [e]
    exact h _ _ φ hφ
  obtain ⟨c, hc⟩ := GlobalTheory.T.adelicStoneVonNeumann_lagrangian_uniqueness F ψ hψ (κ ⊕ κ) (LinearMap.range (diagL F κ))
    (by
      rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
      simp [diagL, dotProduct, Fintype.sum_sum_type])
    (by
      rw [LinearMap.finrank_range_of_inj diagL_injective]
      simp)
    l hl (lDiag F κ) lDiag_adm (key l hinv) (key _ fun x y Φ hΦ => lDiag_schr ψ x y hΦ) exists_lDiag_ne
  obtain ⟨d, hd⟩ := lDiag_eq μ hμ
  exact ⟨c * d, fun Φ hΦ => by rw [hc Φ hΦ, hd Φ hΦ, mul_assoc]⟩

end GlobalTheory.DiagUniq

end
