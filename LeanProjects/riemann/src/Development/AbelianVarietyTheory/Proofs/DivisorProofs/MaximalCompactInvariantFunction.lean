import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevSplitOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviIsoPlaneUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLeviLeviElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLogHomIsMultipleOfLogAbs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFunctionRadialLogDependenceStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFunctionTwistBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianNormAdaptedPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementInfinitePoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerRestrictsToOrthocomp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTopSmul
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.TorFinIso
open Matrix
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin GlobalTheory.TorFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem setIntegral_unip_eq_constTerm_iso (σ : E →ₐ[F] E) (B : Base F E) {n n₁ : ℕ} (Y : Spc F E n) (Y₁ : Spc F E n₁)
    (H : Plane E n n₁) (hsk : ∀ i j, σ (Y.J j i) = -Y.J i j) (hP : IsIsoPlane σ B H Y Y₁) (hσ : ∀ x, σ (σ x) = x)
    (c : E) (hc : c ≠ 0) (f : UA σ Y.J → ℂ) (μ : Measure (unip σ Y H)) [μ.IsHaarMeasure] (𝓕 : Set (unip σ Y H))
    (h𝓕 : IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unip σ Y H)) 𝓕 μ) (h1 : μ 𝓕 = 1)
    (cc : GAd σ (c • Y.J.map σ) → ℂ)
    (hcc : IsConstTerm σ (c • Y.J.map σ) (Matrix.of fun i (_ : Fin 1) => H.x i) (fun x => f ((toGAd hσ Y.J hc).symm x)) cc)
    (g : UA σ Y.J) : ∫ u in 𝓕, f (u.1 * g) ∂μ = cc (toGAd hσ Y.J hc g) := by
  set C : Matrix (Fin n) (Fin 1) E := Matrix.of fun i (_ : Fin 1) => H.x i with hCdef
  let e := toGAd hσ Y.J hc
  have hd₁ : Y₁.J.det ≠ 0 := GlobalTheory.IsoPlaneProj.det_ne_zero_of_cartan B Y₁ hP.2.2.2.2.2.2.2
  have hmem : ∀ g : UA σ Y.J, g ∈ unip σ Y H ↔ e g ∈ unipRad σ (c • Y.J.map σ) C := fun g =>
    GlobalTheory.UnipCocptForm.mem_unip_iff σ hσ Y Y₁.J H hsk hP.1 hP.2.1 hP.2.2.1 hP.2.2.2.1 hP.2.2.2.2.1 hP.2.2.2.2.2.1 hd₁ c hc g
  let e' : unip σ Y H ≃* unipRad σ (c • Y.J.map σ) C :=
    { toFun := fun u => ⟨e u.1, (hmem u.1).1 u.2⟩
      invFun := fun v => ⟨e.symm v.1, (hmem _).2 (by rw [e.apply_symm_apply]; exact v.2)⟩
      left_inv := fun u => Subtype.ext (e.symm_apply_apply u.1)
      right_inv := fun v => Subtype.ext (e.apply_symm_apply v.1)
      map_mul' := fun u v => Subtype.ext (map_mul e u.1 v.1) }
  have he : Continuous e := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  have hes : Continuous e.symm := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  have he' : Continuous e' := (he.comp continuous_subtype_val).subtype_mk _
  have hes' : Continuous e'.symm := (hes.comp continuous_subtype_val).subtype_mk _
  haveI : BorelSpace (UA σ Y.J) := ⟨rfl⟩
  haveI : ContinuousMul (UA σ Y.J) := ⟨by
    have h : (fun p : UA σ Y.J × UA σ Y.J => p.1 * p.2) =
        e.symm ∘ (fun q : GAd σ (c • Y.J.map σ) × GAd σ (c • Y.J.map σ) => q.1 * q.2) ∘ Prod.map e e := by
      funext p
      simp
    rw [h]
    exact hes.comp (continuous_mul.comp (he.prodMap he))⟩
  haveI : ContinuousMul (unip σ Y H) :=
    ⟨(continuous_mul.comp (continuous_subtype_val.prodMap continuous_subtype_val)).subtype_mk _⟩
  let t : unip σ Y H ≃ₜ unipRad σ (c • Y.J.map σ) C := ⟨e'.toEquiv, he', hes'⟩
  let me := t.toMeasurableEquiv
  have hp : MeasurePreserving me μ (μ.map me) := ⟨me.measurable, rfl⟩
  have hH : (μ.map me).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ e' he' hes'
  have hps : MeasurePreserving me.symm (μ.map me) μ := hp.symm
  have hmemU : ∀ γ : (ratPts σ (c • Y.J.map σ)).subgroupOf (unipRad σ (c • Y.J.map σ) C),
      e'.symm γ.1 ∈ (ratU σ Y.J).subgroupOf (unip σ Y H) := fun γ => by
    obtain ⟨u, -, hu2⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 γ.2))
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 ⟨u, hu2⟩)
  have hmemP : ∀ δ : (ratU σ Y.J).subgroupOf (unip σ Y H),
      e' δ.1 ∈ (ratPts σ (c • Y.J.map σ)).subgroupOf (unipRad σ (c • Y.J.map σ) C) := fun δ => by
    obtain ⟨m, hm⟩ := Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 δ.2)
    have h2 := (e δ.1.1).2
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨m, ?_, hm⟩))
    exact unitary_of_map_inclR σ n _ m _ (by rw [hm]; rfl) h2
  let fm : (ratU σ Y.J).subgroupOf (unip σ Y H) →
      (ratPts σ (c • Y.J.map σ)).subgroupOf (unipRad σ (c • Y.J.map σ) C) := fun δ => ⟨e' δ.1, hmemP δ⟩
  have hf : Function.Bijective fm :=
    ⟨fun a b hab => Subtype.ext (e'.injective (congrArg Subtype.val hab)),
      fun γ => ⟨⟨e'.symm γ.1, hmemU γ⟩, Subtype.ext (e'.apply_symm_apply γ.1)⟩⟩
  have hfd := h𝓕.preimage_of_equiv hps.quasiMeasurePreserving hf fun δ x => by
    show e'.symm (e' δ.1 * x) = δ.1 * e'.symm x
    rw [map_mul, e'.symm_apply_apply]
  have hset : me ⁻¹' (me.symm ⁻¹' 𝓕) = 𝓕 := by
    ext x
    simp
  have hmass : (μ.map me) (me.symm ⁻¹' 𝓕) = 1 := by
    rw [me.map_apply, hset, h1]
  have hc' := hcc (μ.map me) (me.symm ⁻¹' 𝓕) hH hfd hmass (e g)
  rw [hc', ← hp.setIntegral_preimage_emb me.measurableEmbedding, hset]
  refine integral_congr_ae (.of_forall fun u => ?_)
  show f (u.1 * g) = f (e.symm (e u.1 * e g))
  rw [← map_mul, e.symm_apply_apply]

section Levi
open GlobalTheory.LeviPlane GlobalTheory.LeviArch

end Levi

end GlobalTheory.TorFinIso
end
