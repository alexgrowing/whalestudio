import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentMemIffUnipotentRadical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSqFundamentalDomain
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.LineCT

open GlobalTheory.UnipMem GlobalTheory.LeviPlane

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_unip_iff {σ : E →ₐ[F] E} {B : Base F E} {d r s : ℕ} {W : Spc F E d} (hW : W.IsSkew σ B r s)
    (hσ : ∀ x, σ (σ x) = x) {c : E} (hc : c ≠ 0) {d₁ : ℕ} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {i₀ i₁ : ℕ}
    (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (g : UA σ W.J) :
    g ∈ unip σ W H' ↔ toGAd hσ W.J hc g ∈ unipRad σ (c • W.J.map σ) (Matrix.of fun i (_ : Fin 1) => H'.x i) := by
  have e : (unip σ W H').map (toGAd hσ W.J hc).toMonoidHom =
      unipRad σ (c • W.J.map σ) (Matrix.of fun i (_ : Fin 1) => H'.x i) := by
    rw [unip, MonoidHom.map_closure, unipRad]
    congr 1
    ext k
    obtain ⟨u, rfl⟩ := (toGAd hσ W.J hc).surjective k
    refine ((toGAd hσ W.J hc).injective.mem_set_image).trans ?_
    exact gen_iff hW hσ hc hH u
  rw [← e]
  exact (Subgroup.mem_map_iff_mem (f := (toGAd hσ W.J hc).toMonoidHom) (toGAd hσ W.J hc).injective).symm

theorem isConstTerm_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (n d₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E d₁) (H' : Plane E n d₁) (i₀ i₁ r s : ℕ),
    W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ (c : E) (hc : c ≠ 0) (f : UA σ W.J → ℂ), IsCT H' f 0 →
      (Matrix.of fun i (_ : Fin 1) => H'.x i) ≠ 0 ∧
      Formalism.UG.cT (σ : E →+* E) (Matrix.of fun i (_ : Fin 1) => H'.x i) * (c • W.J.map σ) * (Matrix.of fun i (_ : Fin 1) => H'.x i) = 0 ∧
      IsConstTerm σ (c • W.J.map σ) (Matrix.of fun i (_ : Fin 1) => H'.x i) (fun x => f ((toGAd hσ W.J hc).symm x)) 0 := by
  intro F E _ _ _ _ _ σ hσ B n d₁ W W₁ H' i₀ i₁ r s hW hH c hc f hf
  let C : Matrix (Fin n) (Fin 1) E := Matrix.of fun i (_ : Fin 1) => H'.x i
  refine ⟨fun h0 => ?_, ?_, ?_⟩
  · have hx : H'.x = 0 := funext fun i => congrFun (congrFun h0 i) 0
    have h1 : form σ W.J H'.x H'.y = 1 := hH.xy
    rw [hx] at h1
    simp [form] at h1
  · ext k l
    refine (row_mulVec (s := (σ : E →+* E)) hσ W.J c H'.x H'.x k).trans ?_
    rw [show fm (σ : E →+* E) W.J H'.x H'.x = 0 from hH.xx]
    simp
  · intro μ 𝓕 hμ h𝓕 h1 g
    let e := toGAd hσ W.J hc
    have hmem : ∀ u, u ∈ unip σ W H' ↔ e u ∈ unipRad σ (c • W.J.map σ) C := fun u => mem_unip_iff hW hσ hc hH u
    let e' : unipRad σ (c • W.J.map σ) C ≃* unip σ W H' :=
      { toFun := fun v => ⟨e.symm v.1, (hmem _).2 (by rw [e.apply_symm_apply]; exact v.2)⟩
        invFun := fun u => ⟨e u.1, (hmem u.1).1 u.2⟩
        left_inv := fun v => Subtype.ext (e.apply_symm_apply v.1)
        right_inv := fun u => Subtype.ext (e.symm_apply_apply u.1)
        map_mul' := fun u v => Subtype.ext (map_mul e.symm u.1 v.1) }
    have he : Continuous e := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val
    have hes : Continuous e.symm := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val
    have he' : Continuous e' := (hes.comp continuous_subtype_val).subtype_mk _
    have hes' : Continuous e'.symm := (he.comp continuous_subtype_val).subtype_mk _
    haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
    haveI : ContinuousMul (UA σ W.J) := ⟨by
      have h : (fun p : UA σ W.J × UA σ W.J => p.1 * p.2) =
          e.symm ∘ (fun q : GAd σ (c • W.J.map σ) × GAd σ (c • W.J.map σ) => q.1 * q.2) ∘ Prod.map e e := by
        funext p
        simp
      rw [h]
      exact hes.comp (continuous_mul.comp (he.prodMap he))⟩
    haveI : ContinuousInv (UA σ W.J) := ⟨by
      have h : (fun p : UA σ W.J => p⁻¹) = e.symm ∘ (fun q : GAd σ (c • W.J.map σ) => q⁻¹) ∘ e := by
        funext p
        simp
      rw [h]
      exact hes.comp (continuous_inv.comp he)⟩
    haveI : IsTopologicalGroup (UA σ W.J) := {}
    haveI : IsTopologicalGroup (unip σ W H') := inferInstance
    let t : unipRad σ (c • W.J.map σ) C ≃ₜ unip σ W H' := ⟨e'.toEquiv, he', hes'⟩
    let me := t.toMeasurableEquiv
    have hp : MeasurePreserving me μ (μ.map me) := ⟨me.measurable, rfl⟩
    have hHaar : (μ.map me).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ e' he' hes'
    have hps : MeasurePreserving me.symm (μ.map me) μ := hp.symm
    have hmemU : ∀ γ : (ratPts σ (c • W.J.map σ)).subgroupOf (unipRad σ (c • W.J.map σ) C),
        e' γ.1 ∈ (ratU σ W.J).subgroupOf (unip σ W H') := fun γ => by
      obtain ⟨u, -, hu2⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 γ.2))
      exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 ⟨u, hu2⟩)
    have hmemP : ∀ δ : (ratU σ W.J).subgroupOf (unip σ W H'),
        e'.symm δ.1 ∈ (ratPts σ (c • W.J.map σ)).subgroupOf (unipRad σ (c • W.J.map σ) C) := fun δ => by
      obtain ⟨m, hm⟩ := Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 δ.2)
      have h2 := (e δ.1.1).2
      refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨m, ?_, hm⟩))
      exact unitary_of_map_inclR σ n _ m _ (by rw [hm]; rfl) h2
    let fm' : (ratPts σ (c • W.J.map σ)).subgroupOf (unipRad σ (c • W.J.map σ) C) →
        (ratU σ W.J).subgroupOf (unip σ W H') := fun γ => ⟨e' γ.1, hmemU γ⟩
    have hfb : Function.Bijective fm' :=
      ⟨fun a b hab => Subtype.ext (e'.injective (congrArg Subtype.val hab)),
        fun δ => ⟨⟨e'.symm δ.1, hmemP δ⟩, Subtype.ext (e'.apply_symm_apply δ.1)⟩⟩
    have hfd := h𝓕.preimage_of_equiv hps.quasiMeasurePreserving hfb fun γ x => by
      show e'.symm (e' γ.1 * x) = γ.1 * e'.symm x
      rw [map_mul, e'.symm_apply_apply]
    have hset : me ⁻¹' (me.symm ⁻¹' 𝓕) = 𝓕 := by
      ext x
      simp
    have hmass : (μ.map me) (me.symm ⁻¹' 𝓕) = 1 := by
      rw [me.map_apply, hset, h1]
    have hc' := hf (μ.map me) (me.symm ⁻¹' 𝓕) hHaar hfd hmass (e.symm g)
    rw [← hp.setIntegral_preimage_emb me.measurableEmbedding, hset] at hc'
    refine hc'.trans (integral_congr_ae (.of_forall fun u => ?_))
    show f (e.symm u.1 * e.symm g) = f (e.symm (u.1 * g))
    rw [map_mul]

end GlobalTheory.LineCT
