import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLeviLeviElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSqFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentMemIffUnipotentRadicalStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin GlobalTheory.TorFin

noncomputable section

namespace GlobalTheory.CtTransp

theorem setIntegral_unip_eq_constTerm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), IsCMExt F E σ → ∀ (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s → ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ f : UA σ W.J → ℂ, ∀ (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ cc : GAd σ (c • W.J.map σ) → ℂ, IsConstTerm σ (c • W.J.map σ) (Matrix.of fun i (_ : Fin 1) => H'.x i) (fun x => f ((toGAd hσ W.J hc).symm x)) cc → ∀ g : UA σ W.J, ∫ u in 𝓕, f (u.1 * g) ∂μ = cc (toGAd hσ W.J hc g) := by
  intro F E _ _ _ _ _ σ B _ d r s W hW hσ c hc hcs d₁ W₁ H' i₀ i₁ hH f μ 𝓕 hμ h𝓕 h1 cc hcc g
  set C : Matrix (Fin d) (Fin 1) E := Matrix.of fun i (_ : Fin 1) => H'.x i with hCdef
  let e := toGAd hσ W.J hc
  have hmem := GlobalTheory.T.unipotent_mem_iff_unipotent_radical F E σ B d r s W hW hσ c hc hcs d₁ W₁ H' i₀ i₁ hH
  let e' : unip σ W H' ≃* unipRad σ (c • W.J.map σ) C :=
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
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI : ContinuousMul (UA σ W.J) := ⟨by
    have h : (fun p : UA σ W.J × UA σ W.J => p.1 * p.2) =
        e.symm ∘ (fun q : GAd σ (c • W.J.map σ) × GAd σ (c • W.J.map σ) => q.1 * q.2) ∘ Prod.map e e := by
      funext p
      simp
    rw [h]
    exact hes.comp (continuous_mul.comp (he.prodMap he))⟩
  haveI : ContinuousMul (unip σ W H') :=
    ⟨(continuous_mul.comp (continuous_subtype_val.prodMap continuous_subtype_val)).subtype_mk _⟩
  let t : unip σ W H' ≃ₜ unipRad σ (c • W.J.map σ) C := ⟨e'.toEquiv, he', hes'⟩
  let me := t.toMeasurableEquiv
  have hp : MeasurePreserving me μ (μ.map me) := ⟨me.measurable, rfl⟩
  have hH : (μ.map me).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ e' he' hes'
  have hps : MeasurePreserving me.symm (μ.map me) μ := hp.symm
  have hmemU : ∀ γ : (ratPts σ (c • W.J.map σ)).subgroupOf (unipRad σ (c • W.J.map σ) C),
      e'.symm γ.1 ∈ (ratU σ W.J).subgroupOf (unip σ W H') := fun γ => by
    obtain ⟨u, -, hu2⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 γ.2))
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 ⟨u, hu2⟩)
  have hmemP : ∀ δ : (ratU σ W.J).subgroupOf (unip σ W H'),
      e' δ.1 ∈ (ratPts σ (c • W.J.map σ)).subgroupOf (unipRad σ (c • W.J.map σ) C) := fun δ => by
    obtain ⟨m, hm⟩ := Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 δ.2)
    have h2 := (e δ.1.1).2
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨m, ?_, hm⟩))
    exact unitary_of_map_inclR σ d _ m _ (by rw [hm]; rfl) h2
  let fm : (ratU σ W.J).subgroupOf (unip σ W H') →
      (ratPts σ (c • W.J.map σ)).subgroupOf (unipRad σ (c • W.J.map σ) C) := fun δ => ⟨e' δ.1, hmemP δ⟩
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

end GlobalTheory.CtTransp
