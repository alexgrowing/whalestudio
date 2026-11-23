import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormConvergentThetaIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAHaarEigenTripleStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeKInt

open scoped Classical

theorem proj_mem_adm {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] (x₀ : κ → AF F) :
    (LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) x₀) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x₀ i).2) • (BoundedContinuousFunction.evalCLM ℂ
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x₀ i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [LinearMap.proj_apply, pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  rw [mul_comm]

theorem exists_admissible_integral {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (t : Ω → ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ht : ∀ x, t x ∈ (adeleClass F).adm κ)
    (hint : ∀ Φ ∈ schA F κ, Integrable (fun x => t x Φ) μ) :
    ∃ l ∈ (adeleClass F).adm κ, ∀ Φ ∈ schA F κ, l Φ = ∫ x, t x Φ ∂μ := by
  let fI : schA F κ →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => ∫ x, t x Φ.1 ∂μ
      map_add' := fun Φ Ψ => by
        simp only [Submodule.coe_add, map_add]
        exact integral_add (hint _ Φ.2) (hint _ Ψ.2)
      map_smul' := fun c Φ => by
        simp only [Submodule.coe_smul, map_smul, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul c _ }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend fI
  have hlΦ : ∀ Φ ∈ schA F κ, l Φ = ∫ x, t x Φ ∂μ := fun Φ hΦ => LinearMap.congr_fun hl ⟨Φ, hΦ⟩
  refine ⟨l, ?_, hlΦ⟩
  intro g hg
  have mem : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, pureA F f g ∈ schA F κ :=
    fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  choose T hT using fun x => ht x g hg
  haveI := GlobalTheory.schwartzMap_barrelledSpace (κ → mixedEmbedding.mixedSpace F)
  obtain ⟨L, hL⟩ := GlobalTheory.ThetaIntAdm.exists_clm_integral μ T
    (fun f => by simpa only [hT] using hint _ (mem f))
  refine ⟨L, fun f => ?_⟩
  rw [hlΦ _ (mem f), hL]
  simp only [hT]

theorem smul_mem_adm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (c : ℂ)
    {l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm κ) : c • l ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨T, hT⟩ := hl g hg
  exact ⟨c • T, fun f => by rw [LinearMap.smul_apply, hT, ContinuousLinearMap.smul_apply]⟩

theorem integrable_inner : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), ∀ y : Fin b × Fin (b + a') → AF F,
      Integrable (fun k : K => ∫ l, e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ)) y * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2) ∂μ) μK := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC K μK μ hK hμK hμ e hE X om om' om₁ om₁' hT hT₁ Ψ hΨ y
  have hM := hT.geo.hM
  have hM₁ := hT₁.geo.hM
  have hψ := hT.base.std
  have hW : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om :=
    hT.weil
  have htate := GlobalTheory.T.config_a_haar_eigen_triple hKP F E σ B b a' G G₁ H H' hC μ hμ e hE X om om' om₁ om₁' hT hT₁
  let t : (AE F E)ˣ → Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] ℂ := fun l =>
    ((X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2)) •
      ((LinearMap.proj (R := ℂ) (φ := fun _ : (Fin b × Fin (b + a') → AF F) => ℂ) y ∘ₗ e) ∘ₗ
        GlobalTheory.ConeMeasV.schrLin B.ψ (G.M.co.e (shiftA H H' l)))
  have hte : ∀ l Φ, t l Φ = e (G.M.co.rho B.ψ (shiftA H H' l) Φ) y * (X.ν l : ℂ) *
      ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2) := fun l Φ => by
    show _ * e (G.M.co.rho B.ψ (shiftA H H' l) Φ) y = _
    ring
  have ht : ∀ l, t l ∈ (adeleClass F).adm (Fin (b + 2) × Fin (b + 2 + a')) := fun l =>
    smul_mem_adm _ (GlobalTheory.ConeMeasV.comp_schr_mem_adm hψ _
      (GlobalTheory.ConeMeasV.comp_ev_mem_adm hM hM₁ hE (proj_mem_adm _ y)))
  obtain ⟨L, hL, hLe⟩ := exists_admissible_integral μ t ht (fun Φ hΦ => by simpa only [hte] using htate Φ hΦ y)
  have hc := hW.2.2 _ hL Ψ hΨ
  have hsplit := hW.isUSplitting
  have heq : (fun k : K => ∫ l, e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ)) y * (X.ν l : ℂ) *
      ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2) ∂μ) = fun k : K => L (om (k.1, 1) Ψ) := by
    funext k
    rw [hLe _ (hsplit.pres (k.1, 1) Ψ hΨ)]
    simp only [hte]
  rw [heq]
  obtain ⟨K₀, -, -, hK₀, hcpt, -, -⟩ := GlobalTheory.StabHaar.stabEx hKP.base F E σ B _ G.V _ _ hT.base hT.geo.hV
  obtain rfl : K₀ = K := Subgroup.ext fun g => (hK₀ g).trans (hK g).symm
  haveI : CompactSpace K₀ := isCompact_iff_compactSpace.1 hcpt
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  have hcont : Continuous fun k : K₀ => L (om (k.1, 1) Ψ) :=
    hc.comp (continuous_subtype_val.prodMk continuous_const)
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end GlobalTheory.ConeKInt
