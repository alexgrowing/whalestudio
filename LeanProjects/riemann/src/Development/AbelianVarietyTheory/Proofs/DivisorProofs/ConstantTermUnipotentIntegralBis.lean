import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.CTLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mat_mul_inv' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g * mat g⁻¹ = 1 := by
  show (g.1 * g.1⁻¹ : GL (Fin n) (AE F E)).1 = 1
  simp

theorem mat_inv_mulVec {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) (w : Fin n → AE F E) :
    mat g⁻¹ *ᵥ (mat g *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, GlobalTheory.UnipCT.mat_inv_mul', Matrix.one_mulVec]

theorem conj_mem {d d₁ : ℕ} {W : Spc F E d} {H : Plane E d d₁} (s u : UA σ W.J)
    (hx : mat s *ᵥ incV F H.x = incV F H.x)
    (hι : ∀ z, ∃ z', mat s *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z')
    (hu : u ∈ unip σ W H) : s⁻¹ * u * s ∈ unip σ W H := by
  rw [GlobalTheory.UnipCT.unip_eq] at hu ⊢
  obtain ⟨hu1, hu2⟩ := hu
  have hx' : mat s⁻¹ *ᵥ incV F H.x = incV F H.x := by
    conv_lhs => rw [← hx]
    exact mat_inv_mulVec s _
  refine ⟨?_, fun z => ?_⟩
  · show mat (s⁻¹ * u * s) *ᵥ incV F H.x = incV F H.x
    rw [GlobalTheory.UnipCT.mat_mul', GlobalTheory.UnipCT.mat_mul', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx, hu1, hx']
  · obtain ⟨z', hz'⟩ := hι z
    obtain ⟨a, ha⟩ := hu2 z'
    refine ⟨a, ?_⟩
    show mat (s⁻¹ * u * s) *ᵥ (incM F H.ι *ᵥ z) = _
    rw [GlobalTheory.UnipCT.mat_mul', GlobalTheory.UnipCT.mat_mul', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz', ha,
      Matrix.mulVec_add, Matrix.mulVec_smul, hx', ← hz', mat_inv_mulVec]

set_option synthInstance.maxHeartbeats 400000 in

theorem ct_levi : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} (H : Plane E n n₁) (f c : UA σ Y.J → ℂ), IsCT H f c →
    (∀ γ ∈ ratU σ Y.J, ∀ x, f (γ * x) = f x) →
    (∃ (μ : Measure (unip σ Y H)) (𝓕 : Set (unip σ Y H)), μ.IsHaarMeasure ∧
      IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unip σ Y H)) 𝓕 μ ∧ μ 𝓕 = 1) →
    ∀ (h₁ : UA σ Y₁.J) (r : UA σ Y.J), IsLevi (W₁ := Y₁) H 1 h₁ r → r ∈ ratU σ Y.J → ∀ x, c (r * x) = c x := by
  intro F E _ _ _ _ _ σ n n₁ Y Y₁ H f c hc hf ⟨μ, 𝓕, hμ, h𝓕, h1⟩ h₁ r hL hr x
  obtain ⟨i1, -, -, -⟩ := GlobalTheory.UnipCT.topFacts (F := F) σ Y.J
  haveI : BorelSpace (UA σ Y.J) := ⟨rfl⟩
  obtain ⟨hLx, -, hLι⟩ := hL
  have hx : mat r *ᵥ incV F H.x = incV F H.x := by simpa using hLx
  have hx' : mat r⁻¹ *ᵥ incV F H.x = incV F H.x := by
    conv_lhs => rw [← hx]
    exact mat_inv_mulVec r _
  have hι : ∀ z, mat r *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat h₁ *ᵥ z) := fun z => by
    rw [Matrix.mulVec_mulVec, hLι, ← Matrix.mulVec_mulVec]
  have hι' : ∀ z, ∃ z', mat r⁻¹ *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z' := fun z =>
    ⟨mat h₁⁻¹ *ᵥ z, by
      have := mat_inv_mulVec r (incM F H.ι *ᵥ (mat h₁⁻¹ *ᵥ z))
      rw [hι, Matrix.mulVec_mulVec (M := mat h₁), mat_mul_inv', Matrix.one_mulVec] at this
      exact this⟩
  have hA : ∀ u ∈ unip σ Y H, r⁻¹ * u * r ∈ unip σ Y H := fun u hu =>
    conj_mem r u hx (fun z => ⟨_, hι z⟩) hu
  have hB : ∀ u ∈ unip σ Y H, r * u * r⁻¹ ∈ unip σ Y H := fun u hu => by
    simpa using conj_mem r⁻¹ u hx' hι' hu
  let φ : unip σ Y H ≃* unip σ Y H :=
    { toFun := fun u => ⟨r⁻¹ * u.1 * r, hA u.1 u.2⟩
      invFun := fun u => ⟨r * u.1 * r⁻¹, hB u.1 u.2⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun u v => Subtype.ext (by
        show r⁻¹ * (u * v).1 * r = (r⁻¹ * u.1 * r) * (r⁻¹ * v.1 * r)
        rw [Subgroup.coe_mul]; group) }
  have hφ : Continuous φ := by
    show Continuous fun u : unip σ Y H => (⟨r⁻¹ * u.1 * r, hA u.1 u.2⟩ : unip σ Y H)
    exact Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  have hφs : Continuous φ.symm := by
    show Continuous fun u : unip σ Y H => (⟨r * u.1 * r⁻¹, hB u.1 u.2⟩ : unip σ Y H)
    exact Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  let e : unip σ Y H ≃ᵐ unip σ Y H := (Homeomorph.mk φ.toEquiv hφ hφs).toMeasurableEquiv
  let μ' : Measure (unip σ Y H) := μ.map e
  haveI : μ'.IsHaarMeasure := φ.isHaarMeasure_map μ hφ hφs
  have hpres : MeasurePreserving e.symm μ' μ := by
    refine ⟨e.symm.measurable, ?_⟩
    simp only [μ', Measure.map_map e.symm.measurable e.measurable, MeasurableEquiv.symm_comp_self, Measure.map_id]
  have hmemΓ : ∀ g : unip σ Y H, g ∈ (ratU σ Y.J).subgroupOf (unip σ Y H) ↔ g.1 ∈ ratU σ Y.J :=
    fun g => Subgroup.mem_subgroupOf
  let eg : (ratU σ Y.J).subgroupOf (unip σ Y H) → (ratU σ Y.J).subgroupOf (unip σ Y H) := fun g =>
    ⟨φ g.1, (hmemΓ _).2 (by
      show r⁻¹ * g.1.1 * r ∈ _
      exact mul_mem (mul_mem (inv_mem hr) ((hmemΓ _).1 g.2)) hr)⟩
  have heg : Function.Bijective eg := by
    refine ⟨fun a b h => Subtype.ext (φ.injective (congrArg Subtype.val h)),
      fun y => ⟨⟨φ.symm y.1, (hmemΓ _).2 ?_⟩, Subtype.ext (φ.apply_symm_apply _)⟩⟩
    show r * y.1.1 * r⁻¹ ∈ _
    exact mul_mem (mul_mem hr ((hmemΓ _).1 y.2)) (inv_mem hr)
  let 𝓕' : Set (unip σ Y H) := e.symm ⁻¹' 𝓕
  have h𝓕' : IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unip σ Y H)) 𝓕' μ' := by
    refine h𝓕.preimage_of_equiv hpres.quasiMeasurePreserving heg ?_
    intro g y
    show φ.symm (φ g.1 * y) = g.1 * φ.symm y
    rw [map_mul, MulEquiv.symm_apply_apply]
  have h1' : μ' 𝓕' = 1 := by
    simp only [μ', 𝓕', e.map_apply]
    rw [← Set.preimage_comp, e.symm_comp_self, Set.preimage_id]; exact h1
  have A := hc μ' 𝓕' inferInstance h𝓕' h1' x
  have B := hc μ 𝓕 hμ h𝓕 h1 (r * x)
  rw [B, A, e.measurableEmbedding.setIntegral_map]
  have h𝓕e : e ⁻¹' 𝓕' = 𝓕 := by
    simp only [𝓕']; rw [← Set.preimage_comp, e.symm_comp_self, Set.preimage_id]
  rw [h𝓕e]
  congr 1; funext u
  show f (u.1 * (r * x)) = f ((r⁻¹ * u.1 * r) * x)
  rw [← hf r⁻¹ (inv_mem hr) (u.1 * (r * x))]
  simp only [mul_assoc]

end GlobalTheory.CTLevi

end
