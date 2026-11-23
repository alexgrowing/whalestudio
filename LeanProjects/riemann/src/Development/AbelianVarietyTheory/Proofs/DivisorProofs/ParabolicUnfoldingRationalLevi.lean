import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.UnipCTLevi
open GlobalTheory.UnipCT

theorem setIntegral_comp_aut {N : Type} [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N]
    [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] (Γ : Subgroup N) [Countable Γ]
    (φ : N ≃* N) (c1 : Continuous φ) (c2 : Continuous φ.symm) (hφ : ∀ u, φ u ∈ Γ ↔ u ∈ Γ)
    (g : N → ℂ) (hg : ∀ γ ∈ Γ, ∀ x, g (γ * x) = g x)
    (μ : Measure N) [μ.IsHaarMeasure] (𝓕 : Set N) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (h1 : μ 𝓕 = 1) :
    ∫ x in 𝓕, g (φ x) ∂μ = ∫ x in 𝓕, g x ∂μ := by
  let e : N ≃ᵐ N := ⟨φ.toEquiv, c1.measurable, c2.measurable⟩
  haveI : (μ.map e).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ φ c1 c2
  have hpre : e ⁻¹' (e.symm ⁻¹' 𝓕) = 𝓕 := by ext u; simp
  have hq : Measure.QuasiMeasurePreserving e.symm (μ.map e) μ :=
    ⟨e.symm.measurable, by rw [e.map_symm_map]⟩
  have hS : IsFundamentalDomain Γ (e.symm ⁻¹' 𝓕) (μ.map e) := by
    refine h𝓕.preimage_of_equiv hq (e := fun γ : Γ => (⟨φ γ, (hφ _).2 γ.2⟩ : Γ)) ⟨?_, ?_⟩ ?_
    · intro a b hab
      exact Subtype.ext (φ.injective (congrArg Subtype.val hab))
    · intro b
      exact ⟨⟨φ.symm b, (hφ _).1 (by simp)⟩, Subtype.ext (by simp)⟩
    · intro γ x
      show φ.symm (φ γ * x) = γ * φ.symm x
      simp
  have hm : (μ.map e) (e.symm ⁻¹' 𝓕) = 1 := by rw [e.map_apply, hpre, h1]
  have h2 := setIntegral_map_equiv (μ := μ) e g (e.symm ⁻¹' 𝓕)
  rw [hpre] at h2
  exact h2.symm.trans (setIntegral_fd_eq Γ g hg _ μ _ 𝓕 hS h𝓕 hm h1)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem conj_mem {n n₁ : ℕ} (Y : Spc F E n) (H : Plane E n n₁) (m : UA σ Y.J)
    (A B : Matrix (Fin n₁) (Fin n₁) (AE F E)) (hAB : B * A = 1)
    (hx : mat m⁻¹ *ᵥ incV F H.x = incV F H.x) (hx' : mat m *ᵥ incV F H.x = incV F H.x)
    (hA : mat m * incM F H.ι = incM F H.ι * A) (hB : mat m⁻¹ * incM F H.ι = incM F H.ι * B)
    (u : UA σ Y.J) (hu : u ∈ unip σ Y H) : m⁻¹ * u * m ∈ unip σ Y H := by
  rw [unip_eq] at hu ⊢
  obtain ⟨h1, h2⟩ := hu
  refine ⟨?_, fun z => ?_⟩
  · rw [mat_mul', mat_mul', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx', h1, hx]
  · obtain ⟨a, ha⟩ := h2 (A *ᵥ z)
    refine ⟨a, ?_⟩
    have e1 : mat m *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (A *ᵥ z) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA]
    have e2 : mat m⁻¹ *ᵥ (incM F H.ι *ᵥ (A *ᵥ z)) = incM F H.ι *ᵥ z := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hB, Matrix.mul_assoc, hAB, Matrix.mul_one]
    rw [mat_mul', mat_mul', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e1, ha, Matrix.mulVec_add,
      Matrix.mulVec_smul, hx, e2]

theorem constantTerm_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (f : UA σ Y.J → ℂ),
    (∀ γ ∈ ratU σ Y.J, ∀ x, f (γ * x) = f x) → ∀ (γ : UA σ Y₁.J) (m₀ : UA σ Y.J), m₀ ∈ ratU σ Y.J →
    IsLevi (W₁ := Y₁) H 1 γ m₀ → ∀ (μ : Measure (unip σ Y H)) (𝓕 : Set (unip σ Y H)), μ.IsHaarMeasure →
    IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unip σ Y H)) 𝓕 μ → μ 𝓕 = 1 →
    ∀ x, ∫ u in 𝓕, f (u.1 * (m₀ * x)) ∂μ = ∫ u in 𝓕, f (u.1 * x) ∂μ := by
  intro F E _ _ _ _ _ σ n n₁ Y Y₁ H f hf γ m hm hL μ 𝓕 hμ h𝓕 h1 x
  obtain ⟨i1, i2, i3, i4⟩ := topFacts (F := F) σ Y.J
  haveI : BorelSpace (UA σ Y.J) := ⟨rfl⟩
  haveI : LocallyCompactSpace (unip σ Y H) := (isClosed_unip σ Y H).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI := countable_ratU (σ := σ) Y.J
  haveI : Countable ((ratU σ Y.J).subgroupOf (unip σ Y H)) :=
    Function.Injective.countable (f := fun g : (ratU σ Y.J).subgroupOf (unip σ Y H) => (⟨g.1.1, g.2⟩ : ratU σ Y.J))
      fun g h hgh => by
        apply Subtype.ext; apply Subtype.ext
        simpa using congrArg Subtype.val hgh
  obtain ⟨hx, -, hι⟩ := hL
  rw [Units.val_one, one_smul] at hx
  have hx' : mat m⁻¹ *ᵥ incV F H.x = incV F H.x := by
    conv_lhs => rw [← hx]
    rw [Matrix.mulVec_mulVec, mat_inv_mul', Matrix.one_mulVec]
  have g1 : mat γ⁻¹ * mat γ = 1 := mat_inv_mul' γ
  have g2 : mat γ * mat γ⁻¹ = 1 := by simpa using mat_inv_mul' γ⁻¹
  have hι' : mat m⁻¹ * incM F H.ι = incM F H.ι * mat γ⁻¹ := by
    calc mat m⁻¹ * incM F H.ι = mat m⁻¹ * (incM F H.ι * mat γ) * mat γ⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, g2, Matrix.mul_one]
      _ = incM F H.ι * mat γ⁻¹ := by rw [← hι, ← Matrix.mul_assoc, mat_inv_mul', Matrix.one_mul]
  have k1 := conj_mem Y H m _ _ g1 hx' hx hι hι'
  have k2 := conj_mem Y H m⁻¹ _ _ g2 (by rwa [inv_inv]) hx' hι' (by rwa [inv_inv])
  let φ : unip σ Y H ≃* unip σ Y H :=
    { toFun := fun u => ⟨m⁻¹ * u.1 * m, k1 _ u.2⟩
      invFun := fun u => ⟨m⁻¹⁻¹ * u.1 * m⁻¹, k2 _ u.2⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun u v => Subtype.ext (by simp [mul_assoc]) }
  have c1 : Continuous φ :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have c2 : Continuous φ.symm :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have hφ : ∀ u, φ u ∈ (ratU σ Y.J).subgroupOf (unip σ Y H) ↔ u ∈ (ratU σ Y.J).subgroupOf (unip σ Y H) := by
    intro u
    simp only [Subgroup.mem_subgroupOf]
    show m⁻¹ * u.1 * m ∈ ratU σ Y.J ↔ _
    rw [Subgroup.mul_mem_cancel_right _ hm, Subgroup.mul_mem_cancel_left _ (inv_mem hm)]
  rw [← setIntegral_comp_aut ((ratU σ Y.J).subgroupOf (unip σ Y H)) φ c1 c2 hφ (fun u => f (u.1 * x)) ?_ μ 𝓕 h𝓕 h1]
  · refine congrArg _ (funext fun u => ?_)
    show _ = f (m⁻¹ * u.1 * m * x)
    rw [mul_assoc, mul_assoc, hf _ (inv_mem hm)]
  · intro δ hδ y
    show f ((δ.1 * y.1) * x) = f (y.1 * x)
    rw [mul_assoc]; exact hf _ (Subgroup.mem_subgroupOf.1 hδ) _

end GlobalTheory.UnipCTLevi

end
