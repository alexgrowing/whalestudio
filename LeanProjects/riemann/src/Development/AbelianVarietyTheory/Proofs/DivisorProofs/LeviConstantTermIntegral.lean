import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicUnfoldingIntegral
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB
open GlobalTheory.ThK.DescB

noncomputable section

namespace GlobalTheory.UnipCT

theorem setIntegral_conj_levi_of_unip_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n n₁ : ℕ)
    (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁) (γ : UA σ W₁.J) (m : UA σ W.J),
    m ∈ ratU σ W.J → IsLevi H 1 γ m → ∀ Φ : UA σ W.J → ℂ,
    (∀ δ ∈ ratU σ W.J ⊓ unip σ W H, ∀ u ∈ unip σ W H, Φ (δ * u) = Φ u) →
    ∀ (μ : Measure (unip σ W H)) (𝓕 : Set (unip σ W H)), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H)) 𝓕 μ → μ 𝓕 = 1 →
      ∫ u in 𝓕, Φ (m * u.1 * m⁻¹) ∂μ = ∫ u in 𝓕, Φ u.1 ∂μ := by
  intro F E _ _ _ _ _ σ n n₁ W W₁ H γ m hm hL Φ hΦ μ 𝓕 hμ h𝓕 h1
  obtain ⟨hLx, -, hLι⟩ := hL
  have hx : mat m *ᵥ incV F H.x = incV F H.x := by simpa using hLx
  have hx' : mat m⁻¹ *ᵥ incV F H.x = incV F H.x := by
    conv_lhs => rw [← hx]
    rw [Matrix.mulVec_mulVec, mat_inv_mul', Matrix.one_mulVec]
  have hι' : mat m⁻¹ * incM F H.ι = incM F H.ι * mat γ⁻¹ := by
    calc mat m⁻¹ * incM F H.ι = mat m⁻¹ * (incM F H.ι * mat γ) * mat γ⁻¹ := by
          rw [Matrix.mul_assoc (mat m⁻¹), Matrix.mul_assoc (incM F H.ι), mat_mul_inv', Matrix.mul_one]
      _ = incM F H.ι * mat γ⁻¹ := by
          rw [← hLι, ← Matrix.mul_assoc, mat_inv_mul', Matrix.one_mul]
  have hN : ∀ u ∈ unip σ W H, m⁻¹ * u * m ∈ unip σ W H ∧ m * u * m⁻¹ ∈ unip σ W H := by
    intro u hu
    rw [unip_eq] at hu ⊢
    refine ⟨conj_mem_unipSet H m γ hx hLι u hu, ?_⟩
    simpa using conj_mem_unipSet H m⁻¹ γ⁻¹ hx' hι' u hu
  obtain ⟨i1, i2, i3, i4⟩ := topFacts (F := F) σ W.J
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI : LocallyCompactSpace (unip σ W H) := (isClosed_unip σ W H).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI := countable_ratU (σ := σ) W.J
  let Γ : Subgroup (unip σ W H) := (ratU σ W.J).subgroupOf (unip σ W H)
  haveI : Countable Γ :=
    Function.Injective.countable (f := fun g : Γ => (⟨g.1.1, g.2⟩ : ratU σ W.J))
      fun g h hgh => by
        apply Subtype.ext; apply Subtype.ext
        simpa using congrArg Subtype.val hgh
  let cφ : unip σ W H ≃ₜ* unip σ W H :=
    { toFun := fun u => ⟨m * u * m⁻¹, (hN u u.2).2⟩
      invFun := fun u => ⟨m⁻¹ * u * m, (hN u u.2).1⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
      continuous_invFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _ }
  have hc1 : ∀ u : unip σ W H, (cφ u : UA σ W.J) = m * u * m⁻¹ := fun _ => rfl
  have hc2 : ∀ u : unip σ W H, (cφ.symm u : UA σ W.J) = m⁻¹ * u * m := fun _ => rfl
  have hΓ1 : ∀ a ∈ Γ, cφ a ∈ Γ := fun a ha => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    rw [hc1]
    exact (ratU σ W.J).mul_mem ((ratU σ W.J).mul_mem hm ha) ((ratU σ W.J).inv_mem hm)
  have hΓ2 : ∀ a ∈ Γ, cφ.symm a ∈ Γ := fun a ha => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    rw [hc2]
    exact (ratU σ W.J).mul_mem ((ratU σ W.J).mul_mem ((ratU σ W.J).inv_mem hm) ha) hm
  let cq : Γ ≃ Γ :=
    { toFun := fun a => ⟨cφ a, hΓ1 a a.2⟩
      invFun := fun a => ⟨cφ.symm a, hΓ2 a a.2⟩
      left_inv := fun a => Subtype.ext (cφ.symm_apply_apply _)
      right_inv := fun a => Subtype.ext (cφ.apply_symm_apply _) }
  let cm : unip σ W H ≃ᵐ unip σ W H := cφ.toHomeomorph.toMeasurableEquiv
  have hmp : MeasurePreserving cm μ (μ.map cm) := cm.measurable.measurePreserving _
  haveI hν : (μ.map cm).IsHaarMeasure := cφ.isHaarMeasure_map μ
  have h𝓕' : IsFundamentalDomain Γ (cm.symm ⁻¹' 𝓕) (μ.map cm) :=
    h𝓕.preimage_of_equiv (hmp.symm cm).quasiMeasurePreserving (e := cq) cq.bijective fun a u => by
      show cφ.symm (cφ a * u) = a * cφ.symm u
      rw [map_mul, cφ.symm_apply_apply]
  have hm1 : (μ.map cm) (cm.symm ⁻¹' 𝓕) = 1 := by
    rw [cm.map_apply, ← Set.preimage_comp, cm.symm_comp_self, Set.preimage_id, h1]
  have key := setIntegral_fd_eq Γ (fun u => Φ u.1) (fun δ hδ x =>
      hΦ δ.1 ⟨Subgroup.mem_subgroupOf.1 hδ, δ.2⟩ x.1 x.2) (μ.map cm) μ (cm.symm ⁻¹' 𝓕) 𝓕 h𝓕' h𝓕 hm1 h1
  rw [← key, setIntegral_map_equiv, ← Set.preimage_comp, cm.symm_comp_self, Set.preimage_id]
  rfl

end GlobalTheory.UnipCT

end
