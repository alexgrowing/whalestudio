import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicVectorHermitianRankGeThreeIndefin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordinateAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentFundamentalDomainExists

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

open GlobalTheory.UnipMass

noncomputable section

namespace GlobalTheory.UnipHermCover

theorem cocompact_herm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n n₁ : ℕ) (V : Spc F E n) (H : Plane E n n₁), (∀ i j, σ (V.J j i) = V.J i j) → form σ V.J H.x H.x = 0 → form σ V.J H.y H.y = 0 → form σ V.J H.x H.y = 1 → (∀ u, form σ V.J (H.ι *ᵥ u) H.x = 0 ∧ form σ V.J (H.ι *ᵥ u) H.y = 0) → (∀ v : Fin n → E, ∃ (s t : E) (u : Fin n₁ → E), v = s • H.x + H.ι *ᵥ u + t • H.y) → ∃ K : Set (unip σ V H), IsCompact K ∧ ∀ g : unip σ V H, ∃ γ : (ratU σ V.J).subgroupOf (unip σ V H), γ • g ∈ K := by
  intro F E _ _ _ _ _ σ hcm n n₁ V H hherm hxx0 hyy0 hxy0 horth0 hspan
  have hσ : ∀ a, σ (σ a) = a := cm_conj_conj hcm
  obtain ⟨δ, hδ0, hδ⟩ := GlobalTheory.UnipMassHerm.exists_anti hcm
  let W' : Spc F E n := ⟨δ • V.J, V.L, V.θ, V.bas⟩
  let H'' : Plane E n n₁ := ⟨H.x, (-δ⁻¹) • H.y, H.ι, H.𝔟⟩
  have hform : ∀ v w, form σ W'.J v w = δ * form σ V.J v w := GlobalTheory.UnipMassHerm.form_smul_mat σ V.J δ
  have hσt : σ (-δ⁻¹) = δ⁻¹ := by rw [map_neg, map_inv₀, hδ, inv_neg, neg_neg]
  have hxx : form σ W'.J H''.x H''.x = 0 := by rw [hform]; show δ * form σ V.J H.x H.x = 0; rw [hxx0, mul_zero]
  have hyy : form σ W'.J H''.y H''.y = 0 := by
    rw [hform]; show δ * form σ V.J ((-δ⁻¹) • H.y) ((-δ⁻¹) • H.y) = 0
    rw [GlobalTheory.UnipMassHerm.form_smul_left, GlobalTheory.UnipMassHerm.form_smul_right, hyy0]; ring
  have hxy : form σ W'.J H''.x H''.y = 1 := by
    rw [hform]; show δ * form σ V.J H.x ((-δ⁻¹) • H.y) = 1
    rw [GlobalTheory.UnipMassHerm.form_smul_right, hxy0, hσt, mul_one, mul_inv_cancel₀ hδ0]
  have horth : ∀ u, form σ W'.J (H''.ι *ᵥ u) H''.x = 0 ∧ form σ W'.J (H''.ι *ᵥ u) H''.y = 0 := by
    intro u
    refine ⟨?_, ?_⟩
    · rw [hform]; show δ * form σ V.J (H.ι *ᵥ u) H.x = 0; rw [(horth0 u).1, mul_zero]
    · rw [hform]; show δ * form σ V.J (H.ι *ᵥ u) ((-δ⁻¹) • H.y) = 0
      rw [GlobalTheory.UnipMassHerm.form_smul_right, (horth0 u).2]; ring
  have hspan'' : ∀ v : Fin n → E, ∃ (s t : E) (u : Fin n₁ → E), v = s • H''.x + H''.ι *ᵥ u + t • H''.y := by
    intro v
    obtain ⟨s, t, u, hv⟩ := hspan v
    refine ⟨s, t * -δ, u, ?_⟩
    show v = s • H.x + H.ι *ᵥ u + (t * -δ) • (-δ⁻¹) • H.y
    rw [smul_smul, show t * -δ * -δ⁻¹ = t by field_simp, hv]
  have horthA : ∀ z, hA σ W'.J (incM F H''.ι *ᵥ z) (incV F H''.x) = 0 := by
    intro z
    rw [hA_incM_incV]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h1 := (horth (Pi.single j 1)).1
    rw [Matrix.mulVec_single_one] at h1
    rw [show (fun i => H''.ι i j) = H''.ι.col j from rfl, h1, map_zero, mul_zero]
  have hyp : Hyp σ W' H'' := by
    refine ⟨hσ, fun i j => ?_, by rw [hA_incV, hxx, map_zero], horthA⟩
    show σ (δ * V.J j i) = -(δ * V.J i j)
    rw [map_mul, hδ, hherm]; ring
  obtain ⟨K', hK', hcov'⟩ := cocompact hyp hxx hyy hxy horth hspan''
  have hUG := GlobalTheory.UnipMassHerm.UG_smul (F := F) σ V.J hδ0
  let φ : UA σ W'.J →* UA σ V.J := Subgroup.inclusion hUG.le
  let φ' : UA σ V.J →* UA σ W'.J := Subgroup.inclusion hUG.ge
  have hmap : (unip σ W' H'').map φ ≤ unip σ V H := by
    rw [unip, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨u, hu, rfl⟩
    exact hu
  have hmap' : (unip σ V H).map φ' ≤ unip σ W' H'' := by
    rw [unip, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨u, hu, rfl⟩
    exact hu
  let Ψ : unip σ W' H'' → unip σ V H := fun g => ⟨φ g.1, hmap ⟨g.1, g.2, rfl⟩⟩
  have hΨ : Continuous Ψ :=
    Continuous.subtype_mk (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _) _
  refine ⟨Ψ '' K', hK'.image hΨ, fun g => ?_⟩
  obtain ⟨γ', hγ'⟩ := hcov' ⟨φ' g.1, hmap' ⟨g.1, g.2, rfl⟩⟩
  refine ⟨⟨Ψ γ'.1, ?_⟩, ⟨_, hγ', ?_⟩⟩
  · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2
      (Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 γ'.2)))
  · exact unip_ext rfl

end GlobalTheory.UnipHermCover
