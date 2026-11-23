import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicSubspaceInvariantSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicOrbitOrthogonalAtPlaceStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.ThK.EvUniq

theorem finRel_unique : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ r s r' s' i₀ i₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (M : Model σ X W)
    (M₁ : Model σ X W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    M₁.IsGood B.ψ → ∀ (v : Pl F) (T T' : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d₁ → Fv F v) → ℂ),
    GlobalTheory.ThK.EvUniq.FinRel B M M₁ H' v T → GlobalTheory.ThK.EvUniq.FinRel B M M₁ H' v T' → (SB _).map T = SB _ → (SB _).map T' = SB _ →
    T (M.vac v) = M₁.vac v → T' (M.vac v) = M₁.vac v → ∀ φ ∈ SB (Fin n × Fin d → Fv F v), T' φ = T φ := by
  intro _ F E _ _ _ _ _ σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ hB hX hW hM hH hM₁ v T T' hT hT' hTs hT's hv hv'
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F _).injective
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt B.ψ hB.std.1 v
  have hψ1 : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hB.std v
  have hsb : ∀ {κ : Type} [Fintype κ] (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ SB (κ → Fv F v),
      schr (GlobalTheory.LatVac.psiAt B.ψ v) w φ ∈ SB (κ → Fv F v) := fun w φ hφ =>
    GlobalTheory.SchrSB.schr_mem_SB B.ψ hB.std.1 v w φ hφ
  have hAtι : ∀ z : Matrix (Fin n) (Fin d₁) (AE F E), At (evFin F v) z →
      At (evFin F v) (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) := by
    intro z hz a ha
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hz a ha, Matrix.mul_zero, Matrix.zero_mul]
  have loc : ∀ T : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d₁ → Fv F v) → ℂ,
      GlobalTheory.ThK.EvUniq.FinRel B M M₁ H' v T → (SB _).map T = SB _ →
      (∀ z, At (evFin F v) z → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
        T (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v
          (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)) φ) =
          schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M₁.co v z) (T φ)) ∧
      (∀ u ∈ iso0 (F := F) n H', At (evFin F v) u → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
        T (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u) φ) = T φ) := by
    intro T hT hTs
    refine ⟨fun z hz φ hφ => ?_, fun u hu hat φ hφ => ?_⟩
    · have hTφ : T φ ∈ SB (Fin n × Fin d₁ → Fv F v) := hTs ▸ Submodule.mem_map_of_mem hφ
      exact hT.1 z hz φ hφ _ (hsb _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v _ (hAtι z hz) φ) _
        (hsb _ _ hTφ) (GlobalTheory.VacBridge.rho_acts_locCo M₁.co B.ψ v z hz (T φ))
    · exact hT.2 u hu hat φ hφ _ (hsb _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v u hat φ)
  obtain ⟨l1, l2⟩ := loc T hT hTs
  obtain ⟨l1', l2'⟩ := loc T' hT' hT's
  obtain ⟨hiso, hperp⟩ := GlobalTheory.T.isotropic_orbit_orthogonal_at_place' F E σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M hB hX hW hH v
  let U : Submodule (Fv F v) ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :=
    { carrier := {w | ∃ u ∈ iso0 (F := F) n H', At (evFin F v) u ∧ GlobalTheory.LatVac.locCo M.co v u = w}
      add_mem' := by
        rintro _ _ ⟨u, ⟨y, rfl⟩, hu, rfl⟩ ⟨u', ⟨y', rfl⟩, hu', rfl⟩
        exact ⟨_, ⟨y + y', (Matrix.add_vecMulVec y y' _).symm⟩, fun a ha => by rw [smul_add, hu a ha, hu' a ha, add_zero],
          map_add _ _ _⟩
      zero_mem' := ⟨0, ⟨0, (Matrix.zero_vecMulVec _).symm⟩, fun a _ => smul_zero a, map_zero _⟩
      smul_mem' := by
        rintro c _ ⟨u, ⟨y, rfl⟩, hu, rfl⟩
        refine ⟨GlobalTheory.LatVac.liftV v c • Matrix.vecMulVec y (incV F H'.x), ⟨GlobalTheory.LatVac.liftV v c • y, ?_⟩, ?_, ?_⟩
        · ext i j
          simp [Matrix.vecMulVec_apply, smul_mul_assoc]
        · intro a ha
          rw [smul_comm, hu a ha, smul_zero]
        · rw [GlobalTheory.LatOpenCpt.locCo_smul, GlobalTheory.LatVac.evFin_liftV] }
  let S : Submodule ℂ ((Fin n × Fin d → Fv F v) → ℂ) := SB _ ⊓ LinearMap.ker (T' - T)
  have hmem : ∀ φ, φ ∈ S ↔ φ ∈ SB (Fin n × Fin d → Fv F v) ∧ T' φ = T φ := by
    intro φ
    simp [S, sub_eq_zero]
  have hne : ∀ x, GlobalTheory.LatVac.psiAt B.ψ v x ≠ 0 := fun x h => by
    have := AddChar.map_add_eq_mul (GlobalTheory.LatVac.psiAt B.ψ v) x (-x)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
    exact one_ne_zero this
  have hkill : ∀ T : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d₁ → Fv F v) → ℂ,
      (∀ u ∈ iso0 (F := F) n H', At (evFin F v) u → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
        T (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u) φ) = T φ) →
      Submodule.span ℂ {f | ∃ u ∈ U, ∃ φ ∈ SB (Fin n × Fin d → Fv F v), f = schr (GlobalTheory.LatVac.psiAt B.ψ v) u φ - φ} ≤
        LinearMap.ker T := by
    intro T h2
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨u, hu, hat, rfl⟩, φ, hφ, rfl⟩
    simp [map_sub, h2 u hu hat φ hφ]
  have key := GlobalTheory.T.isotropic_subspace_invariant_schwartz (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψ1 U
    (by
      rintro _ ⟨u, hu, hat, rfl⟩ _ ⟨u', hu', hat', rfl⟩
      exact hiso u hu hat u' hu' hat')
    S inf_le_left
    (by
      rintro _ ⟨u, hu, hat, rfl⟩ φ hφ
      rw [hmem]
      refine ⟨sub_mem (hsb _ φ hφ) hφ, ?_⟩
      rw [map_sub, map_sub, l2 u hu hat φ hφ, l2' u hu hat φ hφ, sub_self, sub_self])
    (by
      intro w hw φ hφ
      rw [hmem] at hφ ⊢
      obtain ⟨u, hu, hat, z, hz, rfl⟩ := hperp w fun u hu hat => hw _ ⟨u, hu, hat, rfl⟩
      refine ⟨hsb _ φ hφ.1, ?_⟩
      have e' : ∀ a b : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v),
          schr (GlobalTheory.LatVac.psiAt B.ψ v) (a + b) φ = (GlobalTheory.LatVac.psiAt B.ψ v (⅟(2 : Fv F v) * (a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2)))⁻¹ •
            schr (GlobalTheory.LatVac.psiAt B.ψ v) a (schr (GlobalTheory.LatVac.psiAt B.ψ v) b φ) := fun a b => by
        rw [GlobalTheory.WeilM.schr_schr, smul_smul, inv_mul_cancel₀ (hne _), one_smul]
      rw [e', map_smul, map_smul, l2 u hu hat _ (hsb _ φ hφ.1), l2' u hu hat _ (hsb _ φ hφ.1),
        l1 z hz φ hφ.1, l1' z hz φ hφ.1, hφ.2])
    (M.vac v) ((hmem _).2 ⟨(hM.vac v).1, by rw [hv, hv']⟩)
    (fun h => (hM₁.vac v).2.1 (by rw [← hv]; exact hkill T l2 h))
  intro φ hφ
  rw [← key] at hφ
  exact ((hmem φ).1 hφ).2

end GlobalTheory.ThK.EvUniq
