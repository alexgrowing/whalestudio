import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRelG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicSubspaceInvariantSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicOrbitOrthogonalAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedModelLocalPlaceDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedModelLocalPlaceSecond
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.ThK.EvUniqA

theorem finRelG_isoA_unique : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁)
    (H' : Plane E d d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    M.IsGood B.ψ → H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
    ∀ (v : Pl F) (T T' : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ),
    GlobalTheory.ThK.EvFactor.FinRelG B M M₁ H.ι H'.ι (isoA H H') v T → GlobalTheory.ThK.EvFactor.FinRelG B M M₁ H.ι H'.ι (isoA H H') v T' →
    (SB _).map T = SB _ → (SB _).map T' = SB _ → T (M.vac v) = M₁.vac v → T' (M.vac v) = M₁.vac v →
    ∀ φ ∈ SB (Fin n × Fin d → Fv F v), T' φ = T φ := by
  intro _ F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' M M₁ hB hX hW hM hH hH' hM₁ v T T' hT hT' hTs hT's hv hv'
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F _).injective
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt B.ψ hB.std.1 v
  have hψ1 : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hB.std v
  have hsb : ∀ {κ : Type} [Fintype κ] (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ SB (κ → Fv F v),
      schr (GlobalTheory.LatVac.psiAt B.ψ v) w φ ∈ SB (κ → Fv F v) := fun w φ hφ =>
    GlobalTheory.SchrSB.schr_mem_SB B.ψ hB.std.1 v w φ hφ
  have hAtι : ∀ z : Matrix (Fin n₁) (Fin d₁) (AE F E), At (evFin F v) z →
      At (evFin F v) (incM F H.ι * z * (incM F H'.ι)ᵀ) := by
    intro z hz a ha
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hz a ha, Matrix.mul_zero, Matrix.zero_mul]
  have loc : ∀ T : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ,
      GlobalTheory.ThK.EvFactor.FinRelG B M M₁ H.ι H'.ι (isoA H H') v T → (SB _).map T = SB _ →
      (∀ z, At (evFin F v) z → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
        T (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (incM F H.ι * z * (incM F H'.ι)ᵀ)) φ) =
          schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M₁.co v z) (T φ)) ∧
      (∀ u ∈ isoA (F := F) H H', At (evFin F v) u → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
        T (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u) φ) = T φ) := by
    intro T hT hTs
    refine ⟨fun z hz φ hφ => ?_, fun u hu hat φ hφ => ?_⟩
    · have hTφ : T φ ∈ SB (Fin n₁ × Fin d₁ → Fv F v) := hTs ▸ Submodule.mem_map_of_mem hφ
      exact hT.1 z hz φ hφ _ (hsb _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v _ (hAtι z hz) φ) _
        (hsb _ _ hTφ) (GlobalTheory.VacBridge.rho_acts_locCo M₁.co B.ψ v z hz (T φ))
    · exact hT.2 u hu hat φ hφ _ (hsb _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v u hat φ)
  obtain ⟨l1, l2⟩ := loc T hT hTs
  obtain ⟨l1', l2'⟩ := loc T' hT' hT's
  have hiso := GlobalTheory.T.adapted_model_local_place_descent F E σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' M hB hX hW hH hH' v
  have hperp := GlobalTheory.T.adapted_model_local_place_second F E σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' M hB hX hW hH hH' v
  let U0 : Submodule (Fv F v) ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :=
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
  let U1 : Submodule (Fv F v) ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :=
    { carrier := {w | ∃ u ∈ {u : Matrix (Fin n) (Fin d) (AE F E) | ∃ z, u = Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z)},
        At (evFin F v) u ∧ GlobalTheory.LatVac.locCo M.co v u = w}
      add_mem' := by
        rintro _ _ ⟨u, ⟨y, rfl⟩, hu, rfl⟩ ⟨u', ⟨y', rfl⟩, hu', rfl⟩
        refine ⟨_, ⟨y + y', ?_⟩, fun a ha => by rw [smul_add, hu a ha, hu' a ha, add_zero], map_add _ _ _⟩
        ext i j
        simp [Matrix.vecMulVec_apply, Matrix.mulVec_add, mul_add]
      zero_mem' := ⟨0, ⟨0, by ext i j; simp [Matrix.vecMulVec_apply]⟩, fun a _ => smul_zero a, map_zero _⟩
      smul_mem' := by
        rintro c _ ⟨u, ⟨y, rfl⟩, hu, rfl⟩
        refine ⟨GlobalTheory.LatVac.liftV v c • Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ y), ⟨GlobalTheory.LatVac.liftV v c • y, ?_⟩, ?_, ?_⟩
        · ext i j
          simp [Matrix.vecMulVec_apply, Matrix.mulVec_smul]
        · intro a ha
          rw [smul_comm, hu a ha, smul_zero]
        · rw [GlobalTheory.LatOpenCpt.locCo_smul, GlobalTheory.LatVac.evFin_liftV] }
  let U := U0 ⊔ U1
  have hUgen : ∀ u ∈ isoA (F := F) H H', At (evFin F v) u → GlobalTheory.LatVac.locCo M.co v u ∈ U := by
    rintro u (hu | hu) hat
    · exact Submodule.mem_sup_left ⟨u, hu, hat, rfl⟩
    · exact Submodule.mem_sup_right ⟨u, hu, hat, rfl⟩
  have hU : ∀ w ∈ U, ∃ u ∈ isoA (F := F) H H', At (evFin F v) u ∧ ∃ u' ∈ isoA (F := F) H H', At (evFin F v) u' ∧
      w = GlobalTheory.LatVac.locCo M.co v u + GlobalTheory.LatVac.locCo M.co v u' := by
    intro w hw
    obtain ⟨_, ⟨u, hu, hat, rfl⟩, _, ⟨u', hu', hat', rfl⟩, rfl⟩ := Submodule.mem_sup.1 hw
    exact ⟨u, Or.inl hu, hat, u', Or.inr hu', hat', rfl⟩
  have hUiso : ∀ w ∈ U, ∀ w' ∈ U, w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2 = 0 := by
    intro w hw w' hw'
    obtain ⟨u, hu, hat, u', hu', hat', rfl⟩ := hU w hw
    obtain ⟨x, hx, hxt, x', hx', hxt', rfl⟩ := hU w' hw'
    simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
    linear_combination hiso u hu hat x hx hxt + hiso u hu hat x' hx' hxt' + hiso u' hu' hat' x hx hxt +
      hiso u' hu' hat' x' hx' hxt'
  have hne : ∀ x, GlobalTheory.LatVac.psiAt B.ψ v x ≠ 0 := fun x h => by
    have := AddChar.map_add_eq_mul (GlobalTheory.LatVac.psiAt B.ψ v) x (-x)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
    exact one_ne_zero this
  have e' : ∀ (a b : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) (φ : (Fin n × Fin d → Fv F v) → ℂ),
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (a + b) φ = (GlobalTheory.LatVac.psiAt B.ψ v (⅟(2 : Fv F v) * (a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2)))⁻¹ •
        schr (GlobalTheory.LatVac.psiAt B.ψ v) a (schr (GlobalTheory.LatVac.psiAt B.ψ v) b φ) := fun a b φ => by
    rw [GlobalTheory.WeilM.schr_schr, smul_smul, inv_mul_cancel₀ (hne _), one_smul]
  have inv : ∀ T : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ,
      (∀ u ∈ isoA (F := F) H H', At (evFin F v) u → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
        T (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u) φ) = T φ) →
      ∀ w ∈ U, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), T (schr (GlobalTheory.LatVac.psiAt B.ψ v) w φ) = T φ := by
    intro T h2 w hw φ hφ
    obtain ⟨u, hu, hat, u', hu', hat', rfl⟩ := hU w hw
    rw [e', hiso u hu hat u' hu' hat', mul_zero, AddChar.map_zero_eq_one, inv_one, one_smul,
      h2 u hu hat _ (hsb _ φ hφ), h2 u' hu' hat' φ hφ]
  let S : Submodule ℂ ((Fin n × Fin d → Fv F v) → ℂ) := SB _ ⊓ LinearMap.ker (T' - T)
  have hmem : ∀ φ, φ ∈ S ↔ φ ∈ SB (Fin n × Fin d → Fv F v) ∧ T' φ = T φ := by
    intro φ
    simp [S, sub_eq_zero]
  have hkill : ∀ T : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ,
      (∀ w ∈ U, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), T (schr (GlobalTheory.LatVac.psiAt B.ψ v) w φ) = T φ) →
      Submodule.span ℂ {f | ∃ u ∈ U, ∃ φ ∈ SB (Fin n × Fin d → Fv F v), f = schr (GlobalTheory.LatVac.psiAt B.ψ v) u φ - φ} ≤
        LinearMap.ker T := by
    intro T h2
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, hu, φ, hφ, rfl⟩
    simp [map_sub, h2 u hu φ hφ]
  have key := GlobalTheory.T.isotropic_subspace_invariant_schwartz (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψ1 U hUiso S inf_le_left
    (by
      intro u hu φ hφ
      rw [hmem]
      refine ⟨sub_mem (hsb _ φ hφ) hφ, ?_⟩
      rw [map_sub, map_sub, inv T l2 u hu φ hφ, inv T' l2' u hu φ hφ, sub_self, sub_self])
    (by
      intro w hw φ hφ
      rw [hmem] at hφ ⊢
      obtain ⟨u, hu, hat, u', hu', hat', z, hz, rfl⟩ := hperp w fun u hu hat => hw _ (hUgen u hu hat)
      refine ⟨hsb _ φ hφ.1, ?_⟩
      have hUu : GlobalTheory.LatVac.locCo M.co v u + GlobalTheory.LatVac.locCo M.co v u' ∈ U :=
        add_mem (hUgen u hu hat) (hUgen u' hu' hat')
      rw [e', map_smul, map_smul, inv T l2 _ hUu _ (hsb _ φ hφ.1), inv T' l2' _ hUu _ (hsb _ φ hφ.1),
        l1 z hz φ hφ.1, l1' z hz φ hφ.1, hφ.2])
    (M.vac v) ((hmem _).2 ⟨(hM.vac v).1, by rw [hv, hv']⟩)
    (fun h => (hM₁.vac v).2.1 (by rw [← hv]; exact hkill T (inv T l2) h))
  intro φ hφ
  rw [← key] at hφ
  exact ((hmem φ).1 hφ).2

end GlobalTheory.ThK.EvUniqA
