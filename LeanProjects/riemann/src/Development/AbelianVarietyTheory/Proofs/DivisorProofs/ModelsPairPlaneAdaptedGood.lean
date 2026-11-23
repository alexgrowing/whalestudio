import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRelAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicSubspaceInvariantSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRelOfEv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermSkewAdaptedLocalModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermSkewAdaptedLocalModelTwoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelsAdaptedPlanesPairStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

theorem GlobalTheory.ThK.IsoUniq.finRel_unique : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₂ : Model σ X₁ W₁)
    (H : Plane E n n₁) (H' : Plane E d d₁) (i₀ i₁ j₀ j₁ : ℕ), B.IsGood σ → (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') →
    M.IsGood B.ψ → M₂.IsGood B.ψ → H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (v : Pl F) (T T' : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ),
    GlobalTheory.ThK.EvUniqB.FinRel B M M₂ H.ι H'.ι (isoA H H') v T → GlobalTheory.ThK.EvUniqB.FinRel B M M₂ H.ι H'.ι (isoA H H') v T' →
    (SB _).map T = SB _ → (SB _).map T' = SB _ → T (M.vac v) = M₂.vac v → T' (M.vac v) = M₂.vac v →
    ∀ φ ∈ SB (Fin n × Fin d → Fv F v), T' φ = T φ := by
  intro _ F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₂ H H' i₀ i₁ j₀ j₁ hB hXW hM hM₂ hH hH' v T T' hT hT' hTs hT's hv hv'
  obtain ⟨r, s, r', s', hX, hW⟩ := hXW
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F _).injective
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt B.ψ hB.std.1 v
  have hψ1 : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hB.std v
  have hsb : ∀ {κ : Type} [Fintype κ] (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ SB (κ → Fv F v),
      schr (GlobalTheory.LatVac.psiAt B.ψ v) w φ ∈ SB (κ → Fv F v) := fun w φ hφ =>
    GlobalTheory.SchrSB.schr_mem_SB B.ψ hB.std.1 v w φ hφ
  have hAtι : ∀ z : Matrix (Fin n₁) (Fin d₁) (AE F E), At (evFin F v) z →
      At (evFin F v) (incM F H.ι * z * (incM F H'.ι)ᵀ) := by
    intro z hz c hc
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hz c hc, Matrix.mul_zero, Matrix.zero_mul]
  have loc : ∀ T : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ,
      GlobalTheory.ThK.EvUniqB.FinRel B M M₂ H.ι H'.ι (isoA H H') v T → (SB _).map T = SB _ →
      (∀ z, At (evFin F v) z → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
        T (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (incM F H.ι * z * (incM F H'.ι)ᵀ)) φ) =
          schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M₂.co v z) (T φ)) ∧
      (∀ u ∈ isoA (F := F) H H', At (evFin F v) u → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
        T (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u) φ) = T φ) := by
    intro T hT hTs
    refine ⟨fun z hz φ hφ => ?_, fun u hu hat φ hφ => ?_⟩
    · have hTφ : T φ ∈ SB (Fin n₁ × Fin d₁ → Fv F v) := hTs ▸ Submodule.mem_map_of_mem hφ
      exact hT.1 z hz φ hφ _ (hsb _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v _ (hAtι z hz) φ) _
        (hsb _ _ hTφ) (GlobalTheory.VacBridge.rho_acts_locCo M₂.co B.ψ v z hz (T φ))
    · exact hT.2 u hu hat φ hφ _ (hsb _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v u hat φ)
  obtain ⟨l1, l2⟩ := loc T hT hTs
  obtain ⟨l1', l2'⟩ := loc T' hT' hT's
  have hiso := fun u hu hat u' hu' hat' => GlobalTheory.T.herm_skew_adapted_local_model F E σ B n n₁ d d₁ r s r' s' i₀ i₁ j₀ j₁ X X₁ W W₁ H H' M hB hX hW hH hH' v u hu hat u' hu' hat'
  have hperp := GlobalTheory.T.herm_skew_adapted_local_model_two F E σ B n n₁ d d₁ r s r' s' i₀ i₁ j₀ j₁ X X₁ W W₁ H H' M hB hX hW hH hH' v
  have m1 : ∀ z, Matrix.vecMulVec z (incV F H'.x) ∈ isoA (F := F) H H' := fun z => Or.inl ⟨z, rfl⟩
  have m2 : ∀ y, Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ y) ∈ isoA (F := F) H H' := fun y => Or.inr ⟨y, rfl⟩
  have at0 : At (evFin F v) (0 : Matrix (Fin n) (Fin d) (AE F E)) := fun c _ => smul_zero c
  have vz0 : Matrix.vecMulVec (0 : Fin n → AE F E) (incV F H'.x) = 0 := by
    ext i j; simp [Matrix.vecMulVec_apply]
  have vz : ∀ x : Fin n → AE F E, Matrix.vecMulVec x (0 : Fin d → AE F E) = 0 := fun x => by
    ext i j; simp [Matrix.vecMulVec_apply]
  have vz1 : Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ (0 : Fin d₁ → AE F E)) = 0 := by
    ext i j; simp [Matrix.vecMulVec_apply]
  have atAdd : ∀ {A B' : Matrix (Fin n) (Fin d) (AE F E)}, At (evFin F v) A → At (evFin F v) B' →
      At (evFin F v) (A + B') := fun hA hB' c hc => by rw [smul_add, hA c hc, hB' c hc, add_zero]
  let U : Submodule (Fv F v) ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :=
    { carrier := {w | ∃ z y, At (evFin F v) (Matrix.vecMulVec z (incV F H'.x)) ∧
          At (evFin F v) (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ y)) ∧
          w = GlobalTheory.LatVac.locCo M.co v (Matrix.vecMulVec z (incV F H'.x)) +
            GlobalTheory.LatVac.locCo M.co v (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ y))}
      add_mem' := by
        rintro _ _ ⟨z, y, hz, hy, rfl⟩ ⟨z', y', hz', hy', rfl⟩
        refine ⟨z + z', y + y', ?_, ?_, ?_⟩
        · rw [Matrix.add_vecMulVec]; exact atAdd hz hz'
        · rw [Matrix.mulVec_add, Matrix.vecMulVec_add]; exact atAdd hy hy'
        · rw [Matrix.add_vecMulVec, Matrix.mulVec_add, Matrix.vecMulVec_add, map_add, map_add]; abel
      zero_mem' := ⟨0, 0, by simpa [vz0, vz1, vz] using at0,
        by simpa [vz0, vz1, vz] using at0, by simp [vz0, vz1, vz]⟩
      smul_mem' := by
        rintro c _ ⟨z, y, hz, hy, rfl⟩
        refine ⟨GlobalTheory.LatVac.liftV v c • z, GlobalTheory.LatVac.liftV v c • y, ?_, ?_, ?_⟩
        · rw [Matrix.smul_vecMulVec]; intro e he; rw [smul_comm, hz e he, smul_zero]
        · rw [Matrix.mulVec_smul, Matrix.vecMulVec_smul]; intro e he; rw [smul_comm, hy e he, smul_zero]
        · rw [Matrix.smul_vecMulVec, Matrix.mulVec_smul, Matrix.vecMulVec_smul, smul_add,
            GlobalTheory.LatOpenCpt.locCo_smul, GlobalTheory.LatOpenCpt.locCo_smul, GlobalTheory.LatVac.evFin_liftV] }
  have hne : ∀ x, GlobalTheory.LatVac.psiAt B.ψ v x ≠ 0 := fun x h => by
    have := AddChar.map_add_eq_mul (GlobalTheory.LatVac.psiAt B.ψ v) x (-x)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
    exact one_ne_zero this
  have e' : ∀ (a' b' : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) φ,
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (a' + b') φ =
        (GlobalTheory.LatVac.psiAt B.ψ v (⅟(2 : Fv F v) * (a'.1 ⬝ᵥ b'.2 - b'.1 ⬝ᵥ a'.2)))⁻¹ •
          schr (GlobalTheory.LatVac.psiAt B.ψ v) a' (schr (GlobalTheory.LatVac.psiAt B.ψ v) b' φ) := fun a' b' φ => by
    rw [GlobalTheory.WeilM.schr_schr, smul_smul, inv_mul_cancel₀ (hne _), one_smul]
  have hUiso : ∀ w ∈ U, ∀ w' ∈ U, w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2 = 0 := by
    rintro _ ⟨z, y, hz, hy, rfl⟩ _ ⟨z', y', hz', hy', rfl⟩
    have h11 := hiso _ (m1 z) hz _ (m1 z') hz'
    have h12 := hiso _ (m1 z) hz _ (m2 y') hy'
    have h21 := hiso _ (m2 y) hy _ (m1 z') hz'
    have h22 := hiso _ (m2 y) hy _ (m2 y') hy'
    simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
    linear_combination h11 + h12 + h21 + h22
  have hU : ∀ T : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ,
      (∀ u ∈ isoA (F := F) H H', At (evFin F v) u → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
        T (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u) φ) = T φ) →
      ∀ w ∈ U, ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
        T (schr (GlobalTheory.LatVac.psiAt B.ψ v) w φ) = T φ := by
    rintro T h2 _ ⟨z, y, hz, hy, rfl⟩ φ hφ
    rw [e', hiso _ (m1 z) hz _ (m2 y) hy, mul_zero, AddChar.map_zero_eq_one, inv_one, one_smul,
      h2 _ (m1 z) hz _ (hsb _ φ hφ), h2 _ (m2 y) hy φ hφ]
  let S : Submodule ℂ ((Fin n × Fin d → Fv F v) → ℂ) := SB _ ⊓ LinearMap.ker (T' - T)
  have hmem : ∀ φ, φ ∈ S ↔ φ ∈ SB (Fin n × Fin d → Fv F v) ∧ T' φ = T φ := by
    intro φ
    simp [S, sub_eq_zero]
  have hkill : Submodule.span ℂ {f | ∃ u ∈ U, ∃ φ ∈ SB (Fin n × Fin d → Fv F v),
      f = schr (GlobalTheory.LatVac.psiAt B.ψ v) u φ - φ} ≤ LinearMap.ker T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, hu, φ, hφ, rfl⟩
    simp [map_sub, hU T l2 u hu φ hφ]
  have key := GlobalTheory.T.isotropic_subspace_invariant_schwartz (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψ1 U hUiso S inf_le_left
    (by
      intro u hu φ hφ
      rw [hmem]
      refine ⟨sub_mem (hsb _ φ hφ) hφ, ?_⟩
      rw [map_sub, map_sub, hU T l2 u hu φ hφ, hU T' l2' u hu φ hφ, sub_self, sub_self])
    (by
      intro w hw φ hφ
      rw [hmem] at hφ ⊢
      have hw' : ∀ u ∈ isoA (F := F) H H', At (evFin F v) u →
          (GlobalTheory.LatVac.locCo M.co v u).1 ⬝ᵥ w.2 - w.1 ⬝ᵥ (GlobalTheory.LatVac.locCo M.co v u).2 = 0 := by
        rintro u (⟨z, rfl⟩ | ⟨y, rfl⟩) hat
        · refine hw _ ⟨z, 0, hat, ?_, ?_⟩
          · simpa [vz0, vz1, vz] using at0
          · simp [vz0, vz1, vz]
        · refine hw _ ⟨0, y, ?_, hat, ?_⟩
          · simpa [vz0, vz1, vz] using at0
          · simp [vz0, vz1, vz]
      obtain ⟨z₀, hz₀, y₀, hy₀, z, hz, rfl⟩ := hperp w hw'
      have hu : GlobalTheory.LatVac.locCo M.co v (Matrix.vecMulVec z₀ (incV F H'.x)) +
          GlobalTheory.LatVac.locCo M.co v (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ y₀)) ∈ U :=
        ⟨z₀, y₀, hz₀, hy₀, rfl⟩
      refine ⟨hsb _ φ hφ.1, ?_⟩
      rw [e', map_smul, map_smul, hU T l2 _ hu _ (hsb _ φ hφ.1), hU T' l2' _ hu _ (hsb _ φ hφ.1),
        l1 z hz φ hφ.1, l1' z hz φ hφ.1, hφ.2])
    (M.vac v) ((hmem _).2 ⟨(hM.vac v).1, by rw [hv, hv']⟩)
    (fun h => (hM₂.vac v).2.1 (by rw [← hv]; exact hkill h))
  intro φ hφ
  rw [← key] at hφ
  exact ((hmem φ).1 hφ).2

theorem GlobalTheory.ThK.IsoUniq.main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₂ : Model σ X₁ W₁)
    (H : Plane E n n₁) (H' : Plane E d d₁) (i₀ i₁ j₀ j₁ : ℕ), B.IsGood σ → (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') →
    M.IsGood B.ψ → M₂.IsGood B.ψ → H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ e e₂ : Fn F n d →ₗ[ℂ] Fn F n₁ d₁, IsEv B M M₂ H.ι H'.ι (isoA H H') e → IsEv B M M₂ H.ι H'.ι (isoA H H') e₂ →
      ∃ c : ℂ, ∀ Ψ ∈ schA F (Fin n × Fin d), e₂ Ψ = c • e Ψ := by
  intro hKP F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₂ H H' i₀ i₁ j₀ j₁ hB hXW hM hM₂ hH hH' e e₂ he he₂
  obtain ⟨ei, ev, hei, hev, hloc⟩ := he.loc
  obtain ⟨ei', ev', hei', hev', hloc'⟩ := he₂.loc
  have hfin : ∀ v, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev' v φ = ev v φ := fun v φ hφ =>
    GlobalTheory.ThK.IsoUniq.finRel_unique hKP F E σ B n d n₁ d₁ X W X₁ W₁ M M₂ H H' i₀ i₁ j₀ j₁ hB hXW hM hM₂ hH hH' v (ev v) (ev' v)
      (GlobalTheory.ThK.IsoUniq.finRel_of_ev hM hM₂ e he ei ev hei hev hloc v)
      (GlobalTheory.ThK.IsoUniq.finRel_of_ev hM hM₂ e₂ he₂ ei' ev' hei' hev' hloc' v)
      (hev v).2 (hev' v).2 (hev v).1 (hev' v).1 φ hφ
  obtain ⟨c, hc⟩ := GlobalTheory.T.good_models_adapted_planes_pair hKP F E σ B n d n₁ d₁ X W X₁ W₁ M M₂ H H' i₀ i₁ j₀ j₁ hB hXW hM hM₂ hH hH' ei ei' hei
    (GlobalTheory.ThK.IsoUniq.infRel_of_ev hM hM₂ e he ei ev hev hloc)
    (GlobalTheory.ThK.IsoUniq.infRel_of_ev hM hM₂ e₂ he₂ ei' ev' hev' hloc')
  refine ⟨c, fun Ψ hΨ => ?_⟩
  obtain ⟨T, m, f, φ, hφ, hT, rfl⟩ := GlobalTheory.SchADecomp.exists_sum_pure F (Fin n × Fin d) Ψ hΨ
  rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hv : ∀ᶠ v in cofinite, φ i v = M.vac v := by
    filter_upwards [hM.std, (Set.Finite.compl_mem_cofinite T.finite_toSet : (↑T : Set (Pl F))ᶜ ∈ cofinite)] with v h1 h2
    rw [h1, hT i v h2]
  rw [hloc' (f i) (φ i) (hφ i) hv, hloc (f i) (φ i) (hφ i) hv, hc]
  have hfe : (fun v => ev' v (φ i v)) = fun v => ev v (φ i v) := funext fun v => hfin v _ (hφ i v)
  rw [hfe]
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, mul_assoc]
