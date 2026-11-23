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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicSubspaceInvariantSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSkewLocalPlaceDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSkewLocalPlaceCompatibleStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.ThK.EvUniqB

theorem finRel_unique : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (T T' : ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
    GlobalTheory.ThK.EvUniqB.FinRel B G.M' G₁.M' H.ι H'.ι (isoB H H') v T → GlobalTheory.ThK.EvUniqB.FinRel B G.M' G₁.M' H.ι H'.ι (isoB H H') v T' →
    (SB _).map T = SB _ → (SB _).map T' = SB _ → T (G.M'.vac v) = G₁.M'.vac v → T' (G.M'.vac v) = G₁.M'.vac v →
    ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v), T' φ = T φ := by
  intro _ F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hTr hTr₁ v T T' hT hT' hTs hT's hv hv'
  have hB := hTr.base
  have hM := hTr.geo.hM'
  have hM₁ := hTr₁.geo.hM'
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F _).injective
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt B.ψ hB.std.1 v
  have hψ1 : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hB.std v
  have hsb : ∀ {κ : Type} [Fintype κ] (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ SB (κ → Fv F v),
      schr (GlobalTheory.LatVac.psiAt B.ψ v) w φ ∈ SB (κ → Fv F v) := fun w φ hφ =>
    GlobalTheory.SchrSB.schr_mem_SB B.ψ hB.std.1 v w φ hφ
  have hAtι : ∀ z : Matrix (Fin b) (Fin (a + b)) (AE F E), At (evFin F v) z →
      At (evFin F v) (incM F H.ι * z * (incM F H'.ι)ᵀ) := by
    intro z hz c hc
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hz c hc, Matrix.mul_zero, Matrix.zero_mul]
  have loc : ∀ T : ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ,
      GlobalTheory.ThK.EvUniqB.FinRel B G.M' G₁.M' H.ι H'.ι (isoB H H') v T → (SB _).map T = SB _ →
      (∀ z, At (evFin F v) z → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        T (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (incM F H.ι * z * (incM F H'.ι)ᵀ)) φ) =
          schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G₁.M'.co v z) (T φ)) ∧
      (∀ u ∈ isoB (F := F) H H', At (evFin F v) u → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        T (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v u) φ) = T φ) := by
    intro T hT hTs
    refine ⟨fun z hz φ hφ => ?_, fun u hu hat φ hφ => ?_⟩
    · have hTφ : T φ ∈ SB (Fin b × Fin (a + b) → Fv F v) := hTs ▸ Submodule.mem_map_of_mem hφ
      exact hT.1 z hz φ hφ _ (hsb _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v _ (hAtι z hz) φ) _
        (hsb _ _ hTφ) (GlobalTheory.VacBridge.rho_acts_locCo G₁.M'.co B.ψ v z hz (T φ))
    · exact hT.2 u hu hat φ hφ _ (hsb _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v u hat φ)
  obtain ⟨l1, l2⟩ := loc T hT hTs
  obtain ⟨l1', l2'⟩ := loc T' hT' hT's
  have hiso := fun u hu hat u' hu' hat' => GlobalTheory.T.hermitian_skew_local_place_data F E σ B (b + 2) b (a + (b + 2)) (a + b) _ _ _ _ a (a + b + 1) 0 (b + 1)
    G.V' G₁.V' G.W G₁.W H H' G.M' hB hTr.geo.hV' hTr.geo.hW hC.hH hC.hH' v u hu hat u' hu' hat'
  have hperp := GlobalTheory.T.hermitian_skew_local_place_compatible F E σ B (b + 2) b (a + (b + 2)) (a + b) _ _ _ _ a (a + b + 1) 0 (b + 1)
    G.V' G₁.V' G.W G₁.W H H' G.M' hB hTr.geo.hV' hTr.geo.hW hC.hH hC.hH' v
  have m1 : ∀ z, Matrix.vecMulVec (incV F H.x) z ∈ isoB (F := F) H H' := fun z => Or.inl ⟨z, rfl⟩
  have m2 : ∀ y, Matrix.vecMulVec (incM F H.ι *ᵥ y) (incV F H'.x) ∈ isoB (F := F) H H' := fun y => Or.inr ⟨y, rfl⟩
  have at0 : At (evFin F v) (0 : Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (AE F E)) := fun c _ => smul_zero c
  have vz : ∀ x : Fin (b + 2) → AE F E, Matrix.vecMulVec x (0 : Fin (a + (b + 2)) → AE F E) = 0 := fun x => by
    ext i j; simp [Matrix.vecMulVec_apply]
  have atAdd : ∀ {A B' : Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (AE F E)}, At (evFin F v) A → At (evFin F v) B' →
      At (evFin F v) (A + B') := fun hA hB' c hc => by rw [smul_add, hA c hc, hB' c hc, add_zero]
  let U : Submodule (Fv F v) ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) × (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v)) :=
    { carrier := {w | ∃ z y, At (evFin F v) (Matrix.vecMulVec (incV F H.x) z) ∧
          At (evFin F v) (Matrix.vecMulVec (incM F H.ι *ᵥ y) (incV F H'.x)) ∧
          w = GlobalTheory.LatVac.locCo G.M'.co v (Matrix.vecMulVec (incV F H.x) z) +
            GlobalTheory.LatVac.locCo G.M'.co v (Matrix.vecMulVec (incM F H.ι *ᵥ y) (incV F H'.x))}
      add_mem' := by
        rintro _ _ ⟨z, y, hz, hy, rfl⟩ ⟨z', y', hz', hy', rfl⟩
        refine ⟨z + z', y + y', ?_, ?_, ?_⟩
        · rw [Matrix.vecMulVec_add]; exact atAdd hz hz'
        · rw [Matrix.mulVec_add, Matrix.add_vecMulVec]; exact atAdd hy hy'
        · rw [Matrix.vecMulVec_add, Matrix.mulVec_add, Matrix.add_vecMulVec, map_add, map_add]; abel
      zero_mem' := ⟨0, 0, by simpa [vz] using at0,
        by simpa [vz] using at0, by simp [vz]⟩
      smul_mem' := by
        rintro c _ ⟨z, y, hz, hy, rfl⟩
        refine ⟨GlobalTheory.LatVac.liftV v c • z, GlobalTheory.LatVac.liftV v c • y, ?_, ?_, ?_⟩
        · rw [Matrix.vecMulVec_smul]; intro e he; rw [smul_comm, hz e he, smul_zero]
        · rw [Matrix.mulVec_smul, Matrix.smul_vecMulVec]; intro e he; rw [smul_comm, hy e he, smul_zero]
        · rw [Matrix.vecMulVec_smul, Matrix.mulVec_smul, Matrix.smul_vecMulVec, smul_add,
            GlobalTheory.LatOpenCpt.locCo_smul, GlobalTheory.LatOpenCpt.locCo_smul, GlobalTheory.LatVac.evFin_liftV] }
  have hne : ∀ x, GlobalTheory.LatVac.psiAt B.ψ v x ≠ 0 := fun x h => by
    have := AddChar.map_add_eq_mul (GlobalTheory.LatVac.psiAt B.ψ v) x (-x)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
    exact one_ne_zero this
  have e' : ∀ (a' b' : (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) × (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v)) φ,
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
  have hU : ∀ T : ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ,
      (∀ u ∈ isoB (F := F) H H', At (evFin F v) u → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        T (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v u) φ) = T φ) →
      ∀ w ∈ U, ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        T (schr (GlobalTheory.LatVac.psiAt B.ψ v) w φ) = T φ := by
    rintro T h2 _ ⟨z, y, hz, hy, rfl⟩ φ hφ
    rw [e', hiso _ (m1 z) hz _ (m2 y) hy, mul_zero, AddChar.map_zero_eq_one, inv_one, one_smul,
      h2 _ (m1 z) hz _ (hsb _ φ hφ), h2 _ (m2 y) hy φ hφ]
  let S : Submodule ℂ ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) := SB _ ⊓ LinearMap.ker (T' - T)
  have hmem : ∀ φ, φ ∈ S ↔ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) ∧ T' φ = T φ := by
    intro φ
    simp [S, sub_eq_zero]
  have hkill : Submodule.span ℂ {f | ∃ u ∈ U, ∃ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
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
      have hw' : ∀ u ∈ isoB (F := F) H H', At (evFin F v) u →
          (GlobalTheory.LatVac.locCo G.M'.co v u).1 ⬝ᵥ w.2 - w.1 ⬝ᵥ (GlobalTheory.LatVac.locCo G.M'.co v u).2 = 0 := by
        rintro u (⟨z, rfl⟩ | ⟨y, rfl⟩) hat
        · refine hw _ ⟨z, 0, hat, ?_, ?_⟩
          · simpa [vz] using at0
          · simp [vz]
        · refine hw _ ⟨0, y, ?_, hat, ?_⟩
          · simpa [vz] using at0
          · simp [vz]
      obtain ⟨z₀, hz₀, y₀, hy₀, z, hz, rfl⟩ := hperp w hw'
      have hu : GlobalTheory.LatVac.locCo G.M'.co v (Matrix.vecMulVec (incV F H.x) z₀) +
          GlobalTheory.LatVac.locCo G.M'.co v (Matrix.vecMulVec (incM F H.ι *ᵥ y₀) (incV F H'.x)) ∈ U :=
        ⟨z₀, y₀, hz₀, hy₀, rfl⟩
      refine ⟨hsb _ φ hφ.1, ?_⟩
      rw [e', map_smul, map_smul, hU T l2 _ hu _ (hsb _ φ hφ.1), hU T' l2' _ hu _ (hsb _ φ hφ.1),
        l1 z hz φ hφ.1, l1' z hz φ hφ.1, hφ.2])
    (G.M'.vac v) ((hmem _).2 ⟨(hM.vac v).1, by rw [hv, hv']⟩)
    (fun h => (hM₁.vac v).2.1 (by rw [← hv]; exact hkill h))
  intro φ hφ
  rw [← key] at hφ
  exact ((hmem φ).1 hφ).2

end GlobalTheory.ThK.EvUniqB
