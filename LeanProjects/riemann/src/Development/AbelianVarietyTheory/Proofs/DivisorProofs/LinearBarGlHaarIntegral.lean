import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarModelUnitaryActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableZetaIntegralMatrixSchwartz
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL Formalism.DoubleCosetMeasures.instMeasMat

noncomputable section

namespace GlobalTheory.FibreCoinv

open GlobalTheory.SplitFlip

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_mul_eq_one_of_rank {m D : Type} [Fintype m] [DecidableEq m] [Fintype D] [DecidableEq D]
    (Y : Matrix m D k) (hY : Y.rank = Fintype.card m) : ∃ Z : Matrix D m k, Y * Z = 1 := by
  have h1 : LinearMap.range Y.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fintype_fun_eq_card]
    exact hY
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective _ h1
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at this
  have h2 : LinearMap.toMatrix' Y.mulVecLin = Y := LinearMap.toMatrix'_toLin' Y
  rwa [h2] at this

theorem comp_transpose_mul_mem_SB {m D : Type} [Fintype m] [DecidableEq m] [Fintype D] [DecidableEq D]
    {Y : Matrix m D k} {Z : Matrix D m k} (hZ : Y * Z = 1) {Ψ : Matrix m D k → ℂ}
    (hΨ : Ψ ∈ GlobalTheory.SplitWeil.SB (Matrix m D k)) :
    (fun X : Matrix m m k => Ψ (Xᵀ * Y)) ∈ GlobalTheory.SplitWeil.SB (Matrix m m k) := by
  obtain ⟨hlc, hcs⟩ := hΨ
  have hc : Continuous fun X : Matrix m m k => Xᵀ * Y :=
    Continuous.matrix_mul continuous_id.matrix_transpose continuous_const
  have hf : Continuous fun M : Matrix m D k => (M * Z)ᵀ :=
    (Continuous.matrix_mul continuous_id continuous_const).matrix_transpose
  refine ⟨hlc.comp_continuous hc, ?_⟩
  refine IsCompact.of_isClosed_subset (hcs.image hf) (isClosed_tsupport _) ?_
  have hcl : IsClosed ((fun X : Matrix m m k => Xᵀ * Y) ⁻¹' tsupport Ψ) := (isClosed_tsupport _).preimage hc
  have hsub : Function.support (fun X : Matrix m m k => Ψ (Xᵀ * Y)) ⊆ (fun X => Xᵀ * Y) ⁻¹' tsupport Ψ :=
    fun X hX => subset_tsupport Ψ hX
  refine (closure_minimal hsub hcl).trans ?_
  intro X hX
  exact ⟨Xᵀ * Y, hX, by simp [Matrix.mul_assoc, hZ]⟩

variable [MeasurableSpace k] [BorelSpace k]

theorem integrable_omB {n : ℕ} {D : Type} [Fintype D] [DecidableEq D]
    (ν α : kˣ →* ℂˣ) (hν : GlobalTheory.KSplit.IsSmU ν) (hd : (n : ℝ) - 1 < (Fintype.card D : ℝ) / 2)
    {Y : Matrix (Fin n) D k} {Z : Matrix D (Fin n) k} (hZ : Y * Z = 1) {Ψ : Matrix (Fin n) D k → ℂ}
    (hΨ : Ψ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin n) D k)) (μ : Measure (GL (Fin n) k)) [μ.IsHaarMeasure] :
    Integrable (fun g => omB ν α g 1 Ψ Y) μ := by
  have h := GlobalTheory.GJIntegrable.integrable_gjIntegrand k n ν ((Fintype.card D : ℂ) / 2) hν
    (by simpa using hd) _ (comp_transpose_mul_mem_SB hZ hΨ)
  rw [Measure.isMulLeftInvariant_eq_smul μ (haarVol (GlobalTheory.SplitWeil.KO k (Fin n)))]
  refine h.smul_measure_nnreal.congr (Eventually.of_forall fun g => ?_)
  simp only [omB, gdet, map_one, Units.val_one, apow_one, Matrix.mul_one]
  ring

theorem omB_sub_apply {n : ℕ} {D : Type} [Fintype D] [DecidableEq D] (ν α : kˣ →* ℂˣ) (h : GL (Fin n) k)
    (Ψ Ψ' : Matrix (Fin n) D k → ℂ) (Y : Matrix (Fin n) D k) :
    omB ν α h 1 (Ψ - Ψ') Y = omB ν α h 1 Ψ Y - omB ν α h 1 Ψ' Y := by
  simp only [omB, Pi.sub_apply]; ring

theorem integral_omB_translate_sub {n : ℕ} {D : Type} [Fintype D] [DecidableEq D]
    (ν α : kˣ →* ℂˣ) (hν : GlobalTheory.KSplit.IsSmU ν) (hd : (n : ℝ) - 1 < (Fintype.card D : ℝ) / 2)
    {Y : Matrix (Fin n) D k} {Z : Matrix D (Fin n) k} (hZ : Y * Z = 1) {Ψ : Matrix (Fin n) D k → ℂ}
    (hΨ : Ψ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin n) D k)) (μ : Measure (GL (Fin n) k)) [μ.IsHaarMeasure]
    (g₀ : GL (Fin n) k) :
    ∫ h, omB ν α h 1 (omB ν α g₀ 1 Ψ - Ψ) Y ∂μ = 0 := by
  have e : ∀ h : GL (Fin n) k, omB ν α h 1 (omB ν α g₀ 1 Ψ - Ψ) Y =
      omB ν α (h * g₀) 1 Ψ Y - omB ν α h 1 Ψ Y := fun h => by
    rw [omB_sub_apply]
    have := omB_mul ν α h g₀ (1 : GL D k) 1 Ψ
    rw [one_mul] at this
    rw [this]
  simp_rw [e]
  have hi := integrable_omB ν α hν hd hZ hΨ μ
  rw [integral_sub (hi.comp_mul_right g₀) hi, integral_mul_right_eq_self (fun h => omB ν α h 1 Ψ Y) g₀, sub_self]

end Local

open GlobalTheory.SplitFlip in

theorem integral_omB_augAt_eq_zero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ ι, G.M'.IsLinBar B.ψ B.τ₁ 1 1 ι →
    ∀ [MeasurableSpace (GL (Fin a') (Fv F B.v₁))] [BorelSpace (GL (Fin a') (Fv F B.v₁))] (μ : Measure (GL (Fin a') (Fv F B.v₁))) [μ.IsHaarMeasure],
    ∀ x ∈ augAt om' B.v₁, ∀ Y : Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁), Y.rank = a' →
      ∫ g, GlobalTheory.SplitFlip.omB (chrW (X.α / X.β) B.τ₁) (chrW X.α B.τ₁) g 1 (ι x) Y ∂μ = 0 := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' hT ι hι mG hBG μ _ x hx Y hY
  letI : MeasurableSpace (Fv F B.v₁) := borel _
  haveI : BorelSpace (Fv F B.v₁) := ⟨rfl⟩
  have e : mG = Units.instMeasurableSpace :=
    hBG.measurable_eq.trans (borel_GL (k := Fv F B.v₁) (n := Fin a')).measurable_eq.symm
  subst e
  have hP := GlobalTheory.ThK.Inhab.pairV' hT
  have hν : GlobalTheory.KSplit.IsSmU (chrW (X.α / X.β) B.τ₁) := (GlobalTheory.ChrWLocal.chrW_local F E _ hP.hW B.v₁ B.τ₁).1
  have hd : (a' : ℝ) - 1 < (Fintype.card (Fin (a + a')) : ℝ) / 2 := by
    have h1 : (a' : ℝ) + 1 ≤ a := by exact_mod_cast hT.geo.lt
    simp only [Fintype.card_fin, Nat.cast_add]
    linarith
  obtain ⟨Z, hZ⟩ := exists_mul_eq_one_of_rank Y (by simpa using hY)
  have hW1 : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F B.v₁) := fun u _ => by simp [mat]
  have key : x ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁) ∧
      ∫ g, omB (chrW (X.α / X.β) B.τ₁) (chrW X.α B.τ₁) g 1 (ι x) Y ∂μ = 0 := by
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩ := hz
      refine ⟨sub_mem hφ₁ hφ, ?_⟩
      have h1 := GlobalTheory.T.linear_bar_model_unitary_action hK.base F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hP B.v₁ B.τ₁ 1 1 ι hι
        g hg 1 hW1 φ hφ φ₁ hφ₁ hA
      rw [map_one] at h1
      rw [map_sub, h1]
      exact integral_omB_translate_sub _ _ hν hd hZ (hι.bij.mapsTo hφ) μ _
    | zero =>
      refine ⟨zero_mem _, ?_⟩
      simp [omB]
    | add y z _ _ hy hz =>
      refine ⟨add_mem hy.1 hz.1, ?_⟩
      have e2 : ∀ g : GL (Fin a') (Fv F B.v₁), omB (chrW (X.α / X.β) B.τ₁) (chrW X.α B.τ₁) g 1 (ι (y + z)) Y =
          omB (chrW (X.α / X.β) B.τ₁) (chrW X.α B.τ₁) g 1 (ι y) Y + omB (chrW (X.α / X.β) B.τ₁) (chrW X.α B.τ₁) g 1 (ι z) Y :=
        fun g => by simp only [map_add, omB, Pi.add_apply]; ring
      simp_rw [e2]
      rw [integral_add (integrable_omB _ _ hν hd hZ (hι.bij.mapsTo hy.1) μ)
        (integrable_omB _ _ hν hd hZ (hι.bij.mapsTo hz.1) μ), hy.2, hz.2, add_zero]
    | smul c y _ hy =>
      refine ⟨Submodule.smul_mem _ c hy.1, ?_⟩
      have e2 : ∀ g : GL (Fin a') (Fv F B.v₁), omB (chrW (X.α / X.β) B.τ₁) (chrW X.α B.τ₁) g 1 (ι (c • y)) Y =
          c * omB (chrW (X.α / X.β) B.τ₁) (chrW X.α B.τ₁) g 1 (ι y) Y :=
        fun g => by simp only [map_smul, omB, Pi.smul_apply, smul_eq_mul]; ring
      simp_rw [e2]
      rw [integral_const_mul, hy.2, mul_zero]
  exact key.2

end GlobalTheory.FibreCoinv
