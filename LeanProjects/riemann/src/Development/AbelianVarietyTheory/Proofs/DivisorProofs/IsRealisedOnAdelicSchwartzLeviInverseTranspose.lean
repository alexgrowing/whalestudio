import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN
open scoped Matrix

namespace GlobalTheory.AdelicSvNLevi

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]

def qI (F : Type) [Field F] [NumberField F] : F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    ((RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp (algebraMap F (AdeleRing (𝓞 F) F)))

def qF (F : Type) [Field F] [NumberField F] : F →+* FiniteAdeleRing (𝓞 F) F :=
  (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp (algebraMap F (AdeleRing (𝓞 F) F))

def compM (P : Matrix κ κ F) : ((κ → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ((κ → AdeleRing (𝓞 F) F) → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun x => P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x)

theorem compM_apply (P : Matrix κ κ F) (φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (x : κ → AdeleRing (𝓞 F) F) :
    compM P φ x = φ (P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x) := rfl

def archEquiv (P Q : Matrix κ κ F) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) where
  toFun y := P.map (qI F) *ᵥ y
  invFun y := Q.map (qI F) *ᵥ y
  map_add' y y' := Matrix.mulVec_add _ _ _
  map_smul' r y := by rw [RingHom.id_apply, Matrix.mulVec_smul]
  left_inv y := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  right_inv y := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

def finHomeo (P Q : Matrix κ κ F) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    (κ → FiniteAdeleRing (𝓞 F) F) ≃ₜ (κ → FiniteAdeleRing (𝓞 F) F) where
  toFun z := P.map (qF F) *ᵥ z
  invFun z := Q.map (qF F) *ᵥ z
  left_inv z := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  right_inv z := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

theorem comp_pureA (P Q : Matrix κ κ F) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    compM P (pureA F f g) =
      pureA F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archEquiv P Q hPQ hQP) f) (g ∘ finHomeo P Q hPQ hQP) := by
  funext x
  let q : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F :=
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  let p : AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
  have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x) i).1) =
      P.map (qI F) *ᵥ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) := by
    funext i
    change q ((P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x) i) = _
    rw [RingHom.map_mulVec, Matrix.map_map]
    rfl
  have h2 : (fun i => ((P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x) i).2) =
      P.map (qF F) *ᵥ (fun i => (x i).2) := by
    funext i
    change p ((P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x) i) = _
    rw [RingHom.map_mulVec, Matrix.map_map]
    rfl
  simp only [compM_apply, pureA, Function.comp_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  rw [h1, h2]
  rfl

theorem comp_mem (P Q : Matrix κ κ F) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    ∀ φ ∈ schA F κ, compM P φ ∈ schA F κ := by
  have hle : schA F κ ≤ (schA F κ).comap (compM P) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, g, hg, rfl⟩
    refine Submodule.subset_span ⟨_, _, ⟨hg.1.comp_continuous (finHomeo P Q hPQ hQP).continuous,
      hg.2.comp_homeomorph (finHomeo P Q hPQ hQP)⟩, comp_pureA P Q hPQ hQP f g⟩
  exact fun φ hφ => hle hφ

theorem act_levi {K R ι : Type} [Field K] [CommRing R] [Algebra K R] [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι K)
    (w : (ι → R) × (ι → R)) :
    AdelicSvN.act (Matrix.fromBlocks A 0 0 B) w = (A.map (algebraMap K R) *ᵥ w.1, B.map (algebraMap K R) *ᵥ w.2) := by
  have h0 : (0 : Matrix ι ι K).map (algebraMap K R) = 0 := Matrix.map_zero _ (map_zero _)
  simp only [AdelicSvN.act, Matrix.fromBlocks_map, h0, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Matrix.zero_mulVec, add_zero, zero_add]

theorem dot_transpose {R ι : Type} [CommRing R] [Fintype ι] (M : Matrix ι ι R) (x v : ι → R) :
    x ⬝ᵥ (Mᵀ *ᵥ v) = (M *ᵥ x) ⬝ᵥ v := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem realised_levi : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (κ : Type) [Fintype κ]
    [DecidableEq κ] (A : Matrix κ κ F), IsUnit A.det → Realised ψ (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ) := by
  intro F _ _ ψ κ _ _ A hA
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  let Am : Matrix κ κ (AdeleRing (𝓞 F) F) := A.map (algebraMap F (AdeleRing (𝓞 F) F))
  let Aim : Matrix κ κ (AdeleRing (𝓞 F) F) := A⁻¹.map (algebraMap F (AdeleRing (𝓞 F) F))
  have e1 : Am * Aim = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : Aim * Am = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨compM A⁻¹, comp_mem A⁻¹ A h2 h1, fun φ hφ => ⟨compM A φ, comp_mem A A⁻¹ h1 h2 φ hφ, ?_⟩,
    fun l hl => ⟨l ∘ₗ compM A⁻¹, fun g hg => ?_, fun _ _ => rfl⟩, fun w φ _ => funext fun x => ?_⟩
  · funext x
    change φ (Am *ᵥ (Aim *ᵥ x)) = φ x
    rw [Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]
  · obtain ⟨T, hT⟩ := hl _ ⟨hg.1.comp_continuous (finHomeo A⁻¹ A h2 h1).continuous,
      hg.2.comp_homeomorph (finHomeo A⁻¹ A h2 h1)⟩
    refine ⟨T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archEquiv A⁻¹ A h2 h1)), fun f => ?_⟩
    rw [LinearMap.comp_apply, comp_pureA A⁻¹ A h2 h1, hT]
    rfl
  · rw [act_levi, Matrix.transpose_map]
    change ψ ((Aim *ᵥ x) ⬝ᵥ w.2 + ⅟(2 : AdeleRing (𝓞 F) F) * (w.1 ⬝ᵥ w.2)) * φ (Aim *ᵥ x + w.1) =
      ψ (x ⬝ᵥ (Aimᵀ *ᵥ w.2) + ⅟(2 : AdeleRing (𝓞 F) F) * ((Am *ᵥ w.1) ⬝ᵥ (Aimᵀ *ᵥ w.2))) *
        φ (Aim *ᵥ (x + Am *ᵥ w.1))
    rw [dot_transpose, dot_transpose, Matrix.mulVec_add, Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]

end GlobalTheory.AdelicSvNLevi

end
