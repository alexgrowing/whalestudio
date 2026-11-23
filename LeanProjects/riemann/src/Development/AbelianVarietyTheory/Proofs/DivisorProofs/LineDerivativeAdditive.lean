import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HasSmoothLogNearOneOfIsUnitaryLieExpDataStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothInExponentialCoordsIffFirstSecondKindStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeAlongLieSmoothAndLinearStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeAlongLieCommutatorEqBracketStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

open Matrix GlobalTheory.SmoothForms
open GlobalTheory.Orb (archMat)

attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.LeviHC.LineLie

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {w : InfinitePlace F}

section Chart

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

def sigA (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun X := A⁻¹ * Xᴴ * A
  map_add' X Y := by rw [conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    change A⁻¹ * (c • X)ᴴ * A = c • (A⁻¹ * Xᴴ * A)
    rw [conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.smul_mul]

abbrev LieL (A : Matrix (Fin n) (Fin n) ℂ) : Type := ↥(GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU A).toSubmodule

def jA (A : Matrix (Fin n) (Fin n) ℂ) : LieL A →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ := (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU A).toSubmodule.subtype

variable (σ J) in
open Classical in

def secA (τ : EmbOver E w) (u : Matrix (Fin n) (Fin n) ℂ) : GAd σ J :=
  if hu : ∃ y : GArch σ J w, archMat σ J τ y = u then embArch σ J w hu.choose else 1

theorem archMat_injective (h : IsCMExt F E σ) (τ : EmbOver E w) : Function.Injective (archMat σ J τ) := fun a b e => by
  rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, GlobalTheory.Orb.archMat_eq_archEquiv J h] at e
  exact (archEquiv J h τ).injective (Subtype.ext (Units.ext e))

theorem secA_archMat (h : IsCMExt F E σ) (τ : EmbOver E w) (y : GArch σ J w) :
    secA σ J τ (archMat σ J τ y) = embArch σ J w y := by
  have hu : ∃ y' : GArch σ J w, archMat σ J τ y' = archMat σ J τ y := ⟨y, rfl⟩
  rw [secA, dif_pos hu, archMat_injective h τ hu.choose_spec]

theorem exists_archMat (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) {u : Matrix (Fin n) (Fin n) ℂ}
    (hu : sigA (J.map τ.1) u * u = 1) : ∃ y : GArch σ J w, archMat σ J τ y = u := by
  have hA := isUnit_det_map hJ τ.1
  have hu1 : (J.map τ.1)⁻¹ * uᴴ * J.map τ.1 * u = 1 := hu
  have hu2 : uᴴ * J.map τ.1 * u = J.map τ.1 := by
    have := congrArg (J.map τ.1 * ·) hu1
    simpa only [← Matrix.mul_assoc, mul_nonsing_inv _ hA, Matrix.one_mul, Matrix.mul_one] using this
  let v : GL (Fin n) ℂ := ⟨u, (J.map τ.1)⁻¹ * uᴴ * J.map τ.1, mul_eq_one_comm.1 hu1, hu1⟩
  refine ⟨(archEquiv J h τ).symm ⟨v, show _ * _ * _ = _ from hu2⟩, ?_⟩
  rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, MulEquiv.apply_symm_apply]

theorem isLieData (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) :
    IsLieData (sigA (J.map τ.1)) (jA (J.map τ.1)) (secA σ J τ) := by
  have hA := isUnit_det_map hJ τ.1
  have hAh := conjTranspose_map h hJ τ.1
  have anti : ∀ a b, sigA (J.map τ.1) (a * b) = sigA (J.map τ.1) b * sigA (J.map τ.1) a := fun a b => by
    change _ * (a * b)ᴴ * _ = (_ * bᴴ * _) * (_ * aᴴ * _)
    rw [conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ hA]
  refine ⟨anti, ?_, fun a => ?_, Subtype.val_injective, fun X => ⟨fun hX => ?_, ?_⟩, fun a b ha hb => ?_⟩
  · change (J.map τ.1)⁻¹ * (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * J.map τ.1 = 1
    rw [conjTranspose_one, Matrix.mul_one, nonsing_inv_mul _ hA]
  · change _ * (_ * aᴴ * _)ᴴ * _ = a
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hAh]
    simp only [Matrix.mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ hA, nonsing_inv_mul _ hA, Matrix.mul_one]
  · refine ⟨⟨X, ?_⟩, rfl⟩
    have h1 : (J.map τ.1)⁻¹ * Xᴴ * J.map τ.1 = -X := hX
    change Xᴴ * J.map τ.1 + J.map τ.1 * X = 0
    rw [← mul_nonsing_inv_cancel_left _ (Xᴴ * J.map τ.1) hA, ← Matrix.mul_assoc (J.map τ.1)⁻¹, h1, Matrix.mul_neg,
      neg_add_cancel]
  · rintro ⟨Y, rfl⟩
    have h1 : Y.1ᴴ * J.map τ.1 + J.map τ.1 * Y.1 = 0 := Y.2
    change _ * Y.1ᴴ * _ = -Y.1
    rw [Matrix.mul_assoc, eq_neg_of_add_eq_zero_left h1, Matrix.mul_neg, nonsing_inv_mul_cancel_left _ _ hA]
  · have hab : sigA (J.map τ.1) (a * b) * (a * b) = 1 := by
      rw [anti, Matrix.mul_assoc, ← Matrix.mul_assoc (sigA (J.map τ.1) a), ha, Matrix.one_mul, hb]
    obtain ⟨ya, rfl⟩ := exists_archMat h hJ τ ha
    obtain ⟨yb, rfl⟩ := exists_archMat h hJ τ hb
    rw [← map_mul, secA_archMat h, secA_archMat h, secA_archMat h, map_mul]

theorem hasLog (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) :
    HasLog (sigA (J.map τ.1)) (jA (J.map τ.1)) :=
  GlobalTheory.T.hasSmoothLogNearOne_of_isUnitaryLieExpData _ _ _ _ _ _ (isLieData h hJ τ)

theorem isLineOf_expMap (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) (Y : LieL (J.map τ.1)) :
    IsLineOf σ J τ Y.1 fun t => expMap (jA (J.map τ.1)) (secA σ J τ) (t • Y) := fun t => by
  have hA := isUnit_det_map hJ τ.1
  have hY : (t • Y.1)ᴴ * J.map τ.1 + J.map τ.1 * (t • Y.1) = 0 := by
    have h1 : Y.1ᴴ * J.map τ.1 + J.map τ.1 * Y.1 = 0 := Y.2
    rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]
  have h1 : (NormedSpace.exp (t • Y.1))ᴴ * J.map τ.1 * NormedSpace.exp (t • Y.1) = J.map τ.1 :=
    GlobalTheory.SmoothForms.exp_mem_UH hA hY
  have hu : sigA (J.map τ.1) (NormedSpace.exp (t • Y.1)) * NormedSpace.exp (t • Y.1) = 1 := by
    change (J.map τ.1)⁻¹ * _ * J.map τ.1 * _ = 1
    rw [Matrix.mul_assoc _ _ (J.map τ.1), Matrix.mul_assoc, h1, nonsing_inv_mul _ hA]
  obtain ⟨y, hy⟩ := exists_archMat h hJ τ hu
  refine ⟨y, ?_, hy⟩
  change secA σ J τ (NormedSpace.exp (t • Y.1)) = _
  rw [← hy, secA_archMat h]

theorem sm_of_isSm (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) {f : GAd σ J → ℂ} (hf : IsSm σ J f) :
    Sm (expMap (jA (J.map τ.1)) (secA σ J τ)) f := by
  rw [GlobalTheory.T.smoothInExponentialCoords_iff_first_second_kind _ _ _ _ _ _ (isLieData h hJ τ) (hasLog h hJ τ) Set.univ Submodule.span_univ]
  intro k Y _ g
  exact hf k (fun i t => expMap (jA (J.map τ.1)) (secA σ J τ) (t • Y i))
    (fun i => (isLineOf_expMap h hJ τ (Y i)).isRealLine h) g

theorem lineDer_add_bracket : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) (f : GAd σ J → ℂ), IsSm σ J f →
    ∀ (X X' : Matrix (Fin n) (Fin n) ℂ) (γ δ ε : ℝ → GAd σ J), IsLineOf σ J τ X γ → IsLineOf σ J τ X' δ →
      (IsLineOf σ J τ (X + X') ε → lineDer ε f = lineDer γ f + lineDer δ f) ∧
      (IsLineOf σ J τ (X * X' - X' * X) ε → lineDer ε f = lineDer γ (lineDer δ f) - lineDer δ (lineDer γ f)) := by
  intro F E _ _ _ _ _ σ h n J hJ w τ f hf X X' γ δ ε hγ hδ
  have H := isLieData h hJ τ
  have hl := hasLog h hJ τ
  have hs := sm_of_isSm h hJ τ hf
  have hX := hγ.skew h
  have hX' := hδ.skew h
  let Y : LieL (J.map τ.1) := ⟨X, hX⟩
  let Y' : LieL (J.map τ.1) := ⟨X', hX'⟩
  obtain rfl : γ = _ := hγ.unique h (isLineOf_expMap h hJ τ Y)
  obtain rfl : δ = _ := hδ.unique h (isLineOf_expMap h hJ τ Y')
  refine ⟨fun hε => ?_, fun hε => ?_⟩
  · obtain rfl : ε = _ := hε.unique h (isLineOf_expMap h hJ τ (Y + Y'))
    exact (GlobalTheory.T.rightDerivativeAlongLie_smooth_and_linear _ _ _ _ _ _ H hl f hs).2.1 Y Y'
  · have hZ := hε.skew h
    let Z : LieL (J.map τ.1) := ⟨X * X' - X' * X, hZ⟩
    obtain rfl : ε = _ := hε.unique h (isLineOf_expMap h hJ τ Z)
    exact (GlobalTheory.T.rightDerivativeAlongLie_commutator_eq_bracket _ _ _ _ _ _ H hl f hs Y Y' Z rfl).symm

end Chart

end GlobalTheory.LeviHC.LineLie

end
