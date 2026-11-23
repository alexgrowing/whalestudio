import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.ThK.EvAt0.PolD GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open Classical

noncomputable section

namespace GlobalTheory.PlaneDec

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem span3 {σ : E →ₐ[F] E} {B : Base F E} {n n₁ i₀ i₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁}
    {H : Plane E n n₁} (hL : X.L.IsLattice E) (hH : H.IsAdapted σ B X X₁ i₀ i₁) (v : Fin n → E) :
    ∃ (s t : E) (u : Fin n₁ → E), v = s • H.x + H.ι *ᵥ u + t • H.y := by
  have hv : v ∈ Submodule.span E (X.L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨s, t, u, -, -, -, hz⟩ := hH.split z hz
    exact ⟨s, t, u, hz⟩
  | zero => exact ⟨0, 0, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨s, t, u, rfl⟩ := hy
    obtain ⟨s', t', u', rfl⟩ := hz
    exact ⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add]; module⟩
  | smul a y _ hy =>
    obtain ⟨s, t, u, rfl⟩ := hy
    exact ⟨a * s, a * t, a • u, by rw [Matrix.mulVec_smul]; module⟩

theorem one_eq {σ : E →ₐ[F] E} {B : Base F E} {n n₁ i₀ i₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁}
    {H : Plane E n n₁} (hL : X.L.IsLattice E) (hH : H.IsAdapted σ B X X₁ i₀ i₁) :
    ∃ (a b : Fin n → E) (C : Matrix (Fin n₁) (Fin n) E),
      (1 : Matrix (Fin n) (Fin n) E) = Matrix.vecMulVec H.x a + H.ι * C + Matrix.vecMulVec H.y b := by
  choose s t U hU using fun j : Fin n => span3 hL hH (Pi.single j 1)
  refine ⟨s, t, Matrix.of fun k j => U j k, ?_⟩
  ext i j
  have := congrFun (hU j) i
  rw [Matrix.one_apply, show (if i = j then (1 : E) else 0) = (Pi.single j (1 : E) : Fin n → E) i by
    simp [Pi.single_apply], this]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, mul_comm]

theorem one_eq_A {σ : E →ₐ[F] E} {B : Base F E} {n n₁ i₀ i₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁}
    {H : Plane E n n₁} (hL : X.L.IsLattice E) (hH : H.IsAdapted σ B X X₁ i₀ i₁) :
    ∃ (a b : Fin n → AE F E) (C : Matrix (Fin n₁) (Fin n) (AE F E)),
      (1 : Matrix (Fin n) (Fin n) (AE F E)) =
        Matrix.vecMulVec (incV F H.x) a + incM F H.ι * C + Matrix.vecMulVec (incV F H.y) b := by
  obtain ⟨a, b, C, h⟩ := one_eq hL hH
  refine ⟨incV F a, incV F b, incM F C, ?_⟩
  have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) E => M.map (inclR (F := F) (E := E) (AF F))) h
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _),
    Matrix.map_mul] at h2
  rw [h2]
  congr 2
  · ext i j; simp [incV, Matrix.vecMulVec_apply]
  · ext i j; simp [incV, Matrix.vecMulVec_apply]

theorem point_dec : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁)
    (r s r' s' i₀ i₁ j₀ j₁ : ℕ), X.IsHerm σ B r s → W.IsSkew σ B r' s' → H.IsAdapted σ B X X₁ i₀ i₁ → H'.IsAdapted σ B W W₁ j₀ j₁ →
    ∀ u : Matrix (Fin n) (Fin d) (AE F E), ∃ (y y' : Fin n → AE F E) (z z' : Fin d₁ → AE F E) (x : Matrix (Fin n₁) (Fin d₁) (AE F E)),
      u = Matrix.vecMulVec y (incV F H'.x) + Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z) + incM F H.ι * x * (incM F H'.ι)ᵀ +
        (Matrix.vecMulVec y' (incV F H'.y) + Matrix.vecMulVec (incV F H.y) (incM F H'.ι *ᵥ z')) := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' r s r' s' i₀ i₁ j₀ j₁ hX hW hH hH' u
  obtain ⟨a, b, C, hC⟩ := one_eq_A (F := F) hX.lat hH
  obtain ⟨a', b', C', hC'⟩ := one_eq_A (F := F) hW.lat hH'
  have hT : (1 : Matrix (Fin d) (Fin d) (AE F E)) =
      Matrix.vecMulVec a' (incV F H'.x) + C'ᵀ * (incM F H'.ι)ᵀ + Matrix.vecMulVec b' (incV F H'.y) := by
    rw [← Matrix.transpose_one, hC', Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_vecMulVec, Matrix.transpose_vecMulVec]
  set M := u * C'ᵀ with hM
  have hMd : M = Matrix.vecMulVec (incV F H.x) (a ᵥ* M) + incM F H.ι * (C * M) + Matrix.vecMulVec (incV F H.y) (b ᵥ* M) := by
    conv_lhs => rw [← Matrix.one_mul M, hC]
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, Matrix.mul_assoc]
  refine ⟨u *ᵥ a', u *ᵥ b', a ᵥ* M, b ᵥ* M, C * M, ?_⟩
  have hu : u = Matrix.vecMulVec (u *ᵥ a') (incV F H'.x) + M * (incM F H'.ι)ᵀ + Matrix.vecMulVec (u *ᵥ b') (incV F H'.y) := by
    conv_lhs => rw [← Matrix.mul_one u, hT]
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, hM, Matrix.mul_assoc]
  have hm2 : M * (incM F H'.ι)ᵀ = Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ (a ᵥ* M)) +
      incM F H.ι * (C * M) * (incM F H'.ι)ᵀ + Matrix.vecMulVec (incV F H.y) (incM F H'.ι *ᵥ (b ᵥ* M)) := by
    conv_lhs => rw [hMd]
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, Matrix.vecMul_transpose,
      Matrix.vecMul_transpose]
  rw [hm2] at hu
  refine hu.trans ?_
  abel

end GlobalTheory.PlaneDec
