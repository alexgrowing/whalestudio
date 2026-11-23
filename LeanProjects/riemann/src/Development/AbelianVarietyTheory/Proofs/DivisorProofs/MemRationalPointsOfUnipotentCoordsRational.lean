import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemUnitaryRationalPointsOfFrameImagesRationalStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem mem_ratPts_of_crd_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (u : GAd σ J) (b₀ : Matrix (Fin j) (Fin m) E) (c₀ : Matrix (Fin j) (Fin j) E), Crd σ J C D Z J₀ u (adMat F b₀) (adMat F c₀) → u ∈ ratPts σ J := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF u b₀ c₀ h
  have hmul : ∀ {a b c : ℕ} (X : Matrix (Fin a) (Fin b) E) (Y : Matrix (Fin b) (Fin c) E),
      adMat F (X * Y) = adMat F X * adMat F Y := fun X Y => by
    unfold adMat
    exact Matrix.map_mul (f := (inclR (F := F) (AF F) : E →+* _))
  have hadd : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) E),
      adMat F (X + Y) = adMat F X + adMat F Y := fun X Y => by
    ext i k; simp [adMat]
  have hsub : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) E),
      adMat F (X - Y) = adMat F X - adMat F Y := fun X Y => by
    ext i k; simp [adMat]
  refine GlobalTheory.T.mem_unitaryRationalPoints_of_frameImages_rational F E σ n J j m C D Z J₀ hF u C
    (D - Z * (J₀⁻¹ * cT (σ : E →+* E) b₀) + C * c₀) (Z + C * b₀) h.onC ?_ ?_
  · rw [h.onZ, hadd, hmul]
  · rw [h.onD, hadd, hsub, hmul, hmul, hmul]
    rfl

end GlobalTheory.SphEis
