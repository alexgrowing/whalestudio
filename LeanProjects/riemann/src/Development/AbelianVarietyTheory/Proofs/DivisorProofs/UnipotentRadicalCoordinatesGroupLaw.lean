import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFrameCols
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem crdLaw_cT_mul {A : Type} [CommRing A] (s : A →+* A) {a b c : Type} [Fintype b] (M : Matrix a b A) (N : Matrix b c A) :
    cT s (M * N) = cT s N * cT s M := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem crdLaw_cT_add {A : Type} [CommRing A] (s : A →+* A) {a b : Type} (M N : Matrix a b A) :
    cT s (M + N) = cT s M + cT s N := by
  simp [cT, Matrix.map_add, Matrix.transpose_add]

theorem crdLaw_cT_one {A : Type} [CommRing A] (s : A →+* A) {a : Type} [DecidableEq a] :
    cT s (1 : Matrix a a A) = 1 := by
  simp [cT]

theorem crdLaw_plus_add {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {j m : ℕ} (J₀ : Matrix (Fin m) (Fin m) E) (b b' : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) :
    plus σ J₀ (b + b') = plus σ J₀ b + plus σ J₀ b' := by
  simp only [plus, crdLaw_cT_add, Matrix.mul_add]

theorem crdLaw_plus_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {j m : ℕ} (J₀ : Matrix (Fin m) (Fin m) E) (a : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) :
    plus σ J₀ (a * b) = plus σ J₀ b * cT (sigR (AF F) σ) a := by
  simp only [plus, crdLaw_cT_mul, Matrix.mul_assoc]

theorem crd_law : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ (u u' : GAd σ J) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) (b' : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c' : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), Crd σ J C D Z J₀ u b c → (Crd σ J C D Z J₀ u' b' c' → Crd σ J C D Z J₀ (u * u') (b + b') (c + c' - b * plus σ J₀ b')) ∧ (Crd σ J C D Z J₀ u' b c → u = u') ∧ ∀ α, Crd σ J C D Z J₀ (lv α * u * (lv α)⁻¹) (α.1 * b) (α.1 * c * cT (sigR (AF F) σ) α.1) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hL u u' b c b' c' h
  refine ⟨fun h' => ?_, fun h' => ?_, fun α => ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [map_mul, Units.val_mul, Matrix.mul_assoc, h'.onC, h.onC]
    · rw [map_mul, Units.val_mul, Matrix.mul_assoc, h'.onZ, Matrix.mul_add, h.onZ, ← Matrix.mul_assoc, h.onC,
        Matrix.mul_add, add_assoc]
    · have eZ : (matHom _ σ J u).1 * (adMat F Z * plus σ J₀ b') = (adMat F Z + adMat F C * b) * plus σ J₀ b' := by
        rw [← Matrix.mul_assoc, h.onZ]
      have eC : (matHom _ σ J u).1 * (adMat F C * c') = adMat F C * c' := by
        rw [← Matrix.mul_assoc, h.onC]
      rw [map_mul, Units.val_mul, Matrix.mul_assoc, h'.onD, Matrix.mul_add, Matrix.mul_sub, h.onD, eZ, eC,
        crdLaw_plus_add]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_assoc]
      abel
  · exact eq_of_frame_cols F E σ n J j m C D Z J₀ hF u u' (h.onC.trans h'.onC.symm) (h.onZ.trans h'.onZ.symm)
      (h.onD.trans h'.onD.symm)
  · have hinv : (lv α)⁻¹ = lv α⁻¹ := (map_inv lv α).symm
    have iC : (matHom _ σ J (lv α⁻¹)).1 * adMat F C = adMat F C * (α⁻¹).1 := hL.onC α⁻¹
    have iZ : (matHom _ σ J (lv α⁻¹)).1 * adMat F Z = adMat F Z := hL.onZ α⁻¹
    have iD : (matHom _ σ J (lv α⁻¹)).1 * adMat F D = adMat F D * cT (sigR (AF F) σ) α.1 := by
      rw [hL.onD α⁻¹, inv_inv]
    have one : cT (sigR (AF F) σ) (α⁻¹).1 * cT (sigR (AF F) σ) α.1 = 1 := by
      rw [← crdLaw_cT_mul, Units.mul_inv, crdLaw_cT_one]
    have aC : (matHom _ σ J (lv α)).1 * (adMat F C * b) = adMat F C * (α.1 * b) := by
      rw [← Matrix.mul_assoc, hL.onC, Matrix.mul_assoc]
    rw [hinv]
    refine ⟨?_, ?_, ?_⟩
    · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, iC, ← Matrix.mul_assoc,
        Matrix.mul_assoc _ _ (adMat F C), h.onC, hL.onC, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, iZ, Matrix.mul_assoc, h.onZ,
        Matrix.mul_add, hL.onZ, aC]
    · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, iD, Matrix.mul_assoc,
        ← Matrix.mul_assoc _ (adMat F D), h.onD, crdLaw_plus_mul]
      have eZ : (matHom _ σ J (lv α)).1 * (adMat F Z * plus σ J₀ b) = adMat F Z * plus σ J₀ b := by
        rw [← Matrix.mul_assoc, hL.onZ]
      have eC : (matHom _ σ J (lv α)).1 * (adMat F C * c) = adMat F C * (α.1 * c) := by
        rw [← Matrix.mul_assoc, hL.onC, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_sub, hL.onD, eZ, eC]
      simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, one, Matrix.mul_one]

end GlobalTheory.SphEis
