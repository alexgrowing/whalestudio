import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.ThetaLifts.Reductions.SiegelPar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumFrameIdem

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RapidDecay

theorem single_mul_mul_single_eq_zero {R : Type} [CommRing R] {r : ℕ} {B : Matrix (Fin r) (Fin r) R}
    {m i : Fin r} (h : B m i = 0) :
    (single m m (1 : R) : Matrix (Fin r) (Fin r) R) * B * single i i (1 : R) = 0 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
  rcases eq_or_ne m a with rfl | ha <;> rcases eq_or_ne i b with rfl | hb <;>
    simp [*, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem map_single_one_eq {E : Type} [Field E] {r : ℕ} (f : E →+* ℂ) (i : Fin r) :
    (single i i (1 : E) : Matrix (Fin r) (Fin r) E).map f = single i i (1 : ℂ) := by
  ext a b
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem mul_mul_frameLine {n r : ℕ} {A G : Matrix (Fin n) (Fin n) ℂ} {P : Matrix (Fin n) (Fin r) ℂ}
    {B : Matrix (Fin r) (Fin r) ℂ} (hG : G * P = P * B) (Q : Matrix (Fin r) (Fin n) ℂ) (i : Fin r)
    (h : A * P * B * single i i (1 : ℂ) = 0) :
    A * G * (P * single i i (1 : ℂ) * Q) = 0 := by
  calc A * G * (P * single i i (1 : ℂ) * Q) = A * (G * P) * single i i (1 : ℂ) * Q := by
        simp only [Matrix.mul_assoc]
    _ = A * P * B * single i i (1 : ℂ) * Q := by
        rw [hG]; simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h, Matrix.zero_mul]

theorem minPar_frame_block_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ g ∈ minPar σ J X, ∀ (w : InfinitePlace F) (τ : EmbOver E w) (s : Fin r) (α β : FrameIx r), frameLev s α < 2 → frameLev s β = 2 → (frameIdem (σ : E →+* E) J X Y α).map τ.1 * archMat σ J τ (projArch σ J w g) * (frameIdem (σ : E →+* E) J X Y β).map τ.1 = 0 := by
  intro F E _ _ _ _ _ σ hCM n J hJ r X Y hW g hg w τ s α β hα hβ
  obtain ⟨-, -, -, hστ⟩ := hCM
  have hσσ : ∀ x, σ (σ x) = x := fun x => τ.1.injective (by rw [hστ, hστ, star_star])
  have cT_mul : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (B : Matrix (Fin b) (Fin c) E),
      cT (σ : E →+* E) (A * B) = cT (σ : E →+* E) B * cT (σ : E →+* E) A := by
    intro a b c A B
    simp [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have cT_cT : ∀ {a b : ℕ} (A : Matrix (Fin a) (Fin b) E), cT (σ : E →+* E) (cT (σ : E →+* E) A) = A := by
    intro a b A
    ext i j
    simp [Formalism.UG.cT, hσσ]
  have cT_J : cT (σ : E →+* E) J = J := by
    ext i j
    simpa [Formalism.UG.cT] using hJ.1 i j
  have cT_one : cT (σ : E →+* E) (1 : Matrix (Fin r) (Fin r) E) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [Formalism.UG.cT]
    · simp [Formalism.UG.cT, Matrix.one_apply, hij, Ne.symm hij]
  have hyx : cT (σ : E →+* E) Y * (J * X) = 1 := by
    have h := congrArg (cT (σ : E →+* E)) hW.xy
    rw [cT_mul, cT_mul, cT_cT, cT_J, cT_one] at h
    exact h
  have hxx : cT (σ : E →+* E) X * (J * X) = 0 := by
    rw [← Matrix.mul_assoc]
    exact hW.xx
  obtain ⟨B, hBt, hB⟩ := hg
  let φ : TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) E →+* ℂ :=
    (GlobalTheory.AdelicU.infEmb τ).comp (GlobalTheory.AdelicU.compInf F E w)
  have hφ : ∀ x : E, φ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) x) = τ.1 x := by
    intro x
    simp [φ, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, GlobalTheory.AdelicU.compInf, GlobalTheory.AdelicU.infEmb]
  have hAd : (GlobalTheory.SiegelSet.adMat F X).map φ = X.map τ.1 := by
    ext i j
    simp only [GlobalTheory.SiegelSet.adMat, Matrix.map_apply]
    exact hφ (X i j)
  have hA : archMat σ J τ (projArch σ J w g) =
      ((GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J g : GL (Fin n) _) : Matrix (Fin n) (Fin n) _).map φ := by
    ext i j
    simp [GlobalTheory.Orb.archMat, GlobalTheory.AdelicU.matHom_projArch, Formalism.UG.bc, φ]
  have hG : archMat σ J τ (projArch σ J w g) * X.map τ.1 = X.map τ.1 * B.map φ := by
    rw [hA, ← hAd, ← Matrix.map_mul, hB, Matrix.map_mul]
  rcases β with _ | (i | i)
  · change 1 = 2 at hβ
    exact absurd hβ (by decide)
  · by_cases hi : i ≤ s
    · have hframe : (frameIdem (σ : E →+* E) J X Y (some (Sum.inl i))).map τ.1 =
          X.map τ.1 * single i i (1 : ℂ) * (cT (σ : E →+* E) Y * J).map τ.1 := by
        change (X * single i i (1 : E) * (cT (σ : E →+* E) Y * J)).map τ.1 = _
        simp only [Matrix.map_mul, map_single_one_eq]
      rw [hframe]
      apply mul_mul_frameLine hG
      rw [← Matrix.map_mul]
      rcases α with _ | (j | j)
      · have h0 : frameIdem (σ : E →+* E) J X Y none * X = 0 := by
          change (1 - X * (cT (σ : E →+* E) Y * J) - Y * (cT (σ : E →+* E) X * J)) * X = 0
          simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hyx, hxx,
            Matrix.mul_one, Matrix.mul_zero, sub_self, sub_zero]
        rw [h0]
        simp
      · have hj : ¬ j ≤ s := by
          intro h
          change (if j ≤ s then 2 else 1) < 2 at hα
          rw [if_pos h] at hα
          exact absurd hα (by decide)
        have hij : i < j := lt_of_le_of_lt hi (not_le.mp hj)
        have hBji : (B.map φ) j i = 0 := by
          simp [Matrix.map_apply, hBt hij]
        have h1 : frameIdem (σ : E →+* E) J X Y (some (Sum.inl j)) * X = X * single j j (1 : E) := by
          change X * single j j (1 : E) * (cT (σ : E →+* E) Y * J) * X = _
          simp only [Matrix.mul_assoc, hyx, Matrix.mul_one]
        rw [h1, Matrix.map_mul, map_single_one_eq, Matrix.mul_assoc, Matrix.mul_assoc,
          ← Matrix.mul_assoc (single j j (1 : ℂ)), single_mul_mul_single_eq_zero hBji, Matrix.mul_zero]
      · have h2 : frameIdem (σ : E →+* E) J X Y (some (Sum.inr j)) * X = 0 := by
          change Y * single j j (1 : E) * (cT (σ : E →+* E) X * J) * X = 0
          simp only [Matrix.mul_assoc, hxx, Matrix.mul_zero]
        rw [h2]
        simp
    · change (if i ≤ s then 2 else 1) = 2 at hβ
      rw [if_neg hi] at hβ
      exact absurd hβ (by decide)
  · change (if i ≤ s then 0 else 1) = 2 at hβ
    by_cases hi : i ≤ s
    · rw [if_pos hi] at hβ
      exact absurd hβ (by decide)
    · rw [if_neg hi] at hβ
      exact absurd hβ (by decide)

end GlobalTheory.CompanionTheory.RapidDecay

end
