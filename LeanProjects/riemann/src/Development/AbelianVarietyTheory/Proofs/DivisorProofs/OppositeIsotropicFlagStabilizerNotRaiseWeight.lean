import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact

namespace GlobalTheory.UAut.OppFlagWeight

theorem weight_of_triangular {A : Type} [CommRing A] {n r : ℕ} {X Y : Matrix (Fin n) (Fin r) A}
    {L T : Matrix (Fin r) (Fin n) A} {x : Matrix (Fin n) (Fin n) A} {B B' : Matrix (Fin r) (Fin r) A}
    {d : Fin r → ℕ} {M : ℕ} (hd : ∀ j, d j < M)
    (hLX : L * X = 1) (hTY : T * Y = 1) (hLY : L * Y = 0)
    (hB : x * Y = Y * B) (hB' : L * x = B' * L) (tB : ∀ i j, d j < d i → B i j = 0) (tB' : ∀ i j, d i < d j → B' i j = 0)
    (ε : Option (Fin r ⊕ Fin r) → Matrix (Fin n) (Fin n) A)
    (e0 : ε none = 1 - (X * L + Y * T)) (e1 : ∀ j, ε (some (.inl j)) = X * single j j (1 : A) * L)
    (e2 : ∀ j, ε (some (.inr j)) = Y * single j j (1 : A) * T) :
    ∀ a b, wt d M b < wt d M a → ε a * x * ε b = 0 := by
  have k0 : ε none * Y = 0 := by
    rw [e0, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hLY, hTY]; simp
  have k1 : L * ε none = 0 := by
    rw [e0, Matrix.mul_sub, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hLY, hLX]; simp
  have k2 : ∀ (m : Matrix (Fin n) (Fin n) A) j, m * Y = 0 → m * x * ε (some (.inr j)) = 0 := fun m j h => by
    rw [e2, Matrix.mul_assoc Y, ← Matrix.mul_assoc, Matrix.mul_assoc m, hB, ← Matrix.mul_assoc m, h]; simp
  rintro (_ | i | i) (_ | j | j) hab
  · simp [wt] at hab
  · have := hd j; simp [wt] at hab; omega
  · exact k2 _ j k0
  · rw [e1, Matrix.mul_assoc _ L, hB', ← Matrix.mul_assoc, Matrix.mul_assoc _ L, k1, Matrix.mul_zero]
  · rw [e1, e1, sandwich_eq_zero hLX, hB', Matrix.mul_assoc, hLX, Matrix.mul_one]
    exact tB' i j (by simp [wt] at hab; omega)
  · exact k2 _ j (by rw [e1, Matrix.mul_assoc, hLY, Matrix.mul_zero])
  · have := hd i; simp [wt] at hab; omega
  · have := hd i; have := hd j; simp [wt] at hab; omega
  · rw [e2, e2, sandwich_eq_zero hTY, Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hTY, Matrix.one_mul]
    exact tB i j (by simp [wt] at hab; omega)

theorem not_raise_of_mem_parFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) (M : ℕ), (∀ j, d j < M) → Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → ∀ p ∈ parFlag σ J Y d, ∀ a b, wt d M b < wt d M a → fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * (matHom (AF F) σ J p).1 * fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0 := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y d M hd _ hY hXY p hp
  obtain ⟨⟨B, hB, eB⟩, B', hB', eB'⟩ := hp
  have cc : ∀ {m p : Type} (A : Matrix m p E), Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) A) = A := fun A =>
    Matrix.ext fun i j => sigma_sigma h _
  have hYX : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (Formalism.UG.cT (σ : E →+* E)) hXY
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, cT_form hJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  have f := form_mul_of_mul_cols eB'
  rw [inv_inv] at f
  set φ := inclR (F := F) (E := E) (AF F) with hφ
  have adj : ∀ Z : Matrix (Fin r) (Fin r) E, adjA σ J ((X * Z * (Formalism.UG.cT (σ : E →+* E) Y * J)).map φ) =
      Y.map φ * (Formalism.UG.cT (σ : E →+* E) Z).map φ * (Formalism.UG.cT (σ : E →+* E) X * J).map φ := fun Z => by
    rw [adjA_map, ← Matrix.map_mul, ← Matrix.map_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, cT_form hJ]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc J⁻¹, Matrix.nonsing_inv_mul _ (det_isUnit hJ), Matrix.one_mul]
  refine weight_of_triangular (X := X.map φ) (Y := Y.map φ) (L := (Formalism.UG.cT (σ : E →+* E) Y * J).map φ)
    (T := (Formalism.UG.cT (σ : E →+* E) X * J).map φ) hd ?_ ?_ ?_ eB f (fun i j hij => hB hij) (fun i j hij => ?_) _ ?_
    (fun j => idemA_eq _ _ j) (fun j => ?_)
  · rw [← Matrix.map_mul, hYX, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, hXY, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, hY, Matrix.map_zero _ (map_zero _)]
  · show sigR (AF F) σ (B' j i) = 0
    rw [hB' hij, map_zero]
  · have := adj 1
    rw [Matrix.mul_one, Formalism.UG.cT_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this
    simp only [fam, Option.elim, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [← map_sum, sum_idemA, this, Matrix.map_mul]
  · refine (adj (single j j 1)).trans ?_
    congr 2
    ext a b
    by_cases h1 : j = a <;> by_cases h2 : j = b <;> simp [Formalism.UG.cT, single, h1, h2]

end GlobalTheory.UAut.OppFlagWeight
