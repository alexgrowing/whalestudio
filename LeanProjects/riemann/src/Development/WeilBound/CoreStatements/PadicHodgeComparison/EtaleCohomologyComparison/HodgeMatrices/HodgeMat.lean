import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.HTSpecAllHodge

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions.Loc GlobalTheory.HTLink

namespace CrystallineSemistableComparison.Jump

theorem corr_mat {R m m' c c' I : Type*} [CommRing R] [Fintype m] [Fintype m'] [Fintype c] [Fintype c'] [Fintype I]
    [DecidableEq m] (Φ : Matrix m c R) (Φ' : Matrix m' c' R) (Ep : Matrix m' m R) (Hp : Matrix c' c R)
    (E : I → Matrix m' m R) (H : I → Matrix c' c R) (a : I → ℤ) (np : Ep * Φ = Φ' * Hp) (nt : ∀ i, E i * Φ = Φ' * H i)
    (L : Matrix m m' R) (hL : L * Ep = 1) (T : Matrix m m R) (T' : Matrix c c R)
    (hE : Ep * T = ∑ i, a i • E i) (hH : Hp * T' = ∑ i, a i • H i) : T * Φ = Φ * T' := by
  have h : Ep * (T * Φ) = Ep * (Φ * T') := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hE, np, Matrix.mul_assoc, hH, Matrix.sum_mul, Matrix.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Matrix.smul_mul, Matrix.mul_smul, nt]
  have h2 := congrArg (L * ·) h
  simpa only [← Matrix.mul_assoc, hL, Matrix.one_mul] using h2

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {X X' : Scheme.{0}} {q : X ⟶ Sp ↥K.1} {q' : X' ⟶ Sp ↥K.1} {n : ℕ}

theorem corr_ht (F : Frame q n) (F' : Frame q' n) (Φ : Matrix (Fin F.d) F.Col ℂ_[l]) (Φ' : Matrix (Fin F'.d) F'.Col ℂ_[l])
    {p : X' ⟶ X} (hp : p ≫ q = q') {I : Type} [Fintype I] {t : I → (X' ⟶ X)} (ht : ∀ i, t i ≫ q = q') (a : I → ℤ)
    (np : F.etMat F' hp * Φ = Φ' * F.hodgeMat F' hp) (nt : ∀ i, F.etMat F' (ht i) * Φ = Φ' * F.hodgeMat F' (ht i))
    (hinj : Function.Injective (etPull hp n)) (TV : EtV q n →ₗ[ℚ_[l]] EtV q n)
    (TH : ∀ j : Fin (n + 1), HodgeV q n j →ₗ[↥K.1] HodgeV q n j)
    (hV : etPull hp n ∘ₗ TV = ∑ i, a i • etPull (ht i) n)
    (hH : ∀ j : Fin (n + 1), GlobalTheory.HodgeCoh.hodgePull hp j (n - j) ∘ₗ TH j = ∑ i, a i • GlobalTheory.HodgeCoh.hodgePull (ht i) j (n - j)) :
    (LinearMap.toMatrix F.b F.b TV).map (algebraMap ℚ_[l] ℂ_[l]) * Φ =
      Φ * (Matrix.blockDiagonal' fun j : Fin (n + 1) => LinearMap.toMatrix (F.c j) (F.c j) (TH j)).map (toC K) := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (etPull hp n) (LinearMap.ker_eq_bot.2 hinj)
  refine corr_mat Φ Φ' _ _ (fun i => F.etMat F' (ht i)) (fun i => F.hodgeMat F' (ht i)) a np nt
    ((LinearMap.toMatrix F'.b F.b g).map (algebraMap ℚ_[l] ℂ_[l])) ?_ _ _ ?_ ?_
  · rw [Frame.etMat, ← Matrix.map_mul, ← LinearMap.toMatrix_comp, hg, LinearMap.toMatrix_id,
      Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [Frame.etMat, ← Matrix.map_mul, ← LinearMap.toMatrix_comp, hV]
    ext i j
    simp [Frame.etMat, Matrix.sum_apply, map_sum]
  · rw [Frame.hodgeMat, ← Matrix.map_mul, ← Matrix.blockDiagonal'_mul]
    simp only [← LinearMap.toMatrix_comp, hH]
    ext ⟨i, x⟩ ⟨j, y⟩
    by_cases hij : i = j
    · subst hij
      simp [Frame.hodgeMat, Matrix.sum_apply, map_sum]
    · rw [Matrix.map_apply, Matrix.blockDiagonal'_apply_ne _ _ _ hij, map_zero, Matrix.sum_apply]
      refine (Finset.sum_eq_zero fun k _ => ?_).symm
      rw [Matrix.smul_apply, Frame.hodgeMat, Matrix.map_apply, Matrix.blockDiagonal'_apply_ne _ _ _ hij, map_zero, smul_zero]

end CrystallineSemistableComparison.Jump

end
