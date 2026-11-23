import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame

noncomputable section

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
open scoped ContDiff

namespace UpperTheory.Lit.Bur.SmoothConj

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem conj_list_prod {Q Qi : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    Q * l.prod * Qi = (l.map fun g => Q * g * Qi).prod := by
  induction l with
  | nil => simpa using h1
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ← ih]
    calc Q * (a * l.prod) * Qi = Q * a * 1 * l.prod * Qi := by
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = Q * a * Qi * (Q * l.prod * Qi) := by
          rw [← h2]; simp only [Matrix.mul_assoc]

theorem exp_conj_of_inverse {Q Qi : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1)
    (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (Q * X * Qi)) = Q * NormedSpace.exp (t • X) * Qi := by
  have hi : Qi = Q⁻¹ := (Matrix.inv_eq_right_inv h1).symm
  have hu : IsUnit Q := ⟨⟨Q, Qi, h1, h2⟩, rfl⟩
  subst hi
  rw [← Matrix.exp_conj _ _ hu, Matrix.mul_smul, Matrix.smul_mul]

theorem conj_mem_lieG_of_gram {J G Q Qi X : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1)
    (hg : Qᴴ * J * Q = G) (hX : X ∈ lieG G) : Q * X * Qi ∈ lieG J := by
  have hX' : Xᴴ * G + G * X = 0 := hX
  have hc : Qiᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  show (Q * X * Qi)ᴴ * J + J * (Q * X * Qi) = 0
  calc (Q * X * Qi)ᴴ * J + J * (Q * X * Qi)
      = Qiᴴ * Xᴴ * Qᴴ * J * 1 + 1 * J * Q * X * Qi := by
        simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]
    _ = Qiᴴ * Xᴴ * Qᴴ * J * (Q * Qi) + (Qiᴴ * Qᴴ) * J * Q * X * Qi := by rw [h1, hc]
    _ = Qiᴴ * (Xᴴ * (Qᴴ * J * Q) + (Qᴴ * J * Q) * X) * Qi := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hg, hX']; simp

theorem conj_inv_mem_lieG_of_gram {J G Q Qi Y : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1)
    (hg : Qᴴ * J * Q = G) (hY : Y ∈ lieG J) : Qi * Y * Q ∈ lieG G := by
  have hY' : Yᴴ * J + J * Y = 0 := hY
  have hc : Qiᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  show (Qi * Y * Q)ᴴ * G + G * (Qi * Y * Q) = 0
  subst hg
  calc (Qi * Y * Q)ᴴ * (Qᴴ * J * Q) + (Qᴴ * J * Q) * (Qi * Y * Q)
      = Qᴴ * Yᴴ * (Qiᴴ * Qᴴ) * J * Q + Qᴴ * J * (Q * Qi) * Y * Q := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Qᴴ * (Yᴴ * J + J * Y) * Q := by
        rw [h1, hc]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]
    _ = 0 := by rw [hY']; simp

theorem smoothVec_conj_of_subset {L L' : Set (Matrix (Fin n) (Fin n) ℂ)}
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) {Q Qi : Matrix (Fin n) (Fin n) ℂ}
    (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hL : ∀ X ∈ L', Q * X * Qi ∈ L) {v : H}
    (hv : SmoothVec L σ v) : SmoothVec L' (fun g => σ (Q * g * Qi)) v := by
  intro k Xs hX
  have h := hv k (fun i => Q * Xs i * Qi) fun i => hL _ (hX i)
  have he : ∀ t : Fin k → ℝ, Q * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * Qi =
      (List.ofFn fun i => NormedSpace.exp (t i • (Q * Xs i * Qi))).prod := by
    intro t
    rw [conj_list_prod h1 h2, List.map_ofFn]
    congr 1
    congr 1
    funext i
    exact (exp_conj_of_inverse h1 h2 (Xs i) (t i)).symm
  simpa only [he] using h

theorem smoothVec_conj_iff (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    {J G Q Qi : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1)
    (hg : Qᴴ * J * Q = G) (v : H) :
    SmoothVec (lieG G) (fun g => σ (Q * g * Qi)) v ↔ SmoothVec (lieG J) σ v := by
  constructor
  · intro h
    have h' := smoothVec_conj_of_subset (L := lieG G) (L' := lieG J)
      (fun g => σ (Q * g * Qi)) h2 h1 (fun Y hY => conj_inv_mem_lieG_of_gram h1 hg hY) h
    have he : (fun g => σ (Q * (Qi * g * Q) * Qi)) = σ := by
      funext g
      have : Q * (Qi * g * Q) * Qi = g := by
        calc Q * (Qi * g * Q) * Qi = (Q * Qi) * g * (Q * Qi) := by simp only [Matrix.mul_assoc]
          _ = g := by rw [h1]; simp
      rw [this]
    rwa [he] at h'
  · exact smoothVec_conj_of_subset σ h1 h2 fun X hX => conj_mem_lieG_of_gram h1 hg hX

end UpperTheory.Lit.Bur.SmoothConj

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.smoothVec_conjugate_unitaryGroup_iff : ∀ {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) {J G Q Qi : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hg : Qᴴ * J * Q = G) (v : H), SmoothVec (lieG G) (fun g => σ (Q * g * Qi)) v ↔ SmoothVec (lieG J) σ v := by
  first | exact @UpperTheory.Lit.Bur.SmoothConj.smoothVec_conj_iff | exact UpperTheory.Lit.Bur.SmoothConj.smoothVec_conj_iff | (intros; apply UpperTheory.Lit.Bur.SmoothConj.smoothVec_conj_iff <;> assumption)
