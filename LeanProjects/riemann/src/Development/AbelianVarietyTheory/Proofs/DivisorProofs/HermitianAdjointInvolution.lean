import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Idem3

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipHaar

noncomputable section

namespace GlobalTheory.UnipHaar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_mul' {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) : incM F (A * B) = incM F A * incM F B := by
  simp only [incM]; exact Matrix.map_mul

theorem incM_one' {n : ℕ} : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  simp only [incM]; exact Matrix.map_one _ (map_zero _) (map_one _)

theorem incM_neg' {n : ℕ} (A : Matrix (Fin n) (Fin n) E) : incM F (-A) = -incM F A := by
  ext i j; simp [incM]

theorem incM_transpose' {n : ℕ} (A : Matrix (Fin n) (Fin n) E) : incM F Aᵀ = (incM F A)ᵀ := by
  simp only [incM]; exact (Matrix.transpose_map).symm

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem cA_cA (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (a : AE F E) : cA σ (cA σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cA, hσ]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem incM_map_cA (σ : E →ₐ[F] E) {n : ℕ} (A : Matrix (Fin n) (Fin n) E) :
    (incM F A).map (cA σ) = incM F (A.map σ) := by
  ext i j; simp [incM, cA_inclR]

theorem continuous_cA (σ : E →ₐ[F] E) : Continuous (cA σ) := by
  haveI := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  exact IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap

end GlobalTheory.UnipHaar

namespace GlobalTheory.UnipHaar

theorem adj_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ x, σ (σ x) = x) → (∀ i j, σ (J j i) = -J i j) → J.det ≠ 0 → Continuous (adj σ J) ∧ (∀ X Y, adj σ J (X * Y) = adj σ J Y * adj σ J X) ∧ (∀ X, adj σ J (adj σ J X) = X) ∧ (∀ X ∈ ((inclR (F := F) (E := E) (AF F)).mapMatrix (m := Fin n)).range, adj σ J X ∈ ((inclR (F := F) (E := E) (AF F)).mapMatrix (m := Fin n)).range) ∧ ∀ X, adj σ J X * X = 1 ↔ Xᵀ * incM F J * X.map (cA σ) = incM F J := by
  intro F E _ _ _ _ _ σ n J hσ hskew hdet
  haveI := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  set K := J.map σ with hKdef
  have hK : K = -Jᵀ := by ext i j; simp [K, hskew j i]
  have hKdet : K.det ≠ 0 := by
    rw [hK, Matrix.det_neg, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hdet
  have hKu : IsUnit K.det := isUnit_iff_ne_zero.mpr hKdet
  have hKK : K⁻¹ * K = 1 := Matrix.nonsing_inv_mul K hKu
  have hKK' : K * K⁻¹ = 1 := Matrix.mul_nonsing_inv K hKu
  have hKσ : K.map σ = J := by ext i j; simp [K, hσ]
  have hCinv : (incM F K)⁻¹ = incM F K⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [← incM_mul', hKK, incM_one']
  have hCC : incM F K⁻¹ * incM F K = 1 := by rw [← incM_mul', hKK, incM_one']
  have hCC' : incM F K * incM F K⁻¹ = 1 := by rw [← incM_mul', hKK', incM_one']
  have hadj : ∀ X, adj σ J X = incM F K⁻¹ * (X.map (cA σ))ᵀ * incM F K := fun X => by
    show (incM F K)⁻¹ * _ * _ = _
    rw [hCinv]
  set cR : AE F E →+* AE F E := (cA σ).toRingHom
  have hc : ⇑(cA σ) = ⇑cR := rfl
  have hcc : ∀ X : Matrix (Fin n) (Fin n) (AE F E), (X.map (cA σ)).map (cA σ) = X := fun X => by
    ext i j; simp [cA_cA σ hσ]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : ⇑(adj σ J) = fun X => incM F K⁻¹ * (X.map (cA σ))ᵀ * incM F K := funext hadj
    rw [this]
    exact (continuous_const.matrix_mul
      (continuous_id.matrix_map (continuous_cA σ)).matrix_transpose).matrix_mul continuous_const
  · intro X Y
    rw [hadj, hadj, hadj, hc, Matrix.map_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incM F K) (incM F K⁻¹), hCC', Matrix.one_mul]
  · intro X
    set L := K⁻¹.map σ with hLdef
    have hs : ⇑σ = ⇑(σ.toRingHom) := rfl
    have hLJ : L * J = 1 := by
      rw [← hKσ, hLdef, hs, ← Matrix.map_mul, hKK, Matrix.map_one _ (map_zero _) (map_one _)]
    have hJt : Jᵀ = -K := by rw [hK, neg_neg]
    have hKL : (-Lᵀ) * K = 1 := by
      rw [mul_eq_one_comm]
      have : Jᵀ * Lᵀ = 1 := by rw [← Matrix.transpose_mul, hLJ, Matrix.transpose_one]
      rw [hJt] at this
      rw [Matrix.mul_neg, ← Matrix.neg_mul, this]
    have h1 : incM F K⁻¹ * incM F Jᵀ = -1 := by
      rw [← incM_mul', hJt, Matrix.mul_neg, hKK, incM_neg', incM_one']
    have h2 : incM F Lᵀ * incM F K = -1 := by
      rw [← incM_mul', ← neg_neg (Lᵀ * K), ← Matrix.neg_mul, hKL, incM_neg', incM_one']
    rw [hadj (adj σ J X), hadj X, hc, Matrix.map_mul, Matrix.map_mul, ← hc, incM_map_cA, incM_map_cA, hKσ,
      Matrix.transpose_map, hcc, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      ← incM_transpose', ← incM_transpose']
    rw [← hLdef, show ∀ A B C D : Matrix (Fin n) (Fin n) (AE F E), A * (B * (X * C)) * D = (A * B) * X * (C * D)
      from fun A B C D => by simp only [Matrix.mul_assoc], h1, h2]
    simp
  · rintro X ⟨A, rfl⟩
    refine ⟨K⁻¹ * (A.map σ)ᵀ * K, ?_⟩
    rw [hadj]
    show incM F _ = _
    rw [RingHom.mapMatrix_apply]
    change _ = incM F K⁻¹ * ((incM F A).map (cA σ))ᵀ * incM F K
    rw [incM_map_cA, incM_mul', incM_mul', incM_transpose']
  · intro X
    have e1 : adj σ J X * X = incM F K⁻¹ * ((X.map (cA σ))ᵀ * incM F K * X) := by
      rw [hadj]; simp only [Matrix.mul_assoc]
    have e2 : incM F K⁻¹ * ((X.map (cA σ))ᵀ * incM F K * X) = 1 ↔ (X.map (cA σ))ᵀ * incM F K * X = incM F K := by
      constructor
      · intro h
        calc (X.map (cA σ))ᵀ * incM F K * X
            = incM F K * (incM F K⁻¹ * ((X.map (cA σ))ᵀ * incM F K * X)) := by
              rw [← Matrix.mul_assoc, hCC', Matrix.one_mul]
          _ = incM F K := by rw [h, Matrix.mul_one]
      · intro h; rw [h, hCC]
    have e3 : ((X.map (cA σ))ᵀ * incM F K * X).map (cA σ) = Xᵀ * incM F J * X.map (cA σ) := by
      rw [hc, Matrix.map_mul, Matrix.map_mul, ← hc, Matrix.transpose_map, hcc, incM_map_cA, hKσ]
    have e4 : (incM F K).map (cA σ) = incM F J := by rw [incM_map_cA, hKσ]
    rw [e1, e2, ← e3, ← e4]
    constructor
    · intro h; rw [h]
    · intro h
      have := congrArg (fun M : Matrix (Fin n) (Fin n) (AE F E) => M.map (cA σ)) h
      simpa only [hcc] using this

end GlobalTheory.UnipHaar

end
