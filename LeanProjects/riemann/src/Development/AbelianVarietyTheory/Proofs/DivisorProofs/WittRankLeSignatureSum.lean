import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.WittBoundSkew

open Matrix
open scoped ComplexOrder

theorem form_mulVec {n k : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (Q : Matrix (Fin n) (Fin k) ℂ) (x : Fin k → ℂ) :
    (Q *ᵥ x) ⬝ᵥ (M *ᵥ star (Q *ᵥ x)) = x ⬝ᵥ ((Qᵀ * M * Q.map star) *ᵥ star x) := by
  have hs : star (Q *ᵥ x) = Q.map star *ᵥ star x := by
    ext i; simp [mulVec, dotProduct, star_sum]
  rw [hs, ← vecMul_transpose, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, dotProduct_mulVec, Matrix.mul_assoc]

theorem le_of_isotropic_sig {n m s r : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hS : HasSig M m s)
    (Z : Matrix (Fin n) (Fin r) ℂ) (L : Matrix (Fin r) (Fin n) ℂ) (hL : L * Z = 1)
    (hZ : Zᵀ * M * Z.map star = 0) : r ≤ s := by
  obtain ⟨hn, A, hA⟩ := hS
  set A₁ : Matrix (Fin n) (Fin m) ℂ := A.submatrix id Sum.inl with hA₁
  have hA₁M : A₁ᵀ * M * A₁.map star = 1 := by
    ext i j
    have h := congrFun (congrFun hA (Sum.inl i)) (Sum.inl j)
    simpa [A₁, Matrix.mul_apply, transpose_apply, Matrix.one_apply] using h
  have hpos : ∀ x : Fin m → ℂ, (A₁ *ᵥ x) ⬝ᵥ (M *ᵥ star (A₁ *ᵥ x)) = 0 → x = 0 := by
    intro x hx
    rw [form_mulVec, hA₁M, one_mulVec, dotProduct_comm] at hx
    exact dotProduct_star_self_eq_zero.mp hx
  have hiso : ∀ y : Fin r → ℂ, (Z *ᵥ y) ⬝ᵥ (M *ᵥ star (Z *ᵥ y)) = 0 := by
    intro y
    rw [form_mulVec, hZ, zero_mulVec, dotProduct_zero]
  have hinj : Function.Injective (fromCols Z A₁).mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hw' : Z *ᵥ (fun i => w (Sum.inl i)) + A₁ *ᵥ (fun i => w (Sum.inr i)) = 0 := by
      rw [← hw]
      ext i
      simp [mulVec, dotProduct, Fintype.sum_sum_type, fromCols]
    have hZA : Z *ᵥ (fun i => w (Sum.inl i)) = A₁ *ᵥ (-(fun i => w (Sum.inr i))) := by
      rw [mulVec_neg]; exact eq_neg_of_add_eq_zero_left hw'
    have hx : -(fun i => w (Sum.inr i)) = 0 := hpos _ (by rw [← hZA]; exact hiso _)
    have hx' : (fun i => w (Sum.inr i)) = 0 := neg_eq_zero.mp hx
    have hy0 : Z *ᵥ (fun i => w (Sum.inl i)) = 0 := by rw [hZA, hx, mulVec_zero]
    have hy : (fun i => w (Sum.inl i)) = 0 := by
      calc (fun i => w (Sum.inl i)) = (L * Z) *ᵥ (fun i => w (Sum.inl i)) := by rw [hL, one_mulVec]
        _ = 0 := by rw [← mulVec_mulVec, hy0, mulVec_zero]
    funext i
    rcases i with i | i
    · exact congrFun hy i
    · exact congrFun hx' i
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at h
  omega

theorem wittIndex_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ c : E, c ≠ 0 → σ c = -c →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin (a + a')) (Fin r) E), IsWittFrame σ (c • G.W.J.map σ) Xf Yf → r ≤ G.p + G.q := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT c hc _ r Xf Yf hW
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  set τ : E →+* ℂ := (B.emb w).1 with hτ
  have hconj : ∀ x, τ (σ x) = star (τ x) := fun x => hT.base.cm.2.2.2 τ x
  set ρ : E →+* ℂ := (starRingEnd ℂ).comp τ with hρ
  have hρσ : ∀ x, ρ (σ x) = τ x := fun x => by simp [ρ, hconj]
  set Z : Matrix (Fin (a + a')) (Fin r) ℂ := Xf.map τ with hZ
  have hXρ : Xf.map ρ = Z.map star := by ext i j; simp [ρ, Z]
  have key : ∀ {k : ℕ} (Y : Matrix (Fin (a + a')) (Fin k) E),
      (Formalism.UG.cT (σ : E →+* E) Xf * (c • G.W.J.map σ) * Y).map ρ = Zᵀ * (ρ c • G.W.J.map τ) * Y.map ρ := by
    intro k Y
    rw [Matrix.map_mul, Matrix.map_mul]
    congr 2
    · ext i j; simp [Formalism.UG.cT, Z, hρσ]
    · ext i j; simp [hρσ]
  have hρc : ρ c ≠ 0 := (map_ne_zero ρ).mpr hc
  have hxx : Zᵀ * (Complex.I • G.W.J.map τ) * Z.map star = 0 := by
    have h := key Xf
    rw [hW.xx, Matrix.map_zero _ (map_zero _), hXρ] at h
    have h2 : ρ c • (Zᵀ * G.W.J.map τ * Z.map star) = 0 := by
      rw [h]; simp [Matrix.mul_smul, Matrix.smul_mul]
    have h3 : Zᵀ * G.W.J.map τ * Z.map star = 0 := (smul_eq_zero.mp h2).resolve_left hρc
    rw [Matrix.mul_smul, Matrix.smul_mul, h3, smul_zero]
  have hxy : Zᵀ * ((ρ c • G.W.J.map τ) * Yf.map ρ) = 1 := by
    have h := key Yf
    rw [hW.xy, Matrix.map_one _ (map_zero _) (map_one _)] at h
    rw [← Matrix.mul_assoc, ← h]
  have hL : ((ρ c • G.W.J.map τ) * Yf.map ρ)ᵀ * Z = 1 := by
    have h := congrArg Matrix.transpose hxy
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h
  exact le_of_isotropic_sig _ (hT.geo.hW.sig w) Z _ hL hxx

end GlobalTheory.WittBoundSkew
