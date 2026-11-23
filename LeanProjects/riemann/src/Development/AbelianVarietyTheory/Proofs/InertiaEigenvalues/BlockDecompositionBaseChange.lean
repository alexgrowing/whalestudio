import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff

namespace GlobalTheory

open Matrix in

theorem blockDecomposition_baseChange {K L : Type} [Field K] [Field L] (φ : K →+* L) {n r t : ℕ}
    (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K))) :
    ∃ e' : (Fin n → L) ≃ₗ[L] ((Fin r → L) × (Fin t → L)),
      ∀ (M : Matrix (Fin n) (Fin n) K) (P : Matrix (Fin r) (Fin r) K) (d : Fin t → K),
        (∀ u, e (M.mulVec u) = (P.mulVec (e u).1, fun c => d c * (e u).2 c)) →
        ∀ u, e' ((M.map φ).mulVec u) =
          ((P.map φ).mulVec (e' u).1, fun c => φ (d c) * (e' u).2 c) := by
  classical

  have hext : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) K), (∀ v, X *ᵥ v = Y *ᵥ v) → X = Y :=
    fun X Y h => Matrix.toLin'.injective (LinearMap.ext fun v => by
      simpa only [Matrix.toLin'_apply] using h v)

  obtain ⟨A₁, hA₁⟩ : ∃ A : Matrix (Fin r) (Fin n) K, ∀ v, A *ᵥ v = (e v).1 :=
    ⟨LinearMap.toMatrix' (LinearMap.fst K _ _ ∘ₗ e.toLinearMap), fun v => by
      rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl⟩
  obtain ⟨A₂, hA₂⟩ : ∃ A : Matrix (Fin t) (Fin n) K, ∀ v, A *ᵥ v = (e v).2 :=
    ⟨LinearMap.toMatrix' (LinearMap.snd K _ _ ∘ₗ e.toLinearMap), fun v => by
      rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl⟩
  obtain ⟨B₁, hB₁⟩ : ∃ B : Matrix (Fin n) (Fin r) K, ∀ p, B *ᵥ p = e.symm (p, 0) :=
    ⟨LinearMap.toMatrix' (e.symm.toLinearMap ∘ₗ LinearMap.inl K _ _), fun p => by
      rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl⟩
  obtain ⟨B₂, hB₂⟩ : ∃ B : Matrix (Fin n) (Fin t) K, ∀ q, B *ᵥ q = e.symm (0, q) :=
    ⟨LinearMap.toMatrix' (e.symm.toLinearMap ∘ₗ LinearMap.inr K _ _), fun q => by
      rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl⟩

  have h11 : A₁ * B₁ = 1 := hext _ _ fun p => by
    rw [← Matrix.mulVec_mulVec, hB₁, hA₁, LinearEquiv.apply_symm_apply, Matrix.one_mulVec]
  have h12 : A₁ * B₂ = 0 := hext _ _ fun q => by
    rw [← Matrix.mulVec_mulVec, hB₂, hA₁, LinearEquiv.apply_symm_apply, Matrix.zero_mulVec]
  have h21 : A₂ * B₁ = 0 := hext _ _ fun p => by
    rw [← Matrix.mulVec_mulVec, hB₁, hA₂, LinearEquiv.apply_symm_apply, Matrix.zero_mulVec]
  have h22 : A₂ * B₂ = 1 := hext _ _ fun q => by
    rw [← Matrix.mulVec_mulVec, hB₂, hA₂, LinearEquiv.apply_symm_apply, Matrix.one_mulVec]
  have hBA : B₁ * A₁ + B₂ * A₂ = 1 := hext _ _ fun u => by
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA₁, hA₂, hB₁, hB₂,
      ← map_add, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta, LinearEquiv.symm_apply_apply,
      Matrix.one_mulVec]

  have h11' : A₁.map φ * B₁.map φ = 1 := by
    rw [← Matrix.map_mul, h11, Matrix.map_one _ φ.map_zero φ.map_one]
  have h12' : A₁.map φ * B₂.map φ = 0 := by
    rw [← Matrix.map_mul, h12, Matrix.map_zero _ φ.map_zero]
  have h21' : A₂.map φ * B₁.map φ = 0 := by
    rw [← Matrix.map_mul, h21, Matrix.map_zero _ φ.map_zero]
  have h22' : A₂.map φ * B₂.map φ = 1 := by
    rw [← Matrix.map_mul, h22, Matrix.map_one _ φ.map_zero φ.map_one]
  have hBA' : B₁.map φ * A₁.map φ + B₂.map φ * A₂.map φ = 1 := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ φ.map_add, hBA,
      Matrix.map_one _ φ.map_zero φ.map_one]

  refine ⟨LinearEquiv.ofLinearMap ((Matrix.toLin' (A₁.map φ)).prod (Matrix.toLin' (A₂.map φ)))
    ((Matrix.toLin' (B₁.map φ)).coprod (Matrix.toLin' (B₂.map φ))) ?_ ?_, ?_⟩
  · refine LinearMap.ext fun x => ?_
    obtain ⟨p, q⟩ := x
    refine Prod.ext ?_ ?_ <;>
      simp [Matrix.mulVec_add, Matrix.mulVec_mulVec, h11', h12', h21', h22']
  · refine LinearMap.ext fun u => ?_
    have key : (B₁.map φ * A₁.map φ) *ᵥ u + (B₂.map φ * A₂.map φ) *ᵥ u = u := by
      rw [← Matrix.add_mulVec, hBA', Matrix.one_mulVec]
    simpa [Matrix.mulVec_mulVec] using key
  · intro M P d h u

    have hM₁ : A₁ * M = P * A₁ := hext _ _ fun v => by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA₁, hA₁, h v]
    have hM₂ : A₂ * M = Matrix.diagonal d * A₂ := hext _ _ fun v => by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA₂, hA₂, h v]
      funext c
      rw [Matrix.mulVec_diagonal]
    have hM₁' : A₁.map φ * M.map φ = P.map φ * A₁.map φ := by
      rw [← Matrix.map_mul, hM₁, Matrix.map_mul]
    have hM₂' : A₂.map φ * M.map φ = Matrix.diagonal (fun c => φ (d c)) * A₂.map φ := by
      rw [← Matrix.map_mul, hM₂, Matrix.map_mul, Matrix.diagonal_map φ.map_zero]
    refine Prod.ext ?_ (funext fun c => ?_)
    · change A₁.map φ *ᵥ (M.map φ *ᵥ u) = P.map φ *ᵥ (A₁.map φ *ᵥ u)
      rw [Matrix.mulVec_mulVec, hM₁', ← Matrix.mulVec_mulVec]
    · change (A₂.map φ *ᵥ (M.map φ *ᵥ u)) c = φ (d c) * (A₂.map φ *ᵥ u) c
      rw [Matrix.mulVec_mulVec, hM₂', ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]

end GlobalTheory
