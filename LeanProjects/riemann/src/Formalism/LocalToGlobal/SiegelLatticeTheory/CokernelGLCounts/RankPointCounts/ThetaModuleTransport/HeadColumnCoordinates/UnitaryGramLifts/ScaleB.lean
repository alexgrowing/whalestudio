import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.LiftMemHead

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section ScaleIso

variable {R : Type} [CommRing R] {r : ℕ}

theorem isoMbeTransport_inv {Z₁ Z₂ Z₁' Z₂' : Matrix (Fin (r + 1)) (Fin (r + 1)) R}
    (e₁ : MbMod Z₁ ≃ₗ[R] MbMod Z₁') (e₂ : MbMod Z₂ ≃ₗ[R] MbMod Z₂') (s t v : R) (hs : IsUnit s) (hv : IsUnit v)
    (hb₁ : e₁ (s • bCls Z₁ + t • eCl Z₁) = bCls Z₁') (hb₂ : e₂ (s • bCls Z₂ + t • eCl Z₂) = bCls Z₂')
    (he₁ : e₁ (v • eCl Z₁) = eCl Z₁') (he₂ : e₂ (v • eCl Z₂) = eCl Z₂') (φ : MbMod Z₁' ≃ₗ[R] MbMod Z₂')
    (hφb : φ (bCls Z₁') = bCls Z₂') (hφe : φ (eCl Z₁') = eCl Z₂') :
    φ (e₁ (bCls Z₁)) = e₂ (bCls Z₂) ∧ φ (e₁ (eCl Z₁)) = e₂ (eCl Z₂) := by
  have he : φ (e₁ (eCl Z₁)) = e₂ (eCl Z₂) := by
    obtain ⟨w, hw⟩ := hv.exists_left_inv
    have k₁ : e₁ (eCl Z₁) = w • eCl Z₁' := by rw [← he₁, map_smul, smul_smul, hw, one_smul]
    have k₂ : e₂ (eCl Z₂) = w • eCl Z₂' := by rw [← he₂, map_smul, smul_smul, hw, one_smul]
    rw [k₁, map_smul, hφe, k₂]
  refine ⟨?_, he⟩
  obtain ⟨w, hw⟩ := hs.exists_left_inv
  have k2 : ∀ x y : MbMod Z₂', s • x = s • y → x = y := fun x y h => by
    rw [← one_smul R x, ← one_smul R y, ← hw, mul_smul, mul_smul, h]
  apply k2
  have h0 : φ (e₁ (s • bCls Z₁ + t • eCl Z₁)) = e₂ (s • bCls Z₂ + t • eCl Z₂) := by rw [hb₁, hb₂]; exact hφb
  simp only [map_add, map_smul, he] at h0
  exact add_right_cancel h0

def isoMbeTransport {Z₁ Z₂ Z₁' Z₂' : Matrix (Fin (r + 1)) (Fin (r + 1)) R}
    (e₁ : MbMod Z₁ ≃ₗ[R] MbMod Z₁') (e₂ : MbMod Z₂ ≃ₗ[R] MbMod Z₂') (s t v : R) (hs : IsUnit s) (hv : IsUnit v)
    (hb₁ : e₁ (s • bCls Z₁ + t • eCl Z₁) = bCls Z₁') (hb₂ : e₂ (s • bCls Z₂ + t • eCl Z₂) = bCls Z₂')
    (he₁ : e₁ (v • eCl Z₁) = eCl Z₁') (he₂ : e₂ (v • eCl Z₂) = eCl Z₂') : IsoMbe Z₁ Z₂ ≃ IsoMbe Z₁' Z₂' where
  toFun γ := ⟨(e₁.symm.trans γ.1).trans e₂, by
      have h1 : e₁.symm (bCls Z₁') = s • bCls Z₁ + t • eCl Z₁ := by rw [← hb₁, LinearEquiv.symm_apply_apply]
      simp only [LinearEquiv.trans_apply, h1, map_add, map_smul, γ.2.1, γ.2.2, hb₂],
    by
      have h1 : e₁.symm (eCl Z₁') = v • eCl Z₁ := by rw [← he₁, LinearEquiv.symm_apply_apply]
      simp only [LinearEquiv.trans_apply, h1, map_smul, γ.2.2, he₂]⟩
  invFun γ := ⟨(e₁.trans γ.1).trans e₂.symm, by
      simp only [LinearEquiv.trans_apply,
        (isoMbeTransport_inv e₁ e₂ s t v hs hv hb₁ hb₂ he₁ he₂ γ.1 γ.2.1 γ.2.2).1, LinearEquiv.symm_apply_apply],
    by
      simp only [LinearEquiv.trans_apply,
        (isoMbeTransport_inv e₁ e₂ s t v hs hv hb₁ hb₂ he₁ he₂ γ.1 γ.2.1 γ.2.2).2, LinearEquiv.symm_apply_apply]⟩
  left_inv γ := by apply Subtype.ext; ext x; simp
  right_inv γ := by apply Subtype.ext; ext x; simp

theorem card_isoMbe_transport {Z₁ Z₂ Z₁' Z₂' : Matrix (Fin (r + 1)) (Fin (r + 1)) R}
    (e₁ : MbMod Z₁ ≃ₗ[R] MbMod Z₁') (e₂ : MbMod Z₂ ≃ₗ[R] MbMod Z₂') (s t v : R) (hs : IsUnit s) (hv : IsUnit v)
    (hb₁ : e₁ (s • bCls Z₁ + t • eCl Z₁) = bCls Z₁') (hb₂ : e₂ (s • bCls Z₂ + t • eCl Z₂) = bCls Z₂')
    (he₁ : e₁ (v • eCl Z₁) = eCl Z₁') (he₂ : e₂ (v • eCl Z₂) = eCl Z₂') :
    Nat.card (IsoMbe Z₁ Z₂) = Nat.card (IsoMbe Z₁' Z₂') :=
  Nat.card_congr (isoMbeTransport e₁ e₂ s t v hs hv hb₁ hb₂ he₁ he₂)

def dlast (r : ℕ) (δ : R) : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  Matrix.diagonal fun i => if i = Fin.last r then δ else 1

theorem headCols_eq_of (Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (h : ∀ i (a : Fin r), Z' i a.castSucc = Z i a.castSucc) : headCols Z' = headCols Z := by
  unfold headCols; congr 2; funext a; funext i; exact h i a

def mbEqv (Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (h : ∀ i (a : Fin r), Z' i a.castSucc = Z i a.castSucc) :
    MbMod Z ≃ₗ[R] MbMod Z' :=
  Submodule.quotEquivOfEq _ _ (headCols_eq_of Z Z' h).symm

theorem mbEqv_mk (Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (h) (v : Fin (r + 1) → R) :
    mbEqv Z Z' h (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := rfl

theorem card_isoMbe_lastCol (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (δ c : R) (hδ : IsUnit δ) :
    Nat.card (IsoMbe Z₁ Z₂) =
      Nat.card (IsoMbe (Z₁ * dlast r δ + Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then c else 0)
        (Z₂ * dlast r δ + Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then c else 0)) := by
  have hcol : ∀ (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) i (a : Fin r),
      (Z * dlast r δ + Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then c else 0) i a.castSucc =
        Z i a.castSucc := by
    intro Z i a
    simp [dlast, Matrix.mul_diagonal, Fin.castSucc_ne_last]
  refine card_isoMbe_transport (mbEqv _ _ (hcol Z₁)) (mbEqv _ _ (hcol Z₂)) δ c 1 hδ isUnit_one ?_ ?_ ?_ ?_
  · simp only [bCls, eCl, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add, mbEqv_mk]
    try (congr 1; funext i; by_cases hi : i = Fin.last r <;> simp [dlast, Matrix.mul_diagonal, hi, mul_comm])
  · simp only [bCls, eCl, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add, mbEqv_mk]
    try (congr 1; funext i; by_cases hi : i = Fin.last r <;> simp [dlast, Matrix.mul_diagonal, hi, mul_comm])
  · simp [eCl, mbEqv_mk]
  · simp [eCl, mbEqv_mk]

def mbRowEqv (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (D Dinv : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (h1 : D * Dinv = 1) (h2 : Dinv * D = 1) : MbMod Z ≃ₗ[R] MbMod (D * Z) :=
  Submodule.Quotient.equiv (headCols Z) (headCols (D * Z))
    { toFun := D.mulVec, invFun := Dinv.mulVec,
      map_add' := Matrix.mulVec_add D, map_smul' := fun c v => by simp [Matrix.mulVec_smul],
      left_inv := fun v => by simp [Matrix.mulVec_mulVec, h2],
      right_inv := fun v => by simp [Matrix.mulVec_mulVec, h1] }
    (by
      unfold headCols
      rw [Submodule.map_span]
      congr 1
      ext x
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
        exact ⟨a, by funext i; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]⟩
      · rintro ⟨a, rfl⟩
        exact ⟨_, ⟨a, rfl⟩, by funext i; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]⟩)

theorem mbRowEqv_mk (Z D Dinv : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (h1 h2) (v : Fin (r + 1) → R) :
    mbRowEqv Z D Dinv h1 h2 (Submodule.Quotient.mk v) = Submodule.Quotient.mk (D.mulVec v) := rfl

theorem card_isoMbe_lastRow (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (δ δi : R) (hδ : δ * δi = 1) :
    Nat.card (IsoMbe Z₁ Z₂) = Nat.card (IsoMbe (dlast r δ * Z₁) (dlast r δ * Z₂)) := by
  have h1 : dlast r δ * dlast r δi = 1 := by
    rw [dlast, dlast, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    try (congr 1; funext i; by_cases hi : i = Fin.last r <;> simp [hi, hδ])
  have h2 : dlast r δi * dlast r δ = 1 := by
    rw [dlast, dlast, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    try (congr 1; funext i; by_cases hi : i = Fin.last r <;> simp [hi, hδ, mul_comm])
  have hu : IsUnit δi := ⟨⟨δi, δ, by rw [mul_comm, hδ], hδ⟩, rfl⟩
  refine card_isoMbe_transport (mbRowEqv Z₁ _ _ h1 h2) (mbRowEqv Z₂ _ _ h1 h2) 1 0 δi isUnit_one hu ?_ ?_ ?_ ?_
  · simp only [bCls, one_smul, zero_smul, add_zero, mbRowEqv_mk]
    rw [lift_col_mul]
  · simp only [bCls, one_smul, zero_smul, add_zero, mbRowEqv_mk]
    rw [lift_col_mul]
  · simp only [eCl, ← Submodule.Quotient.mk_smul, mbRowEqv_mk]
    congr 1; funext i; by_cases hi : i = Fin.last r <;> simp [dlast, Matrix.mulVec_diagonal, hi, mul_comm, hδ]
  · simp only [eCl, ← Submodule.Quotient.mk_smul, mbRowEqv_mk]
    congr 1; funext i; by_cases hi : i = Fin.last r <;> simp [dlast, Matrix.mulVec_diagonal, hi, mul_comm, hδ]

end ScaleIso

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
