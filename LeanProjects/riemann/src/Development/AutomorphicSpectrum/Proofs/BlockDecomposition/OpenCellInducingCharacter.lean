import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZRes

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem hpg_wGL_conj_apply {i t : ℕ} (h : (i + 1) + t = i + t + 1) (G : GL (Fin (i + t + 1)) k) (a b : Fin (i + t + 1)) :
    ((wGL k h * G * (wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) a b =
      (G : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (wPerm h a) (wPerm h b) := by
  have e : (((wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
      (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k).submatrix id (wPerm h) := rfl
  have e' : ((wGL k h : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
      (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k).submatrix (wPerm h) id := rfl
  rw [Units.val_mul, Units.val_mul, e, e']
  simp [Matrix.mul_apply, Matrix.one_apply]

theorem hpg_wPerm_two {i t : ℕ} (h : (i + 1) + t = i + t + 1) (y : Σ x, Two (Fin (i + 1)) (Fin t) x) :
    wPerm h (two (stdSum h) y) = ePG i t y := by
  simp [wPerm]

theorem hpg_leviProj_wGL_conj {i t : ℕ} (h : (i + 1) + t = i + t + 1) (g : HPG k i t)
    (hq : wGL k h * ((g : Mir k (i + t)) : GL (Fin (i + t + 1)) k) * (wGL k h)⁻¹ ∈ parab k (two (stdSum h))) (x : Bool) :
    leviProj k (two (stdSum h)) ⟨_, hq⟩ x = leviProj k (ePG i t) (hpgIncl k i t g) x := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [leviProj_apply, leviProj_apply]
  show ((wGL k h * ((g : Mir k (i + t)) : GL (Fin (i + t + 1)) k) * (wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) _ _ = _
  rw [hpg_wGL_conj_apply, hpg_wPerm_two, hpg_wPerm_two]
  rfl

theorem open_orbit_twist : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {i j : ℕ} (h : (i + 1) + (j + 1) = i + (j + 1) + 1) (π₁ : Representation ℂ (GL (Fin (i + 1)) k) V) (π₂ : Representation ℂ (GL (Fin (j + 1)) k) W) (g : HPG k i (j + 1)) (hq : wGL k h * ((g : Mir k (i + (j + 1))) : GL (Fin (i + (j + 1) + 1)) k) * (wGL k h)⁻¹ ∈ parab k (two (stdSum h))) (v : ⨂[ℂ] x, TwoT V W x), ((extTensor (mtw (gres (⟨V, π₁⟩ : GRep k (i + 1))) (((j + 1 : ℕ) : ℝ) / 2)).ρ (GRep.tw (⟨W, π₂⟩ : GRep k (j + 1)) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k i (j + 1))) g (tE V W v) = tE V W (sQ h π₁ π₂ ⟨_, hq⟩ v) := by
  intro k _ _ _ _ V W _ _ _ _ i j h π₁ π₂ g hq v
  have hf : leviProj k (two (stdSum h)) ⟨_, hq⟩ false = ((pgProj k i (j + 1) g).1 : GL (Fin (i + 1)) k) :=
    hpg_leviProj_wGL_conj h g hq false
  have ht : leviProj k (two (stdSum h)) ⟨_, hq⟩ true = (pgProj k i (j + 1) g).2 :=
    hpg_leviProj_wGL_conj h g hq true
  have hδ : (deltaHalf k (Two (Fin (i + 1)) (Fin (j + 1))) (leviProj k (two (stdSum h)) ⟨_, hq⟩) : ℂ) =
      (absPow k (((((j + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) (GeneralLinearGroup.det ((pgProj k i (j + 1) g).1 : GL (Fin (i + 1)) k)) : ℂ) *
      (absPow k (((-((i + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) (GeneralLinearGroup.det (pgProj k i (j + 1) g).2) : ℂ) := by
    have e := deltaHalf_two (k := k) (a := Fin (i + 1)) (b := Fin (j + 1))
      (leviProj k (two (stdSum h)) ⟨_, hq⟩ false, leviProj k (two (stdSum h)) ⟨_, hq⟩ true)
    have e2 : leviTwo k (Fin (i + 1)) (Fin (j + 1))
        (leviProj k (two (stdSum h)) ⟨_, hq⟩ false, leviProj k (two (stdSum h)) ⟨_, hq⟩ true) =
        leviProj k (two (stdSum h)) ⟨_, hq⟩ := by
      funext x
      cases x <;> rfl
    rw [e2, hf, ht] at e
    rw [e, Units.val_mul]
    simp only [Fintype.card_fin]
    push_cast
    rfl
  have key : ∀ x : ∀ b, TwoT V W b, ((extTensor (mtw (gres (⟨V, π₁⟩ : GRep k (i + 1))) (((j + 1 : ℕ) : ℝ) / 2)).ρ
      (GRep.tw (⟨W, π₂⟩ : GRep k (j + 1)) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k i (j + 1))) g
        (tE V W (PiTensorProduct.tprod ℂ x)) = tE V W (sQ h π₁ π₂ ⟨_, hq⟩ (PiTensorProduct.tprod ℂ x)) := by
    intro x
    have hr : tE V W (sQ h π₁ π₂ ⟨_, hq⟩ (PiTensorProduct.tprod ℂ x)) =
        (deltaHalf k (Two (Fin (i + 1)) (Fin (j + 1))) (leviProj k (two (stdSum h)) ⟨_, hq⟩) : ℂ) •
          (π₁ (leviProj k (two (stdSum h)) ⟨_, hq⟩ false) (x false) ⊗ₜ[ℂ]
            π₂ (leviProj k (two (stdSum h)) ⟨_, hq⟩ true) (x true)) := by
      show tE V W ((deltaHalf k (Two (Fin (i + 1)) (Fin (j + 1))) (leviProj k (two (stdSum h)) ⟨_, hq⟩) : ℂ) •
        piTensor (twoRep π₁ π₂) (leviProj k (two (stdSum h)) ⟨_, hq⟩) (PiTensorProduct.tprod ℂ x)) = _
      rw [piTensor_tprod, map_smul, Exponents.boolTensorEquiv_tprod]
      rfl
    rw [hr, hf, ht, hδ, Exponents.boolTensorEquiv_tprod]
    refine (extTensor_tmul _ _ _ (x false) (x true)).trans ?_
    show ((absPow k (((((j + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) (GeneralLinearGroup.det ((pgProj k i (j + 1) g).1 : GL (Fin (i + 1)) k)) : ℂ) •
        π₁ ((pgProj k i (j + 1) g).1 : GL (Fin (i + 1)) k) (x false)) ⊗ₜ[ℂ]
      ((absPow k (((-((i + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) (GeneralLinearGroup.det (pgProj k i (j + 1) g).2) : ℂ) •
        π₂ (pgProj k i (j + 1) g).2 (x true)) = _
    rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_smul, mul_comm]
  let A : V ⊗[ℂ] W →ₗ[ℂ] V ⊗[ℂ] W := ((extTensor (mtw (gres (⟨V, π₁⟩ : GRep k (i + 1))) (((j + 1 : ℕ) : ℝ) / 2)).ρ
      (GRep.tw (⟨W, π₂⟩ : GRep k (j + 1)) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k i (j + 1))) g
  have hlin : A ∘ₗ (tE V W).toLinearMap = (tE V W).toLinearMap ∘ₗ sQ h π₁ π₂ ⟨_, hq⟩ :=
    PiTensorProduct.ext (MultilinearMap.ext fun x => key x)
  exact LinearMap.congr_fun hlin v

end GlobalTheory.CompanionTheory.BZRes

end
