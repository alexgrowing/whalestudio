import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeFunctorTwistEquiv
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Coinv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def cls {i : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (x : τ.V) : (phiN ψ τ).V :=
  (twKer τ.ρ (MirUin k (i + 1)) (mirChar k ψ i)).mkQ x

theorem qO_tmul {i t : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (x : τ.V) (y : σ.V) :
    qO τ σ ψ (x ⊗ₜ[ℂ] y) = cls ψ τ x ⊗ₜ[ℂ] y := rfl

theorem phiN_cls {i : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (a : Mir k i) (x : τ.V) :
    (phiN ψ τ).ρ a (cls ψ τ x) = ((dpowM i (-1 / 2) a : ℂˣ) : ℂ) • cls ψ τ (τ.ρ (sEmb k i a) x) :=
  twist_apply _ _ _ _

theorem dpowM_half (i : ℕ) (a : Mir k i) :
    ((dpowM i (1 / 2) a : ℂˣ) : ℂ) * ((dpowM i (-1 / 2) a : ℂˣ) : ℂ) = 1 := by
  have h : dpow (k := k) (i + 1) (1 / 2 + -1 / 2) = dpow (i + 1) (1 / 2) * dpow (i + 1) (-1 / 2) :=
    GlobalTheory.CompanionTheory.LeibPhi.dpow_add k (i + 1) _ _
  have h0 : dpow (k := k) (i + 1) (1 / 2 + -1 / 2) = 1 := by
    rw [show ((1 / 2 + -1 / 2 : ℝ)) = 0 by norm_num]
    ext g
    simp [dpow, detChar, absPow]
  have h1 := congrArg (fun f => ((f (a : GL (Fin (i + 1)) k) : ℂˣ) : ℂ)) (h.symm.trans h0)
  simpa [dpowM] using h1

theorem dpow_step (i t : ℕ) (w : GL (Fin (t + 1)) k) :
    ((dpow (t + 1) (-((i + 1 + 1 : ℕ) : ℝ) / 2) w : ℂˣ) : ℂ) =
      ((dpow (t + 1) (-1 / 2) w : ℂˣ) : ℂ) * ((dpow (t + 1) (-((i + 1 : ℕ) : ℝ) / 2) w : ℂˣ) : ℂ) := by
  have e : (-((i + 1 + 1 : ℕ) : ℝ) / 2) = -1 / 2 + (-((i + 1 : ℕ) : ℝ) / 2) := by
    push_cast; ring
  rw [e, GlobalTheory.CompanionTheory.LeibPhi.dpow_add]
  simp

theorem smul_tmul_scal {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (p : X) (q : Y)
    (c d e f f' g : ℂ) (h : c * d = e * (f * f' * g)) :
    (c • p) ⊗ₜ[ℂ] (d • q) = e • ((f • f' • p) ⊗ₜ[ℂ] (g • q)) := by
  rw [smul_smul f f' p]
  generalize f * f' = f at h
  rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul',
    smul_smul, smul_smul, smul_smul, mul_comm d c, h, mul_comm f g, mul_assoc]

theorem intertwine (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (a : Mir k i) (w : GL (Fin (t + 1)) k) (v : τ.V ⊗[ℂ] σ.V) :
  qO τ σ ψ (extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ (sEmb k i a, w) v) =
    (((dpowM i (1 / 2) a : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) w : ℂˣ) : ℂ)) •
      extTensor (mtw (phiN ψ τ) (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ (a, w) (qO τ σ ψ v) := by
  let L : τ.V ⊗[ℂ] σ.V →ₗ[ℂ] (phiN ψ τ).V ⊗[ℂ] σ.V := (qO τ σ ψ) ∘ₗ
    (extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ (sEmb k i a, w))
  let R : τ.V ⊗[ℂ] σ.V →ₗ[ℂ] (phiN ψ τ).V ⊗[ℂ] σ.V :=
    (((dpowM i (1 / 2) a : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) w : ℂˣ) : ℂ)) •
      ((extTensor (mtw (phiN ψ τ) (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ (a, w)) ∘ₗ (qO τ σ ψ))
  have hLR : L = R := by
    refine TensorProduct.ext' fun x y => ?_
    have hl : (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (sEmb k i a) x =
        ((dpowM i (((t + 1 : ℕ) : ℝ) / 2) a : ℂˣ) : ℂ) • τ.ρ (sEmb k i a) x :=
      (twist_apply _ _ _ _).trans (by
        rw [show sEmb k i a = (levi k (i + 1)).comp (Mir k i).subtype a from rfl, GlobalTheory.CompanionTheory.LeibPhiTw.dpowM_levi]
        rfl)
    have hr : ∀ s : ℝ, (σ.tw s).ρ w y = ((dpow (t + 1) s w : ℂˣ) : ℂ) • σ.ρ w y := fun s => twist_apply _ _ _ _
    have hm : (mtw (phiN ψ τ) (((t + 1 : ℕ) : ℝ) / 2)).ρ a (cls ψ τ x) =
        ((dpowM i (((t + 1 : ℕ) : ℝ) / 2) a : ℂˣ) : ℂ) • (phiN ψ τ).ρ a (cls ψ τ x) := twist_apply _ _ _ _
    have hc : ∀ (c : ℂ) (z : τ.V), cls ψ τ (c • z) = c • cls ψ τ z := fun c z => map_smul _ c z
    have eL : L (x ⊗ₜ[ℂ] y) = cls ψ τ ((mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (sEmb k i a) x) ⊗ₜ[ℂ]
        (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ w y := rfl
    have eR : R (x ⊗ₜ[ℂ] y) = (((dpowM i (1 / 2) a : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) w : ℂˣ) : ℂ)) •
        ((mtw (phiN ψ τ) (((t + 1 : ℕ) : ℝ) / 2)).ρ a (cls ψ τ x) ⊗ₜ[ℂ] (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ w y) := rfl
    rw [eL, eR, hl, hm, phiN_cls, hr, hr, hc, dpow_step]
    have hh := dpowM_half i a
    refine smul_tmul_scal (X := (phiN ψ τ).V) (Y := σ.V) _ _ _ _ _ _ _ _ ?_
    linear_combination (-(((dpowM i (((t + 1 : ℕ) : ℝ) / 2) a : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) w : ℂˣ) : ℂ) * ((dpow (t + 1) (-((i + 1 : ℕ) : ℝ) / 2) w : ℂˣ) : ℂ))) * hh
  exact LinearMap.congr_fun hLR v

end GlobalTheory.CompanionTheory.BZPhiPG.Coinv

end
