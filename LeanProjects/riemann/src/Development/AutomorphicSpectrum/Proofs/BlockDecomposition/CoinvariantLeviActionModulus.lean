import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeTwistedIso
import GroundTheory.PAdicHodge.FactorizationFactorialLe

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.QLevi

theorem tmul_scalars {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (x : A) (y : B)
    (c d d' e f : ℂ) (hd : d * d' = 1) :
    (c * (e * f)) • (x ⊗ₜ[ℂ] y) = (d * e) • ((c • d' • x) ⊗ₜ[ℂ] (f • y)) := by
  rw [smul_smul, TensorProduct.smul_tmul_smul, smul_smul]
  congr 1
  linear_combination (-(c * e * f)) * hd

theorem qC_sigX : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (h : MirabolicParabolic k (i + 1) t) (η : HPG k (i + 1) (t + 1)) (hη : pgProj k (i + 1) (t + 1) η = (levi k (i + 1) (gpProj k (i + 1) t h).1, (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k))) (w : τ.V ⊗[ℂ] σ.V), qC τ σ (sigX τ σ η w) = ((dpow (i + 1) (1 / 2) (gpProj k (i + 1) t h).1 * dpow (t + 1) (-1 / 2) (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k) : ℂˣ) : ℂ) • sigC τ σ h (qC τ σ w) := by
  intro k _ _ _ _ i t τ σ h η hη w
  generalize hgdef : (gpProj k (i + 1) t h).1 = g at *
  generalize hpdef : (gpProj k (i + 1) t h).2 = p at *
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul a b =>
    have hL : sigX τ σ η (a ⊗ₜ[ℂ] b) =
        (((dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2) (levi k (i + 1) g) : ℂˣ) : ℂ) • τ.ρ (levi k (i + 1) g) a) ⊗ₜ[ℂ]
        (((dpow (t + 1) (-((i + 1 + 1 : ℕ) : ℝ) / 2) (p : GL (Fin (t + 1)) k) : ℂˣ) : ℂ) • σ.ρ (p : GL (Fin (t + 1)) k) b) := by
      show extTensor _ _ (pgProj k (i + 1) (t + 1) η) _ = _
      rw [hη]
      exact extTensor_tmul (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ
        (levi k (i + 1) g, (p : GL (Fin (t + 1)) k)) a b
    have hR : sigC τ σ h (qC τ σ (a ⊗ₜ[ℂ] b)) =
        (((dpow (i + 1) (((t + 1 : ℕ) : ℝ) / 2) g : ℂˣ) : ℂ) • ((dpow (i + 1) (-1 / 2) g : ℂˣ) : ℂ) •
          ((twKer τ.ρ (MirUin k (i + 1)) 1).mkQ (τ.ρ (levi k (i + 1) g) a) : (psiN τ).V)) ⊗ₜ[ℂ]
        (((dpow (t + 1) (-((i + 1 : ℕ) : ℝ) / 2) (p : GL (Fin (t + 1)) k) : ℂˣ) : ℂ) • σ.ρ (p : GL (Fin (t + 1)) k) b) := by
      show extTensor _ _ (gpProj k (i + 1) t h) (qC τ σ (a ⊗ₜ[ℂ] b)) = _
      have hq : qC τ σ (a ⊗ₜ[ℂ] b) = ((twKer τ.ρ (MirUin k (i + 1)) 1).mkQ a : (psiN τ).V) ⊗ₜ[ℂ] b := rfl
      have hgp : gpProj k (i + 1) t h = (g, p) := Prod.ext hgdef hpdef
      rw [hq, hgp]
      exact extTensor_tmul ((psiN τ).tw (((t + 1 : ℕ) : ℝ) / 2)).ρ (mtw (gres σ) (-((i + 1 : ℕ) : ℝ) / 2)).ρ (g, p)
        ((twKer τ.ρ (MirUin k (i + 1)) 1).mkQ a : (psiN τ).V) b
    have hg : dpow (i + 1) (1 / 2) g * dpow (i + 1) (-1 / 2) g = (1 : ℂˣ) := by
      have e := DFunLike.congr_fun (GlobalTheory.CompanionTheory.LeibOrd.DerivTw.dpow_add (k := k) (i + 1) (-1 / 2) (1 / 2)) g
      rw [MonoidHom.mul_apply] at e
      rw [← e, show (-1 / 2 + 1 / 2 : ℝ) = 0 by norm_num, GlobalTheory.CompanionTheory.LeibOrd.DerivTw.dpow_zero]
      rfl
    have hp : dpow (t + 1) (-((i + 1 + 1 : ℕ) : ℝ) / 2) (p : GL (Fin (t + 1)) k) =
        dpow (t + 1) (-1 / 2) (p : GL (Fin (t + 1)) k) * dpow (t + 1) (-((i + 1 : ℕ) : ℝ) / 2) (p : GL (Fin (t + 1)) k) := by
      have e := DFunLike.congr_fun (GlobalTheory.CompanionTheory.LeibOrd.DerivTw.dpow_add (k := k) (t + 1) (-((i + 1 : ℕ) : ℝ) / 2) (-1 / 2))
        (p : GL (Fin (t + 1)) k)
      rw [MonoidHom.mul_apply] at e
      rw [← e]
      congr 2
      push_cast
      ring
    have hg' : ((dpow (i + 1) (1 / 2) g : ℂˣ) : ℂ) * ((dpow (i + 1) (-1 / 2) g : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, hg, Units.val_one]
    have hq : qC τ σ ((τ.ρ (levi k (i + 1) g) a) ⊗ₜ[ℂ] (σ.ρ (p : GL (Fin (t + 1)) k) b)) =
        ((twKer τ.ρ (MirUin k (i + 1)) 1).mkQ (τ.ρ (levi k (i + 1) g) a) : (psiN τ).V) ⊗ₜ[ℂ] (σ.ρ (p : GL (Fin (t + 1)) k) b) := rfl
    rw [hL, hR, GlobalTheory.CompanionTheory.LeibOrd.DerivTw.dpowM_levi, hp, TensorProduct.smul_tmul_smul, map_smul, hq]
    exact tmul_scalars _ _ _ _ _ _ _ hg'

end GlobalTheory.CompanionTheory.BZPhiPG.QLevi

end
