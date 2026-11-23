import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeFunctorTwistEquiv
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG

theorem qC_sigX_unip : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (u : HPG k (i + 1) (t + 1)) (h1 : (pgProj k (i + 1) (t + 1) u).1 ∈ MirUin k (i + 1)) (h2 : (pgProj k (i + 1) (t + 1) u).2 = 1) (w : τ.V ⊗[ℂ] σ.V), qC τ σ (sigX τ σ u w) = qC τ σ w := by
  intro k _ _ _ _ i t τ σ u h1 h2 w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    have hd : ((dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2) (pgProj k (i + 1) (t + 1) u).1 : ℂˣ) : ℂ) = 1 := by
      have := GlobalTheory.CompanionTheory.LeibPhiTw.dpowM_unip (k := k) (i + 1) (((t + 1 : ℕ) : ℝ) / 2) ⟨_, h1⟩
      simpa using congrArg Units.val this
    have ha : (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (pgProj k (i + 1) (t + 1) u).1 a = τ.ρ (pgProj k (i + 1) (t + 1) u).1 a := by
      refine (twist_apply τ.ρ (dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2)) _ a).trans ?_
      rw [hd, one_smul]
    have hρ : (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ (pgProj k (i + 1) (t + 1) u).2 = 1 := by
      rw [h2, map_one]
    have hb : (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ (pgProj k (i + 1) (t + 1) u).2 b = b :=
      LinearMap.congr_fun hρ b
    have e : sigX τ σ u (a ⊗ₜ[ℂ] b) = (τ.ρ (pgProj k (i + 1) (t + 1) u).1 a) ⊗ₜ[ℂ] b :=
      (extTensor_tmul (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ
        (pgProj k (i + 1) (t + 1) u) a b).trans (congrArg₂ (fun x y => TensorProduct.tmul ℂ x y) ha hb)
    have hq : (twKer τ.ρ (MirUin k (i + 1)) 1).mkQ (τ.ρ (pgProj k (i + 1) (t + 1) u).1 a) =
        (twKer τ.ρ (MirUin k (i + 1)) 1).mkQ a := by
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      unfold twKer
      apply Submodule.subset_span
      exact ⟨⟨_, h1⟩, a, by simp⟩
    rw [e]
    exact congrArg (fun x => TensorProduct.tmul ℂ x b) hq

end GlobalTheory.CompanionTheory.BZPhiPG
