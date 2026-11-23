import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.DefUTest
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.DefUSel

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.alSel :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), (∀ α ∈ S.Tp, S.alC α ∈ SelP S.h S.x S.F ∧ BndM S.x.t (S.alC α)) ∧ (∀ μ ∈ S.La, S.laC μ ∈ SelM S.h S.x S.F ∧ BndM S.x.t (S.laC μ)) ∧ (∀ (ι : Type) [Fintype ι] (c : ι → S.F) (α : ι → S.Bh →+ S.F), S.alC (∑ i, c i • α i) = ∑ i, c i • S.alC (α i)) ∧ ∀ (ι : Type) [Fintype ι] (c : ι → S.F) (μ : ι → S.U.N →+ S.F), S.laC (∑ i, c i • μ i) = ∑ i, c i • S.laC (μ i) := by
  intro l _ S
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α hα
    obtain ⟨u, ψ, hU, -, h2⟩ := defUTest l S 1 (fun _ => α) (fun _ => 0) 0 (fun _ => hα)
      (fun _ => S.La.zero_mem) (by intro b y; simp)
    have h := defUSel l _ _ _ S.h S.n S.x 1 u ψ hU 0
    rw [h2 0] at h
    exact h.1
  · intro μ hμ
    obtain ⟨u, ψ, hU, h1, -⟩ := defUTest l S 1 (fun _ => 0) (fun _ => μ) 0 (fun _ => S.Tp.zero_mem)
      (fun _ => hμ) (by intro b y; simp)
    have h := defUSel l _ _ _ S.h S.n S.x 1 u ψ hU 0
    rw [h1 0] at h
    exact h.2
  · intro ι _ c α
    funext g
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Ctx.alC]
    simp only [← smul_mul_assoc]
    rw [← Finset.sum_mul]
    congr 1
    ext i j
    simp [Matrix.map_apply, Matrix.sum_apply, AddMonoidHom.finset_sum_apply]
  · intro ι _ c μ
    funext g
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Ctx.laC]
    simp only [← smul_mul_assoc]
    rw [← Finset.sum_mul]
    congr 1
    ext i j
    simp [Matrix.map_apply, Matrix.sum_apply, AddMonoidHom.finset_sum_apply]
