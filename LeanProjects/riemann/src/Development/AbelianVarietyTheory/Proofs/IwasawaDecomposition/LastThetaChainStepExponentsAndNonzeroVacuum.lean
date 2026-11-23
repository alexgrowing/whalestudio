import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpMulZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastStepVac

theorem last_step : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → IsInfFam R.θ → R.chain_ωX → R.chain_vX → ∀ t (k : Fin D.R.m), (k : ℕ) = D.R.m - 1 → IsStepWeil k R.ψ (Yc D (D.R.m - 1)) D.sp.X' (R.ωX t) ∧ IsVacVec R.ψ R.θ (R.MY (D.R.m - 1)) R.MX (R.vX t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL _ hω hv t k hk
  have hm := D.R.two_le_m
  have hk' : (k : ℕ) + 1 = D.R.m := by omega
  have he := GlobalTheory.InnerSteps.exp_chrStep R.toLevCh hL t k
  rw [hk'] at he
  refine ⟨⟨_, _, hω t, he⟩, ?_⟩
  have hr : (Yc D (D.R.m - 1)).rank ≤ D.sp.X'.rank := by
    rw [D.sp.Y_rank _ (min_le_right _ _), D.sp.X'_rank]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (min_le_right _ _)) _
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.InnerSteps.stepVec_vac
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY (D.R.m - 1) (by omega)))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hL.βX) hr (hv t)
  exact ⟨h1, h2, h3⟩

end GlobalTheory.LastStepVac

end
