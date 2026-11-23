import Formalism.FormalGroupWitt.FormalGroupWittProofs.SolveV
import Formalism.FormalGroupWitt.FormalGroupWittProofs.CoeffExpandEqZero
import Formalism.FormalGroupWitt.FormalGroupWittProofs.CoeffV
import Formalism.FormalGroupWitt.FormalGroupWittProofs.InvIntV
import Formalism.FormalGroupWitt.FormalGroupWittProofs.FunctionalEquationSubstVector

noncomputable section

universe u v w

namespace Formalism.FG.FunctionalEquationHom

open Formalism.G Formalism.LT

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem integralMv_sub {τ : Type w} {a b : MvPowerSeries τ K} (ha : IntegralMv a)
    (hb : IntegralMv b) : IntegralMv (a - b) := by
  unfold IntegralMv at ha hb ⊢
  intro d
  rw [map_sub, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha d) ?_)
  rw [norm_neg]
  exact hb d

theorem funEqV_sub {ι : Type v} [Fintype ι] {τ : Type w} {p q : ℕ} (hq : q ≠ 0) (σ : K →+* K)
    (M : ι → ι → K) {a b : ι → MvPowerSeries τ K} (ha : IsFunEqTypeV p q hq σ M a)
    (hb : IsFunEqTypeV p q hq σ M b) : IsFunEqTypeV p q hq σ M (a - b) := by
  intro j
  convert integralMv_sub (ha j) (hb j) using 1
  simp only [Pi.sub_apply, map_sub, smul_sub, Finset.sum_sub_distrib]
  abel

theorem two_le_q {p q : ℕ} {σ : K →+* K} (h : FunctionalEquationSetting K p q σ) : 2 ≤ q := by
  unfold FunctionalEquationSetting at h
  obtain ⟨hp, ⟨k, hk, rfl⟩, -, -⟩ := h
  calc 2 ≤ p := hp.two_le
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk

theorem main (hSol : Formalism.FG.SolveExistsV.{u, v, w}) (hInv : Formalism.FG.InvIntegralV.{u, v, w})
    (hLow : Formalism.FG.LowCoeffV.{u, v, w}) (hKey : Formalism.FG.FunEqSubstV.{u, v, w}) :
    Formalism.FG.FunEqHomV.{u, v, w} := by
  intro K _ _ _ p q hq σ hS ι _ _ M hM f hf hfF τ _ g hg0 hgF
  obtain ⟨h, h0, hsub⟩ := hSol K ι τ f g hf hg0
  refine ⟨h, h0, ?_, hsub⟩
  have hC : IsFunEqTypeV p q hq σ M (fun j => MvPowerSeries.subst h (f j)) := by
    have e : (fun j => MvPowerSeries.subst h (f j)) = g := funext hsub
    rw [e]
    exact hgF
  exact hInv K ι τ (IsFunEqTypeV p q hq σ M) f hf
    (fun a b ha hb => funEqV_sub hq σ M ha hb)
    (fun P hP0 hPI => hKey K p q hq σ hS ι M hM f hf.1 hfF τ P hP0 hPI)
    (fun D hD N hN hlow => hLow K p q hq σ (two_le_q hS) ι M τ D hD N hN hlow)
    h h0 hC

end Formalism.FG.FunctionalEquationHom

namespace Formalism.FG

theorem FunEqHomV_of (hSol : Formalism.FG.SolveExistsV.{u, v, w}) (hInv : Formalism.FG.InvIntegralV.{u, v, w})
    (hLow : Formalism.FG.LowCoeffV.{u, v, w}) (hKey : Formalism.FG.FunEqSubstV.{u, v, w}) :
    Formalism.FG.FunEqHomV.{u, v, w} :=
  FunctionalEquationHom.main hSol hInv hLow hKey

theorem functional_equation_hom_vector : Formalism.FG.FunEqHomV.{u, v, w} :=
  FunEqHomV_of solve_exists_vector inverse_integral_vector low_coeff_vector functional_equation_subst_vector

end Formalism.FG
