import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NabBijectiveWindow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenEigenMultiplicityQuotientAdditiveChainStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicityShiftLatticeVariablePowStatement

noncomputable section
namespace GlobalTheory.PhiGam.Range
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem finite_map_trans {k U : Type} [Field k] [AddCommGroup U] [Module k U] {P Q S : Submodule k U}
    (hSQ : S ≤ Q) (h1 : FiniteDimensional k (P.map Q.mkQ)) (h2 : FiniteDimensional k (Q.map S.mkQ)) :
    FiniteDimensional k (P.map S.mkQ) := by
  refine Module.Finite.iff_fg.mpr (Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.factor hSQ) ?_ ?_)
  · rw [← Submodule.map_comp, Submodule.factor_comp_mk]
    exact Module.Finite.iff_fg.mp h1
  · have hle : P.map S.mkQ ⊓ LinearMap.ker (Submodule.factor hSQ) ≤ Q.map S.mkQ := by
      rintro _ ⟨⟨p, -, rfl⟩, hp⟩
      exact ⟨p, (Submodule.Quotient.mk_eq_zero Q).mp hp, rfl⟩
    exact Module.Finite.iff_fg.mp (Submodule.finiteDimensional_of_le hle)

theorem finite_quot_of_map {k U : Type} [Field k] [AddCommGroup U] [Module k U] {P S : Submodule k U}
    (h : FiniteDimensional k (P.map S.mkQ)) : FiniteDimensional k (↥P ⧸ S.submoduleOf P) := by
  have hker : LinearMap.ker (S.mkQ ∘ₗ P.subtype) = S.submoduleOf P := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]; rfl
  have hr : LinearMap.range (S.mkQ ∘ₗ P.subtype) = P.map S.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  haveI : FiniteDimensional k (LinearMap.range (S.mkQ ∘ₗ P.subtype)) := by rw [hr]; exact h
  rw [← hker]
  exact LinearEquiv.finiteDimensional (LinearMap.quotKerEquivRange _).symm

theorem gmult_self {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U)
    (P : Submodule k U) (x : k) : gmult T P P x = 0 := by
  unfold gmult
  set P' := P ⊓ ⨆ m : ℕ, P.comap ((T - algebraMap k (Module.End k U) x) ^ m)
  have h : P.submoduleOf P' = ⊤ := eq_top_iff.mpr fun y _ => y.2.1
  haveI : Subsingleton (↥P' ⧸ P.submoduleOf P') := Submodule.Quotient.subsingleton_iff.mpr h
  exact Module.finrank_zero_of_subsingleton

theorem finite_sh {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
    [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
    {N : Submodule k⟦X⟧ V} (hN : IsLat N) (a : ℤ) (m : ℕ) :
    FiniteDimensional k (((sh a N).restrictScalars k).map ((sh (a + m) N).restrictScalars k).mkQ) := by
  induction m with
  | zero =>
    rw [Nat.cast_zero, add_zero, Submodule.mkQ_map_self]
    infer_instance
  | succ m ih =>
    have h := Window.finite_quot (hN.shift (a + m)).1
    rw [sh_sh_eq, add_comm (1 : ℤ)] at h
    rw [Nat.cast_succ, ← add_assoc]
    exact finite_map_trans (fun y hy => Window.sh_succ_le _ _ hy) ih h

theorem qmult_sh_range : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (a : ℤ) (m : ℕ) (x : k), qmult g (sh a N) (sh (a + m) N) x = ∑ j ∈ Finset.range m, sen g N (x + (a + j : ℤ)) := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N hN hC a m x
  induction m with
  | zero =>
    rw [Nat.cast_zero, add_zero, Finset.sum_range_zero]
    exact gmult_self _ _ _
  | succ m ih =>
    have hf := finite_quot_of_map (finite_sh hN a (m + 1))
    rw [Finset.sum_range_succ, ← ih, ← GlobalTheory.T.senMultiplicity_shift_lattice_variablePow R g hg N hN hC (a + m) x, sen, sh_sh_eq,
      add_comm (1 : ℤ)]
    rw [Nat.cast_succ, ← add_assoc] at hf ⊢
    exact GlobalTheory.T.genEigenMultiplicityQuotient_additive_chain (nab g) _ _ _ (fun y hy => Window.sh_succ_le _ _ hy)
      (fun y hy => Window.sh_add_le a m N hy) (fun y hy => Window.nab_mem_sh R hg hC _ hy)
      (fun y hy => Window.nab_mem_sh R hg hC _ hy) (fun y hy => Window.nab_mem_sh R hg hC _ hy) hf x

end GlobalTheory.PhiGam.Range
