import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsWt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

noncomputable section

open Matrix

namespace GlobalTheory.BadCount.WtPsi

open Formalism.L2.SG.Pf.AllRowsWt Formalism.L2.SG.Pf.AllRowsTr

variable {g : ℕ} [Fact g.Prime] {N : ℕ} (c : ZMod g)

theorem posN_lt {a : ℕ} (h : a < N) : posN 0 N a = a := by
  unfold posN; simp [h]

theorem sdg_conj (hc : c ≠ 0) (u : Matrix (Fin N) (Fin N) (ZMod g)) :
    ∑ i ∈ Finset.range (N - 1), entN (diagonal (fun i : Fin N => (tN 0 N c i)⁻¹) * u *
      diagonal (fun i : Fin N => tN 0 N c i)) i (i + 1) = c * ∑ i ∈ Finset.range (N - 1), entN u i (i + 1) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [entN_conj, pair 0 N c hc (by rw [posN_lt (by omega), posN_lt (by omega)])]

theorem uniUp_conj (hc : c ≠ 0) (u : Matrix (Fin N) (Fin N) (ZMod g)) :
    IsUniUp (diagonal (fun i : Fin N => (tN 0 N c i)⁻¹) * u * diagonal (fun i : Fin N => tN 0 N c i)) ↔ IsUniUp u := by
  have h := PJ_conj 0 N c hc u
  unfold PJ at h
  have hv : ∀ M : Matrix (Fin N) (Fin N) (ZMod g), ∀ a, N ≤ a → a < N → entN M a N = 0 :=
    fun _ a h1 h2 => absurd h2 (by omega)
  exact ⟨fun x => (h.1 ⟨x, hv _⟩).1, fun x => (h.2 ⟨x, hv _⟩).1⟩

theorem eU_conj (hc : c ≠ 0) (ψ : AddChar (ZMod g) ℂ) :
    haveI : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
    MonoidAlgebra.single (T 0 N c hc) 1 * eU g N ψ * MonoidAlgebra.single (T 0 N c hc)⁻¹ 1 =
      eU g N (ψ.mulShift c) := by
  classical
  have : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  unfold eU eDat
  rw [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  simp only [MonoidAlgebra.single_mul_single, one_mul, mul_one]
  refine Finset.sum_nbij' (fun u => T 0 N c hc * u * (T 0 N c hc)⁻¹) (fun v => (T 0 N c hc)⁻¹ * v * T 0 N c hc)
    ?_ ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    show IsUniUp ((T 0 N c hc * u * (T 0 N c hc)⁻¹ : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g))
    rw [← uniUp_conj c hc, ← T_conj_val 0 N c hc]
    have e : (T 0 N c hc)⁻¹ * (T 0 N c hc * u * (T 0 N c hc)⁻¹) * T 0 N c hc = u := by group
    rw [e]; exact hu
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    show IsUniUp (((T 0 N c hc)⁻¹ * v * T 0 N c hc : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g))
    rw [T_conj_val, uniUp_conj c hc]; exact hv
  · intro u _; group
  · intro v _; group
  · intro u hu
    have e : (u : GL (Fin N) (ZMod g)) = (T 0 N c hc)⁻¹ * (T 0 N c hc * u * (T 0 N c hc)⁻¹) * T 0 N c hc := by group
    have hφ : ∑ i ∈ Finset.range (N - 1), entN (u : Matrix (Fin N) (Fin N) (ZMod g)) i (i + 1) =
        c * ∑ i ∈ Finset.range (N - 1),
          entN ((T 0 N c hc * u * (T 0 N c hc)⁻¹ : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g)) i (i + 1) := by
      conv_lhs => rw [e]
      rw [T_conj_val, sdg_conj c hc]
    rw [hφ, AddChar.mulShift_apply]

end GlobalTheory.BadCount.WtPsi

namespace GlobalTheory.BadCount

open Formalism.L2.SG.Pf.AllRowsWt Formalism.L2.SG.Pf.AllRowsTr GlobalTheory.BadCount.WtPsi

theorem wtOf_eUk_indep : ∀ (D : D7) (k : Fin 2) (ψ ψ' : AddChar (ZMod (D.host.g k)) ℂ), ψ ≠ 1 → ψ' ≠ 1 →
    ∀ f, wtOf D k (eUk D k ψ) f = wtOf D k (eUk D k ψ') f := by
  intro D k ψ ψ' h h' f
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨c, hc0, rfl⟩ := exists_shift ψ ψ' h h'
  have hconj : eUk D k (ψ.mulShift c) =
      MonoidAlgebra.single (T 0 D.R.r c hc0) 1 * eUk D k ψ * MonoidAlgebra.single (T 0 D.R.r c hc0)⁻¹ 1 := by
    unfold eUk
    exact (eU_conj c hc0 ψ).symm
  have h1 : (eUk D k (ψ.mulShift c) * D.ntypes.eSer k f).coeff 1 = (eUk D k ψ * D.ntypes.eSer k f).coeff 1 := by
    rw [hconj]
    have e1 : MonoidAlgebra.single (T 0 D.R.r c hc0) 1 * eUk D k ψ * MonoidAlgebra.single (T 0 D.R.r c hc0)⁻¹ 1 *
        D.ntypes.eSer k f = MonoidAlgebra.single (T 0 D.R.r c hc0) 1 * (eUk D k ψ * D.ntypes.eSer k f) *
        MonoidAlgebra.single (T 0 D.R.r c hc0)⁻¹ 1 := by
      rw [mul_assoc _ (MonoidAlgebra.single (T 0 D.R.r c hc0)⁻¹ 1) (D.ntypes.eSer k f), ← D.ntypes.eSer_central,
        mul_assoc, mul_assoc, mul_assoc]
    rw [e1, tau_conj]
  have h2 : (eUk D k (ψ.mulShift c)).coeff 1 = (eUk D k ψ).coeff 1 := by
    rw [hconj, tau_conj]
  unfold wtOf
  rw [h1, h2]

end GlobalTheory.BadCount
