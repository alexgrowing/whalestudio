import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingHomRhoK

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.TrDualExpand

variable {K : Type} [Field K]

theorem iter_mul (σ : K →+* K) (n : ℕ) (a b : K) : σ^[n] (a * b) = σ^[n] a * σ^[n] b := by
  rw [← RingHom.coe_pow, map_mul]

theorem sum_zmod_val {d : ℕ} [NeZero d] (F : ℕ → K) :
    ∑ s : ZMod d, F s.val = ∑ n ∈ Finset.range d, F n := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_bijective (fun s : ZMod d => (⟨s.val, ZMod.val_lt s⟩ : Fin d))
    ⟨fun a b h => ZMod.val_injective d (by simpa using congrArg Fin.val h),
     fun i => ⟨(i.val : ZMod d), by ext; simp [ZMod.val_natCast_of_lt i.2]⟩⟩ _ _ (fun _ => rfl)

theorem sum_range_even (m : ℕ) (G : ℕ → K) :
    ∑ n ∈ Finset.range (2 * m), (if n % 2 = 0 then G n else 0) = ∑ i ∈ Finset.range m, G (2 * i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, if_pos (by omega), if_neg (by omega), add_zero]

theorem even_case {m d : ℕ} [NeZero d] (hd : 2 * m = d) (σ : K →+* K) (om oms : Fin m → K)
    (h : ∀ r r' : Fin m, (∑ s : ZMod d, if s.val % 2 = 0 then σ^[s.val] (om r * oms r') else 0) =
      if r = r' then 1 else 0) (i j : Fin m) :
    ∑ k, σ^[2 * i.val] (om k) * σ^[2 * j.val] (oms k) = if i = j then 1 else 0 := by
  let M : Matrix (Fin m) (Fin m) K := fun i k => σ^[2 * i.val] (om k)
  let Q : Matrix (Fin m) (Fin m) K := fun i k => σ^[2 * i.val] (oms k)
  have hMQ : M.transpose * Q = 1 := by
    ext r r'
    rw [Matrix.mul_apply, Matrix.one_apply, ← h r r',
      sum_zmod_val (fun n => if n % 2 = 0 then σ^[n] (om r * oms r') else 0), ← hd, sum_range_even,
      ← Fin.sum_univ_eq_sum_range (fun i => σ^[2 * i] (om r * oms r'))]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [iter_mul]
    rfl
  have hMQ' : M * Q.transpose = 1 := by
    have := congrArg Matrix.transpose (mul_eq_one_comm.1 hMQ)
    simpa [Matrix.transpose_mul] using this
  have := congrFun (congrFun hMQ' i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  exact this

theorem sum_eq_ite {d : ℕ} [NeZero d] (σ : K →+* K) (om oms : Fin (d / 2) → K)
    (hT : TrDual d σ om oms) (s t : ZMod d) (hst : s.val % 2 = t.val % 2) :
    ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) = if s = t then 1 else 0 := by
  obtain ⟨hc, h⟩ := hT
  rw [Fintype.card_fin] at hc
  have hs := ZMod.val_lt s
  have ht := ZMod.val_lt t
  let i : Fin (d / 2) := ⟨s.val / 2, by omega⟩
  let j : Fin (d / 2) := ⟨t.val / 2, by omega⟩
  have E := even_case hc σ om oms h i j
  have hij : (i = j) ↔ (s = t) := by
    rw [Fin.ext_iff, ← (ZMod.val_injective d).eq_iff]
    simp only [i, j]
    omega
  rcases Nat.mod_two_eq_zero_or_one s.val with h0 | h1
  · have e1 : s.val = 2 * i.val := by simp only [i]; omega
    have e2 : t.val = 2 * j.val := by simp only [j]; omega
    rw [e1, e2, E]
    exact if_congr hij rfl rfl
  · have e1 : s.val = 2 * i.val + 1 := by simp only [i]; omega
    have e2 : t.val = 2 * j.val + 1 := by simp only [j]; omega
    simp_rw [e1, e2, Function.iterate_succ_apply', ← map_mul, ← map_sum, E]
    split_ifs with h3 h4 h4
    · exact map_one σ
    · exact absurd (hij.1 h3) h4
    · exact absurd (hij.2 h4) h3
    · exact map_zero σ

end GlobalTheory.TrDualExpand

namespace GlobalTheory.KerStd.HypCoord

theorem trDual_expand : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p),
    TrDual (nP D p) σ om oms → ∀ s t : ZMod (nP D p), s.val % 2 = t.val % 2 →
      ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) = if s = t then 1 else 0 :=
  fun _ _ _ σ om oms hT s t hst => GlobalTheory.TrDualExpand.sum_eq_ite σ om oms hT s t hst

end GlobalTheory.KerStd.HypCoord
