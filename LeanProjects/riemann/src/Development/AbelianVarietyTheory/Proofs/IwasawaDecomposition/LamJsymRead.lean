import Mathlib
import Formalism.LocalToGlobal.Columns.LevGSym
import Formalism.LocalToGlobal.HermitianForms.DefsSym
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopTargetSym
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.JoinForms

open Formalism.L2.Col

noncomputable section

namespace GlobalTheory.LamRead

theorem sum_skip {F : Type} [Field F] {n r k : ℕ} (hr : r ≤ n) (hk : k ≤ r) (N : Matrix (Fin n) (Fin n) F) (f : ℕ → ℕ → F)
    (hf : ∀ i j : Fin n, f i.1 j.1 = N i j) :
    (∑ x : Fin n, ∑ y : Fin n, if (x : ℕ) + 1 = y ∧ (y : ℕ) < r ∧ (y : ℕ) ≠ k then N x y else 0) =
      ∑ i ∈ Finset.range (k - 1), f i (i + 1) + ∑ i ∈ Finset.range (r - k - 1), f (k + i) (k + i + 1) := by
  rw [Formalism.L2.G.sum_sup hr k ((Finset.range r).filter (fun x => x + 1 ≠ k))
    (fun x hx => by simp only [Finset.mem_filter, Finset.mem_range]; constructor <;> intro h <;> first | exact h.2 | exact ⟨by omega, h⟩) N,
    Finset.filter_filter, Finset.sum_filter]
  have h1 : ∀ x ∈ Finset.range r, (if x + 1 ≠ k ∧ x + 1 < r then Formalism.L2.G.entN N x (x + 1) else 0) =
      if x + 1 < r ∧ x + 1 ≠ k then f x (x + 1) else 0 := fun x hx => by
    by_cases hx' : x + 1 < r ∧ x + 1 ≠ k
    · rw [if_pos hx', if_pos ⟨hx'.2, hx'.1⟩]
      have a1 : x < n := by omega
      have a2 : x + 1 < n := by omega
      unfold Formalism.L2.G.entN
      rw [dif_pos ⟨a1, a2⟩]
      exact (hf ⟨x, a1⟩ ⟨x + 1, a2⟩).symm
    · rw [if_neg hx', if_neg (fun h => hx' ⟨h.2, h.1⟩)]
  rw [Finset.sum_congr rfl h1]
  obtain ⟨d, rfl⟩ : ∃ d, r = k + d := ⟨r - k, by omega⟩
  rw [Finset.sum_range_add, Nat.add_sub_cancel_left]
  by_cases hd : d = 0
  · subst hd
    rw [GlobalTheory.TopLawSym.sum_pred k _ _ fun p hp => by omega]
    simp
  · rw [GlobalTheory.TopLawSym.sum_pred k _ _ fun p hp => by omega,
      GlobalTheory.TopLawSym.sum_pred d (fun p => f (k + p) (k + p + 1)) (fun p => k + p + 1 < k + d ∧ k + p + 1 ≠ k) fun p hp => by omega]

theorem coarse_iff {r m t s i : ℕ} (ht : 0 < t) (hs : s < m) :
    coarse r (List.replicate m t) i = s + 1 ↔ r + s * t ≤ i ∧ i < r + s * t + t := by
  have hb := GlobalTheory.DatumLaw.blk_le (r := r) (a := r + m * t) hs le_rfl
  by_cases hir : i < r
  · rw [coarse_of_lt hir]
    omega
  · by_cases h2 : i < r + m * t
    · rw [GlobalTheory.TopLawSym.coarse_eq ht (by omega) h2, Nat.add_right_cancel_iff, Nat.div_eq_iff ht]
      omega
    · rw [coarse_of_le (by omega), blkIdx_replicate_of_le t m _ (by
        have := Nat.sub_le_sub_right (Nat.not_lt.1 h2) r
        rwa [Nat.add_sub_cancel_left] at this)]
      omega

theorem lamJsym_read (κ κ' K : Type) [CommRing κ] [Field κ'] [Field K] (e : κ →+* κ') (emb : K →+* ℂ) (ψ : AddChar κ K)
    (χ : ℕ → κˣ →* Kˣ) (ψ' : AddChar κ' ℂ) (χ' : ℕ → MulChar κ' ℂ) (n k r t m rS : ℕ) (h : r ≤ n) (hr : r = k + 2 * rS + 1)
    (ht : 0 < t) (hn : r + m * t ≤ n) (hψ : ∀ x, ψ' (e x) = emb (ψ x))
    (hχ : ∀ s, s < m → ∀ c : κˣ, χ' s (e c) = emb ((χ s c : Kˣ) : K)) (M : HJsym κ n k r t m rS h) :
    emb ((lamJsym ψ χ n k r t m rS h M : Kˣ) : K) =
      Formalism.L2.Forms.lamSym ψ' χ' k rS t m ((M.1 : Matrix (Fin n) (Fin n) κ).map e) := by
  let A : ℕ → ℕ → κ := fun i j => if h' : i < n ∧ j < n then (M.1 : Matrix (Fin n) (Fin n) κ) ⟨i, h'.1⟩ ⟨j, h'.2⟩ else 0
  have hA : ∀ i j : Fin n, A i.1 j.1 = (M.1 : Matrix (Fin n) (Fin n) κ) i j := fun i j => dif_pos ⟨i.2, j.2⟩
  have h0 : ((lamJsym ψ χ n k r t m rS h M : Kˣ) : K) =
      ((chiSymF ψ r k rS (HPar0 h _ _ M) : Kˣ) : K) *
        ((detChar χ n r (List.replicate m t) ⟨M.1, HPar_le h _ _ M.2⟩ : Kˣ) : K) := rfl
  have hrS : Formalism.L2.Forms.rSym k rS = r := hr.symm
  rw [h0, GlobalTheory.TopLawSym.chiSymF_val ψ (by omega) (HPar0 h _ _ M) A fun i j => hA (Fin.castLE h i) (Fin.castLE h j), detChar_apply,
    List.length_replicate, Units.coe_prod, map_mul, map_prod, ← hψ]
  unfold Formalism.L2.Forms.lamSym Formalism.L2.Forms.lamJ
  rw [hrS]
  congr 1
  · congr 1
    rw [sum_skip h (by omega) _ (fun i j => e (A i j)) fun i j => by rw [hA]; rfl, map_add, map_sum, map_sum]
  · refine Finset.prod_congr rfl fun s hs => ?_
    rw [Finset.mem_range] at hs
    rw [← hχ s hs, GlobalTheory.TopLaw.blkDet_eq_dB (coarse r (List.replicate m t)) (s + 1) (r + s * t) t (GlobalTheory.DatumLaw.blk_le hs hn)
      (fun i _ => coarse_iff ht hs) ⟨M.1, HPar_le h _ _ M.2⟩ A hA]
    unfold GlobalTheory.DatumLaw.dB
    rw [RingHom.map_det]
    congr 2
    ext u v
    have hb := GlobalTheory.DatumLaw.blk_le hs hn
    have a1 : r + s * t + u.1 < n := by have := u.2; omega
    have a2 : r + s * t + v.1 < n := by have := v.2; omega
    show e (A (r + s * t + u.1) (r + s * t + v.1)) = Formalism.L2.Forms.entN _ (r + s * t + u.1) (r + s * t + v.1)
    unfold Formalism.L2.Forms.entN
    rw [dif_pos ⟨a1, a2⟩]
    exact congrArg e (hA ⟨_, a1⟩ ⟨_, a2⟩)

end GlobalTheory.LamRead
