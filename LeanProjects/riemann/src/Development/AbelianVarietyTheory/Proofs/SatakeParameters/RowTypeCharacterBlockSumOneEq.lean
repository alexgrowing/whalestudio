import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.XiAtPenultimateEqXiCpl1
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.Columns.ChainTwTopQ
import Formalism.LocalToGlobal.Columns.DiagUnitMemAndNormalizesKOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopTargetTwist
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

namespace GlobalTheory.SumRowType

variable {E : Type} [Field E]

theorem atN_sumE_last {n : ℕ} (j : Sp E n ≃ₗ[E] Sp E n) (t : ℕ) :
    Loc.atN ((sumE (rfl : n + 1 = n + 1) j 1) (Loc.eN E (n + 1) t)) n = if n = t then 1 else 0 := by
  rw [Loc.atN, dif_pos (Nat.lt_succ_self n)]
  have h := sumE_last (rfl : n + 1 = n + 1) j 1 (Loc.eN E (n + 1) t)
  have e : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Br.iL (rfl : n + 1 = n + 1) := rfl
  rw [e, h, Units.val_one, one_mul]
  rfl

theorem atN_sumE_up {n : ℕ} (j : Sp E n ≃ₗ[E] Sp E n) (t s : ℕ) (hs : s < n) :
    Loc.atN ((sumE (rfl : n + 1 = n + 1) j 1) (Loc.eN E (n + 1) t)) s = Loc.atN (j (Loc.eN E n t)) s := by
  rw [Loc.atN, dif_pos (by omega), Loc.atN, dif_pos hs]
  have h := congrFun (prH_sumE (rfl : n + 1 = n + 1) j 1 (Loc.eN E (n + 1) t)) ⟨s, hs⟩
  have e1 : prH E (rfl : n + 1 = n + 1) (Loc.eN E (n + 1) t) = Loc.eN E n t := by
    funext i
    rw [prH_apply]
    rfl
  rw [e1] at h
  rw [← h, prH_apply]
  rfl

end GlobalTheory.SumRowType

namespace GlobalTheory.SumRowType

open Matrix in
theorem det_sumE {E : Type} [Field E] {n : ℕ} (r : ℕ) (hr : r ≤ n) (j : Sp E n ≃ₗ[E] Sp E n) :
    (Matrix.of fun s t : Fin (n + 1 - r) =>
        Loc.atN ((sumE (rfl : n + 1 = n + 1) j 1).toLinearMap (Loc.eN E (n + 1) (r + t.1))) (r + s.1)).det =
      (Matrix.of fun s t : Fin (n - r) => Loc.atN (j.toLinearMap (Loc.eN E n (r + t.1))) (r + s.1)).det := by
  obtain ⟨m, rfl⟩ : ∃ m, n = r + m := ⟨n - r, by omega⟩
  have hm : r + m + 1 - r = m + 1 := by omega
  have hm' : r + m - r = m := by omega
  set A := Matrix.of fun s t : Fin (r + m + 1 - r) =>
    Loc.atN ((sumE (rfl : r + m + 1 = r + m + 1) j 1).toLinearMap (Loc.eN E (r + m + 1) (r + t.1))) (r + s.1) with hA
  rw [← Matrix.det_submatrix_equiv_self (finCongr hm).symm A]
  rw [← Matrix.det_submatrix_equiv_self (finCongr hm').symm]
  rw [Matrix.det_succ_row _ (Fin.last m)]
  rw [Finset.sum_eq_single (Fin.last m)]
  · have e1 : A.submatrix (finCongr hm).symm (finCongr hm).symm (Fin.last m) (Fin.last m) = 1 := by
      show Loc.atN ((sumE rfl j 1) (Loc.eN E (r + m + 1) (r + m))) (r + m) = 1
      rw [atN_sumE_last, if_pos rfl]
    rw [e1, Fin.succAbove_last, Fin.val_last, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, one_mul]
    congr 1
    ext s t
    show Loc.atN ((sumE rfl j 1) (Loc.eN E (r + m + 1) (r + t.1))) (r + s.1) =
      Loc.atN (j (Loc.eN E (r + m) (r + t.1))) (r + s.1)
    exact atN_sumE_up j _ _ (by have := s.2; omega)
  · intro b _ hb
    have hb' : b.1 < m := Fin.val_lt_last hb
    have e1 : A.submatrix (finCongr hm).symm (finCongr hm).symm (Fin.last m) b = 0 := by
      show Loc.atN ((sumE rfl j 1) (Loc.eN E (r + m + 1) (r + b.1))) (r + m) = 0
      rw [atN_sumE_last, if_neg (by omega)]
    rw [e1, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem lamQB_sumE : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {N n : ℕ} (hN : N = n + 1) (r : ℕ), r ≤ n → ∀ j : Sp E n ≃ₗ[E] Sp E n, LocE.lamQB ξ r N (sumE hN j 1).toLinearMap = LocE.lamQB ξ r n j.toLinearMap := by
  intro E K _ _ _ _ P ξ N n hN r hr j
  subst hN
  unfold LocE.lamQB
  rw [det_sumE r hr j]

end GlobalTheory.SumRowType
