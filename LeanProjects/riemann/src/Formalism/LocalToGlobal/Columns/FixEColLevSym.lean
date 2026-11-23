import Formalism.LocalToGlobal.Columns.LastRowColLevSym
import Formalism.LocalToGlobal.Columns.OcbLevIsSym

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section FE

variable {X : Fields} {Pr : Primes X} {R : Ranks}

private theorem mulVec_eN_eq_of_mem_HPar {κ : Type} [CommRing κ] {n r k rS t s : ℕ} (hr : r ≤ n) (ht : 0 < t)
    (hn : n = r + s * t) (hkr : k < r) (hkrS : k + rS ≤ r) (M : GL (Fin n) κ)
    (hM : M ∈ HPar n κ hr (List.replicate s t) (HPsymF κ r k rS)) :
    (M : Matrix (Fin n) (Fin n) κ) *ᵥ Loc.eN κ n k = Loc.eN κ n k := by
  rw [mem_HPar_iff hr ht hn] at hM
  obtain ⟨hB, hS⟩ := hM
  rw [mem_HPsymF_iff hkrS] at hS
  obtain ⟨s1, s2, s3⟩ := hS
  have hv := upper_block_val_submatrix hr (blockTri_blkOf_le r t hB)
  rw [mem_blockTri] at hB
  have hkn : k < n := by omega
  have he : Loc.eN κ n k = Pi.single (⟨k, hkn⟩ : Fin n) 1 := by
    funext l
    simp only [Loc.eN, Pi.single_apply, Fin.ext_iff]
  rw [he, Matrix.mulVec_single_one]
  funext i
  simp only [Matrix.col_apply, Pi.single_apply]
  by_cases hir : (i : ℕ) < r
  · have key : ∀ a b : Fin r, ((upperLeftBlock hr M : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) a b =
        (M : Matrix (Fin n) (Fin n) κ) (Fin.castLE hr a) (Fin.castLE hr b) := by
      intro a b
      rw [hv]
      rfl
    have hk' : (⟨k, hkn⟩ : Fin n) = Fin.castLE hr ⟨k, hkr⟩ := Fin.ext rfl
    rw [hk']
    by_cases hik : (i : ℕ) = k
    · have hi2 : i = Fin.castLE hr ⟨k, hkr⟩ := Fin.ext hik
      rw [if_pos hi2, hi2, ← key]
      exact s2 _
    · have hi' : i = Fin.castLE hr ⟨i, hir⟩ := Fin.ext rfl
      rw [if_neg (fun h => hik (by rw [h]; rfl)), hi', ← key]
      by_cases hrS : rS = 0
      · rcases Nat.lt_or_gt_of_ne hik with h | h
        · exact s3 _ _ h (by simp [hrS])
        · exact s1 _ _ (by simp only [symIdx, Fin.val_mk, hrS]; split_ifs <;> omega)
      · exact s1 _ _ (by simp only [symIdx, Fin.val_mk]; split_ifs <;> omega)
  · rw [if_neg (fun h => hir (by rw [h]; exact hkr))]
    exact hB _ _ (by
      simp only [blkOf, Fin.val_mk, if_pos hkr, if_neg hir]
      exact Nat.succ_pos _)

theorem fixE_colLevSym (Ch : Chars X Pr R.m) {m2 : ℕ} (hm : R.m = m2 + 2) : FixE (R := R) (colLevSym Ch) m2 := by
  intro h hh w
  have hw : h w ∈ (colLevSym Ch (m2 + 1) w).H := (Subgroup.mem_pi _).mp hh w (Set.mem_univ _)
  have e0 : ¬ (m2 + 1 = 0) := by omega
  have e1 : ¬ (m2 + 1 + 1 < R.m) := by omega
  have e2 : m2 + 1 + 1 = R.m := by omega
  unfold colLevSym at hw
  rw [if_neg e0, dif_neg e1, dif_pos e2] at hw
  exact mulVec_eN_eq_of_mem_HPar _ (by have := R.rank_add_five_le; omega)
    (by
      show R.k + (m2 + 1) * (R.t + 1) = R.k + R.m - 1 + (m2 + 1) * R.t
      rw [hm, Nat.mul_succ]
      omega)
    (by
      show R.k < R.k + R.m - 1
      have := R.two_le_m
      omega)
    (by
      show R.k + (R.m / 2 - 1) ≤ R.k + R.m - 1
      omega) _ hw

end FE

end Formalism.L2.Col
