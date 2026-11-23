import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittAlg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoGram

noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittAlg

open Matrix Formalism.UG

private theorem s_inv_eq_of_s_eq_of_mul_eq_one {S : Type} [CommRing S] (s : S →+* S) (b b' : S) (hb : s b = b)
    (h : b * b' = 1) : s b' = b' := by
  have h1 : s b * s b' = 1 := by rw [← map_mul, h, map_one]
  rw [hb] at h1
  calc s b' = (b' * b) * s b' := by rw [mul_comm b' b, h, one_mul]
    _ = b' * (b * s b') := by ring
    _ = b' := by rw [h1, mul_one]

private theorem hform_transvection_preserves {S : Type} [CommRing S] (s : S →+* S) (hs : ∀ z, s (s z) = z) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) S) (hJ : IsHerm s J) (v : Fin n → S) (b b' lam : S)
    (hvv : hform s J v v = b) (hbb : b * b' = 1) (hb' : s b' = b') (hlam : lam * s lam = 1)
    (z w : Fin n → S) :
    hform s J (z + ((s lam - 1) * (b' * hform s J v z)) • v)
      (w + ((s lam - 1) * (b' * hform s J v w)) • v) = hform s J z w := by
  have hzv : hform s J z v = s (hform s J v z) := (hform_conj s J hs hJ v z).symm
  simp only [hform_add_left, hform_add_right, hform_smul_left, hform_smul_right]
  rw [hzv, hvv]
  simp only [map_mul, map_sub, map_one, hs, hb']
  linear_combination (b' * hform s J v w * s (hform s J v z)) * hlam +
    (b' * hform s J v w * s (hform s J v z) * (lam - 1) * (s lam - 1)) * hbb

theorem algWitt : Formalism.L2.SG.Pf.NcS.IntWittPf.AlgWitt := by
  unfold Formalism.L2.SG.Pf.NcS.IntWittPf.AlgWitt
  intro S _ s O hs hsO n J J' hJ hJJ' hJO hJ'O a β β' hβO hβ'O hββ' hH x y hxO hyO hxx hyy

  have key : ∀ k : ℕ, k ≤ a → ∃ M : Matrix (Fin n) (Fin n) S,
      (∀ z w, hform s J (M *ᵥ z) (M *ᵥ w) = hform s J z w) ∧ (∀ i j, M i j ∈ O) ∧
      ∀ i : Fin a, i.val < k → M *ᵥ y i = x i := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨1, fun z w => by rw [Matrix.one_mulVec, Matrix.one_mulVec],
        fun i j => Formalism.L2.SG.Pf.NcS.IntWittAlg.one_mem' O i j, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨M, hMp, hMO, hMy⟩ := ih (Nat.le_of_succ_le hk)
      obtain ⟨i0, hi0⟩ : ∃ i0 : Fin a, i0.val = k := ⟨⟨k, hk⟩, rfl⟩
      obtain ⟨yy, hyy_def⟩ : ∃ yy : Fin n → S, yy = M *ᵥ y i0 := ⟨_, rfl⟩
      have hyyO : ∀ l, yy l ∈ O := fun l => by
        rw [hyy_def]; exact mulVec_mem O M hMO (y i0) (hyO i0) l
      have htO : hform s J (x i0) yy ∈ O := hform_mem O s hsO J hJO (x i0) yy (hxO i0) hyyO
      obtain ⟨lam, hlamO, hlam, c', hc'O, hc'⟩ := hH i0 (hform s J (x i0) yy) htO
      have hxx0 : hform s J (x i0) (x i0) = β i0 := by rw [hxx, if_pos rfl]
      have hyy0 : hform s J yy yy = β i0 := by rw [hyy_def, hMp, hyy, if_pos rfl]
      have hβr : s (β i0) = β i0 := by
        have h := hform_conj s J hs hJ (x i0) (x i0)
        rwa [hxx0] at h
      have hβ'r : s (β' i0) = β' i0 := s_inv_eq_of_s_eq_of_mul_eq_one s (β i0) (β' i0) hβr (hββ' i0)

      obtain ⟨u, hu_def⟩ : ∃ u : Fin n → S, u = yy - lam • x i0 := ⟨_, rfl⟩
      have huO : ∀ l, u l ∈ O := fun l => by
        rw [hu_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        exact O.sub_mem (hyyO l) (O.mul_mem hlamO (hxO i0 l))
      have huy : hform s J u yy = β i0 - s lam * hform s J (x i0) yy := by
        rw [hu_def, hform_sub_left, hform_smul_left, hyy0]
      have huu : hform s J u u =
          (β i0 - s lam * hform s J (x i0) yy) + s (β i0 - s lam * hform s J (x i0) yy) := by
        rw [hu_def]
        simp only [hform_sub_left, hform_sub_right, hform_smul_left, hform_smul_right]
        rw [hyy0, hxx0, ← hform_conj s J hs hJ (x i0) yy]
        simp only [map_sub, map_mul, hs, hβr]
        linear_combination (β i0) * hlam
      have hcc : c' * (β i0 - s lam * hform s J (x i0) yy) = 1 := by rw [mul_comm]; exact hc'
      obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin n) (Fin n) S, T = rT s J u c' 1 := ⟨_, rfl⟩
      have hT_mul : ∀ z, T *ᵥ z = z - (c' * hform s J u z) • u := fun z => by
        rw [hT, rT_mulVec, map_one, one_smul]
      have hT_pres : ∀ z w, hform s J (T *ᵥ z) (T *ᵥ w) = hform s J z w := fun z w => by
        rw [hT]
        exact rT_preserves s J hs hJ u _ c' 1 (by rw [map_one, one_mul]) huu hcc z w
      have hT_O : ∀ i j, T i j ∈ O := fun i j => by
        rw [hT]; exact rT_mem O s hsO J hJO u huO c' 1 hc'O O.one_mem i j
      have hT_yy : T *ᵥ yy = lam • x i0 := by
        rw [hT_mul, huy, hcc, one_smul, hu_def, sub_sub_cancel]

      obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin n) (Fin n) S,
          D = 1 + (s lam - 1) • pM s J {i0} x β' := ⟨_, rfl⟩
      have hD_mul : ∀ z, D *ᵥ z = z + ((s lam - 1) * (β' i0 * hform s J (x i0) z)) • x i0 :=
        fun z => by
          rw [hD, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, pM_mulVec,
            Finset.sum_singleton, smul_smul]
      have hD_pres : ∀ z w, hform s J (D *ᵥ z) (D *ᵥ w) = hform s J z w := fun z w => by
        rw [hD_mul, hD_mul]
        exact hform_transvection_preserves s hs J hJ (x i0) (β i0) (β' i0) lam hxx0 (hββ' i0) hβ'r hlam z w
      have hD_O : ∀ i j, D i j ∈ O := fun i j => by
        rw [hD, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        exact O.add_mem (Formalism.L2.SG.Pf.NcS.IntWittAlg.one_mem' O i j)
          (O.mul_mem (O.sub_mem (hsO lam hlamO) O.one_mem)
            (pM_mem O s hsO J hJO {i0} x hxO β' hβ'O i j))
      have hD_x : D *ᵥ (lam • x i0) = x i0 := by
        rw [hD_mul, hform_smul_right, hxx0]
        funext l
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linear_combination (x i0 l) * hlam + (x i0 l * (lam * s lam - lam)) * hββ' i0

      have hfix : ∀ i : Fin a, i.val < k → D *ᵥ (T *ᵥ x i) = x i := by
        intro i hi
        have hne : i0 ≠ i := fun h => by subst h; omega
        have h0 : hform s J u (x i) = 0 := by
          rw [hu_def, hform_sub_left, hform_smul_left, hxx i0 i, if_neg hne, ← hMy i hi, hyy_def,
            hMp, hyy i0 i, if_neg hne]
          ring
        rw [hT_mul, h0, mul_zero, zero_smul, sub_zero, hD_mul, hxx i0 i, if_neg hne, mul_zero,
          mul_zero, zero_smul, add_zero]
      refine ⟨D * T * M, fun z w => ?_, fun i j => ?_, fun i hi => ?_⟩
      · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          ← Matrix.mulVec_mulVec, hD_pres, hT_pres, hMp]
      · exact Formalism.L2.SG.Pf.NcS.IntWittAlg.mul_mem' O (D * T) M
          (fun i j => Formalism.L2.SG.Pf.NcS.IntWittAlg.mul_mem' O D T hD_O hT_O i j) hMO i j
      · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
        · rw [hMy i hlt]; exact hfix i hlt
        · have hi' : i = i0 := Fin.ext (by omega)
          rw [hi', ← hyy_def, hT_yy, hD_x]
  obtain ⟨M, hMp, hMO, hMy⟩ := key a le_rfl
  have hU : cT s M * J * M = J := unitary_of s J M hMp
  have hNM : (J' * cT s M * J) * M = 1 := by
    calc (J' * cT s M * J) * M = J' * (cT s M * J * M) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU, hJJ']
  have hMN : M * (J' * cT s M * J) = 1 := mul_eq_one_comm.mp hNM
  refine ⟨⟨M, J' * cT s M * J, hMN, hNM⟩, ?_, fun i j => hMO i j, fun i j => ?_, fun i => hMy i i.isLt⟩
  · show cT s M * J * M = J
    exact hU
  · show (J' * cT s M * J) i j ∈ O
    exact Formalism.L2.SG.Pf.NcS.IntWittAlg.mul_mem' O (J' * cT s M) J
      (fun i j => Formalism.L2.SG.Pf.NcS.IntWittAlg.mul_mem' O J' (cT s M) hJ'O
        (fun i j => cT_mem O s hsO M hMO i j) i j) hJO i j

end Formalism.L2.SG.Pf.NcS.IntWittAlg
