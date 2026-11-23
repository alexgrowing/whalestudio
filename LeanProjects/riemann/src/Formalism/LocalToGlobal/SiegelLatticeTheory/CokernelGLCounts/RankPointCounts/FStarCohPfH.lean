import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfG
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.GramNondeg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarPairOrthogonal.MemThPairs

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohGoodPf

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace GramNePf

theorem sign_norm {l : ℕ} (hl : l ≤ D.R.rS + 1) :
    leadMinorE (ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)) l *
      star (leadMinorE (ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)) l) = 1 := by
  have hsub : (ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)).submatrix
      (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.diagonal (fun i : Fin l => (-1 : D.host.E) ^ (D.R.rS - (Fin.castLE hl i).val)) := by
    ext i j
    rcases eq_or_ne i j with rfl | h
    · simp [ZhatOM]
    · have h' : Fin.castLE hl i ≠ Fin.castLE hl j := fun e => h (Fin.castLE_injective hl e)
      simp [ZhatOM, Matrix.one_apply_ne h', Matrix.diagonal_apply_ne _ h]
  have hdet : Formalism.MainNotions.S.leadMinorE (ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)) l =
      (-1 : D.host.E) ^ (∑ i : Fin l, (D.R.rS - (Fin.castLE hl i).val)) := by
    unfold Formalism.MainNotions.S.leadMinorE
    rw [dif_pos hl, hsub, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
  rw [hdet, star_pow, star_neg, star_one, ← pow_add]
  exact Even.neg_one_pow ⟨_, rfl⟩

theorem conjF_star (x : D.host.E) : D.conjF x = star x := by
  rw [D.conjF_eq]
  exact (Formalism.BasicNotions.Examples₂.star_eq_conj D.host x).symm

private lemma submatrix_castLE_mul_of_upper {K : Type*} [Field K] {n l : ℕ} (hl : l ≤ n) (A B : Matrix (Fin n) (Fin n) K)
    (hB : ∀ i j, j < i → B i j = 0) :
    (A * B).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      A.submatrix (Fin.castLE hl) (Fin.castLE hl) * B.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl) _ _ ?_ (fun k => rfl)
  intro k hk
  have hkl : l ≤ k.val := by
    by_contra h
    exact hk ⟨⟨k.val, by omega⟩, Fin.ext rfl⟩
  rw [hB k (Fin.castLE hl j) (by rw [Fin.lt_def, Fin.val_castLE]; exact lt_of_lt_of_le j.isLt hkl), mul_zero]

private lemma submatrix_castLE_mul_of_lower {K : Type*} [Field K] {n l : ℕ} (hl : l ≤ n) (A B : Matrix (Fin n) (Fin n) K)
    (hA : ∀ i j, i < j → A i j = 0) :
    (A * B).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      A.submatrix (Fin.castLE hl) (Fin.castLE hl) * B.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl) _ _ ?_ (fun k => rfl)
  intro k hk
  have hkl : l ≤ k.val := by
    by_contra h
    exact hk ⟨⟨k.val, by omega⟩, Fin.ext rfl⟩
  rw [hA (Fin.castLE hl i) k (by rw [Fin.lt_def, Fin.val_castLE]; exact lt_of_lt_of_le i.isLt hkl), zero_mul]

private lemma det_submatrix_castLE_of_isLoUni {K : Type*} [Field K] {n l : ℕ} (hl : l ≤ n) (L : Matrix (Fin n) (Fin n) K)
    (hL : IsLoUni L) : (L.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
  have hb : (L.submatrix (Fin.castLE hl) (Fin.castLE hl)).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := by simpa using hij
    show L (Fin.castLE hl i) (Fin.castLE hl j) = 0
    exact (hL _ _).1 (by rw [Fin.lt_def, Fin.val_castLE, Fin.val_castLE]; exact hij')
  rw [Matrix.det_of_lowerTriangular _ hb]
  exact Finset.prod_eq_one (fun i _ => (hL _ _).2 rfl)

private lemma det_submatrix_castLE_of_isUpUni {K : Type*} [Field K] {n l : ℕ} (hl : l ≤ n) (U : Matrix (Fin n) (Fin n) K)
    (hU : IsUpUni U) : (U.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
  have hb : (U.submatrix (Fin.castLE hl) (Fin.castLE hl)).BlockTriangular id := by
    intro i j hij
    have hij' : j < i := by simpa using hij
    show U (Fin.castLE hl i) (Fin.castLE hl j) = 0
    exact (hU _ _).1 (by rw [Fin.lt_def, Fin.val_castLE, Fin.val_castLE]; exact hij')
  rw [Matrix.det_of_upperTriangular hb]
  exact Finset.prod_eq_one (fun i _ => (hU _ _).2 rfl)

private lemma det_submatrix_castLE_LPU_eq {K : Type*} [Field K] {n l : ℕ} (hl : l ≤ n) (L P U : Matrix (Fin n) (Fin n) K)
    (hL : IsLoUni L) (hU : IsUpUni U) :
    ((L * P * U).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (P.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  rw [submatrix_castLE_mul_of_upper hl _ _ (fun i j h => (hU i j).1 h), submatrix_castLE_mul_of_lower hl _ _ (fun i j h => (hL i j).1 h),
    Matrix.det_mul, Matrix.det_mul, det_submatrix_castLE_of_isLoUni hl L hL, det_submatrix_castLE_of_isUpUni hl U hU, one_mul, mul_one]

private lemma zhatOM_eq_mul_zhatOM_one {K : Type*} [CommRing K] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    ZhatOM Z = Z * ZhatOM (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) K) := by
  ext a b
  simp [ZhatOM, Matrix.mul_apply, Matrix.one_apply]
  try ring

theorem gflag_ne (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (hC : Ctx γ Z) (hZ : ZhatL (lf D F0) F'₂ = Z) :
    Gflag (lf D F0).fl F'₂.fl ≠ 0 := by
  obtain ⟨w, -, w', hG, -, hA⟩ := hC
  obtain ⟨L, U, hL, hU, hM⟩ := hA
  have hS : ∀ i j : Fin (D.R.rS + 1), j < i →
      ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) i j = 0 := by
    intro i j h
    simp [ZhatOM, Matrix.one_apply_ne (ne_of_gt h)]
  have hsq : ∀ l, l ≤ D.R.rS + 1 →
      Formalism.MainNotions.S.leadMinorE Z l * star (Formalism.MainNotions.S.leadMinorE Z l) = Dmin w' l * D.conjF (Dmin w' l) := by
    intro l hl
    have h1 : Dmin w' l = Formalism.MainNotions.S.leadMinorE Z l *
        Formalism.MainNotions.S.leadMinorE (ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)) l := by
      unfold Dmin Formalism.MainNotions.S.leadMinorE
      simp only [dif_pos hl]
      rw [← Matrix.det_mul, ← submatrix_castLE_mul_of_upper hl _ _ hS, ← zhatOM_eq_mul_zhatOM_one, hM, det_submatrix_castLE_LPU_eq hl _ _ _ hL hU]
    rw [h1, conjF_star, star_mul']
    linear_combination (-(Formalism.MainNotions.S.leadMinorE Z l * star (Formalism.MainNotions.S.leadMinorE Z l))) * sign_norm hl
  intro h0
  apply hG
  unfold Formalism.MainNotions.S.LocalSplitGroups.Gpt
  rw [← hsq _ le_rfl, ← hsq _ (Nat.le_succ _)]
  refine Eq.trans ?_ h0
  unfold Formalism.MainNotions.S.Gflag Formalism.MainNotions.S.Dl
  rw [show Formalism.MainNotions.S.Zhat (lf D F0).fl F'₂.fl = Z from hZ]
  rfl

end GramNePf

open GramNePf

theorem globGramNe_holds : GlobGramNe u u' F0 what₂ := by
  intro _ γ Z F'₂ hC hZ hdet
  have hG := gflag_ne γ Z F'₂ hC hZ
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hw : ∀ k, (VS D).hT (wG F0 F'₂ k) (∑ j, v j • wG F0 F'₂ j) = 0 := by
    intro k
    have hk := congr_fun hv k
    simp only [Matrix.mulVec, dotProduct, gramG, Matrix.of_apply, brS, Pi.zero_apply] at hk
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    exact (Finset.sum_congr rfl (fun j _ => mul_comm _ _)).trans hk
  obtain ⟨h1, h2⟩ := PI.UnitaryGroupMassFormula.BetaLUniq.GN.coeffs_zero F0 F'₂.fl (v ∘ Sum.inl) (v ∘ Sum.inr)
    (∑ j, v j • wG F0 F'₂ j) (by rw [Fintype.sum_sum_type]; rfl)
    (fun a => hw (Sum.inl a)) (fun b => hw (Sum.inr b)) hG
  apply hv0
  funext k
  rcases k with a | b
  · exact congr_fun h1 a
  · exact congr_fun h2 b

variable (Zd : LocDat D)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
