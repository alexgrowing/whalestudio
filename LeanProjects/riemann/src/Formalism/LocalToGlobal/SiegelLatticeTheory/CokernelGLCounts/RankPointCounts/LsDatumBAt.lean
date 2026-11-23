import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds

noncomputable section

namespace Formalism.L2.SG.LsDatumB

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Minors

variable {K : Type*} [CommRing K]

theorem sum_castLE {N l : ℕ} (h : l ≤ N) (f : Fin N → K) (hf : ∀ k : Fin N, l ≤ k.val → f k = 0) :
    ∑ k, f k = ∑ k' : Fin l, f (Fin.castLE h k') := by
  have hsub : (Finset.univ : Finset (Fin l)).map (Fin.castLEEmb h) ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_subset hsub (fun k _ hk => ?_), Finset.sum_map]
  · rfl
  · apply hf
    by_contra hlt
    push_neg at hlt
    exact hk (Finset.mem_map.2 ⟨⟨k.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem submatrix_loUni_mul {N l : ℕ} (h : l ≤ N) (L A U : Matrix (Fin N) (Fin N) K) (hL : IsLoUni L)
    (hU : IsUpUni U) :
    (L * A * U).submatrix (Fin.castLE h) (Fin.castLE h) =
      L.submatrix (Fin.castLE h) (Fin.castLE h) * A.submatrix (Fin.castLE h) (Fin.castLE h) *
        U.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have hin : ∀ m : Fin N, ∑ k, L (Fin.castLE h i) k * A k m =
      ∑ k' : Fin l, L (Fin.castLE h i) (Fin.castLE h k') * A (Fin.castLE h k') m := fun m =>
    sum_castLE h _ fun k hk => by
      rw [(hL _ _).1 (Fin.lt_iff_val_lt_val.2 (lt_of_lt_of_le (by simpa using i.isLt) hk)), zero_mul]
  simp only [hin]
  exact sum_castLE h _ fun m hm => by
    rw [(hU _ _).1 (Fin.lt_iff_val_lt_val.2 (lt_of_lt_of_le (by simpa using j.isLt) hm)), mul_zero]

theorem det_sub_loUni {N l : ℕ} (h : l ≤ N) (L A U : Matrix (Fin N) (Fin N) K) (hL : IsLoUni L) (hU : IsUpUni U) :
    ((L * A * U).submatrix (Fin.castLE h) (Fin.castLE h)).det = (A.submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  rw [submatrix_loUni_mul h L A U hL hU, Matrix.det_mul, Matrix.det_mul]
  have h1 : (L.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1 := by
    have hb : (L.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular OrderDual.toDual := by
      intro i j hij
      exact (hL _ _).1 (Fin.lt_iff_val_lt_val.2 (by
        simpa using Fin.lt_iff_val_lt_val.1 (OrderDual.toDual_lt_toDual.1 hij)))
    rw [Matrix.det_of_lowerTriangular _ hb]
    exact Finset.prod_eq_one fun i _ => (hL _ _).2 rfl
  have h2 : (U.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1 := by
    have hb : (U.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id := by
      intro i j hij
      exact (hU _ _).1 (Fin.lt_iff_val_lt_val.2 (by simpa using Fin.lt_iff_val_lt_val.1 hij))
    rw [Matrix.det_of_upperTriangular hb]
    exact Finset.prod_eq_one fun i _ => (hU _ _).2 rfl
  rw [h1, h2, one_mul, mul_one]

theorem det_sub_ZhatOM {r l : ℕ} (h : l ≤ r + 1) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    ((ZhatOM Z).submatrix (Fin.castLE h) (Fin.castLE h)).det =
      (∏ b : Fin l, ((-1 : K) ^ (r - b.val))) * (Z.submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  have e : (ZhatOM Z).submatrix (Fin.castLE h) (Fin.castLE h) =
      Z.submatrix (Fin.castLE h) (Fin.castLE h) * Matrix.diagonal fun b : Fin l => (-1 : K) ^ (r - b.val) := by
    ext a b
    simp [ZhatOM, Matrix.mul_diagonal, mul_comm]
  rw [e, Matrix.det_mul, Matrix.det_diagonal, mul_comm]

end Minors

theorem conjF_eq_star {D : Formalism.BasicNotions.D7} (x : D.host.E) : D.conjF x = star x :=
  (D.conjF_eq x).trans (Formalism.BasicNotions.Examples₂.star_eq_conj (H := D.host) x).symm

theorem atPtG_holds {D : Formalism.BasicNotions.D7} (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : AtPtG u u' F0 what₂ := by
  intro γ w hat
  obtain ⟨F', -, hG, L, U, hL, hU, hZ⟩ := hat
  have N_eq : ∀ (l : ℕ) (h : l ≤ D.R.rS + 1),
      leadMinorE (ZhatL (lf D F0) F') l * star (leadMinorE (ZhatL (lf D F0) F') l) =
        Dmin w l * D.conjF (Dmin w l) := by
    intro l h
    have e1 : ((ptMat w).submatrix (Fin.castLE h) (Fin.castLE h)).det =
        (∏ b : Fin l, ((-1 : D.host.E) ^ (D.R.rS - b.val))) *
          ((ZhatL (lf D F0) F').submatrix (Fin.castLE h) (Fin.castLE h)).det := by
      rw [← det_sub_loUni h L (ptMat w) U hL hU, ← hZ]
      exact det_sub_ZhatOM h _
    have hss : (∏ b : Fin l, ((-1 : D.host.E) ^ (D.R.rS - b.val))) *
        (∏ b : Fin l, ((-1 : D.host.E) ^ (D.R.rS - b.val))) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun b _ => by rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    have hst : star (∏ b : Fin l, ((-1 : D.host.E) ^ (D.R.rS - b.val))) =
        ∏ b : Fin l, ((-1 : D.host.E) ^ (D.R.rS - b.val)) := by
      rw [star_prod]
      exact Finset.prod_congr rfl fun b _ => by rw [star_pow, star_neg, star_one]
    have hD : Dmin w l = ((ptMat w).submatrix (Fin.castLE h) (Fin.castLE h)).det := by
      unfold Dmin
      rw [dif_pos h]
    have hM : leadMinorE (ZhatL (lf D F0) F') l =
        ((ZhatL (lf D F0) F').submatrix (Fin.castLE h) (Fin.castLE h)).det := by
      unfold leadMinorE
      rw [dif_pos h]
    rw [hD, hM, conjF_eq_star, e1, star_mul', hst]
    linear_combination (-(((ZhatL (lf D F0) F').submatrix (Fin.castLE h) (Fin.castLE h)).det *
      star ((ZhatL (lf D F0) F').submatrix (Fin.castLE h) (Fin.castLE h)).det)) * hss
  have key : Gval (lf D F0) F' = Gpt (D.mem u).A.T (D.mem u').A.T w := by
    rw [CntLocal.gz_eq]
    unfold CntLocal.GZ Gpt
    rw [N_eq (D.R.rS + 1) le_rfl, N_eq D.R.rS (Nat.le_succ _)]
    rfl
  rw [← key]
  exact hG

theorem dnInDens_of {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (hN : NormRepElig u u' F0 what₂) (hrows : IsRowReps D F0 what₂) :
    DnInDens u u' F0 what₂ := by
  intro γ w hγ
  have hex := hN γ w hγ
  have hz : zT γ = ZhatL (lf D F0) hex.choose.2.1 := by
    unfold zT nrep
    rw [dif_pos hex]
  obtain ⟨⟨hPD, hmk⟩, hadm, -, -, -⟩ := hex.choose_spec
  have hTF := Formalism.L2.SG.Closed.TermFun_holds D u u' F0 γ.lam (hrows.1 γ.lam γ.mem)
  have hGt := TermDef.Gt_mk hTF.1 ⟨_, hPD⟩
  have hGen := TermDef.isGen_mk (gS D) hTF.2.2.2.1 ⟨_, hPD⟩
  rw [hmk] at hGt hGen
  refine ⟨γ.lam, γ.mem, hex.choose.2.1, ⟨hPD.1, hPD.2.1, ?_⟩, hadm, hGen.1 hγ.1.1, hPD.2.2, hz.symm⟩
  exact fun h => hγ.1.2 (hGt.trans h)

end Formalism.L2.SG.LsDatumB
