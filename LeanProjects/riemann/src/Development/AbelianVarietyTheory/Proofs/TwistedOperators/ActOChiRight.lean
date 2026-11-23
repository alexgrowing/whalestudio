import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEqSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovFn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOMemLatOOfHat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemAtConjOfOtherPrimeOverSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenComapProdLev
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

open GlobalTheory.StdFrames
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
namespace GlobalTheory.RowMoveAt
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem notOff (S : GridChoice W U) {t : T} (ht : t ∈ U) {w : Pl D.host.E} (hw : w ∈ locPl G t) : ¬ Off S.N.S w := by
  classical
  intro h0
  have h3 := S.N.off w h0
  rcases Finset.mem_union.1 hw with h | h
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
    exact h3.1 (by rw [G.pl.under_w hv]; exact hv)
  · exact h3.2.1 t ht w h rfl

theorem cpt_supp_zero {S : Finset ℕ} {w : Pl D.host.E} (hw : ¬ Off S w) {P : Finset (Pl D.host.E)} {e : AE D}
    (he : IsIdemSum e P) (hoff : ∀ w' ∈ P, Off S w') : cpt w (toEAf D (e + cA D e)) = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [map_sum, ← Finset.sum_add_distrib, map_sum, map_sum]
  refine Finset.sum_eq_zero fun w' hw' => ?_
  obtain ⟨hne, hnc⟩ := GlobalTheory.StdHalfLat.ne_and_not_conj hw (hoff w' hw')
  rw [map_add, map_add, (cpt_of_isIdemAt (hes w' hw')).2 w hne,
    (cpt_of_isIdemAt (GlobalTheory.MovedIdem.isIdemAt_conj (hes w' hw') (GlobalTheory.IdemSupport.mem_cP w'))).2 w ?_, add_zero]
  rintro rfl
  apply hnc
  intro c hc
  exact ⟨GlobalTheory.IdemSupport.cO D c, (GlobalTheory.IdemSupport.mem_cP w' c).1 hc, by simp [GlobalTheory.IdemSupport.cO]⟩

theorem map_mt_eq_one {S : Finset ℕ} {w : Pl D.host.E} (hw : ¬ Off S w) {P : Finset (Pl D.host.E)} {e : AE D}
    (he : IsIdemSum e P) (hoff : ∀ w' ∈ P, Off S w') {V : HSp D} {g : GA D V} (hg : SuppAt e V g) :
    (mt V g).map ((cpt w).comp (toEAf D)) = 1 := by
  have h0 := cpt_supp_zero hw he hoff
  have h1 : (mt V g - 1).map ((cpt w).comp (toEAf D)) = 0 := by
    ext i j
    rw [Matrix.map_apply, ← hg i j, RingHom.comp_apply, map_mul, map_mul, h0, zero_mul, Matrix.zero_apply]
  have h2 : (mt V g).map ((cpt w).comp (toEAf D)) =
      (mt V g - 1).map ((cpt w).comp (toEAf D)) + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map ((cpt w).comp (toEAf D)) := by
    rw [← Matrix.map_add _ (map_add _), sub_add_cancel]
  rw [h2, h1, zero_add, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.RowMoveAt

namespace GlobalTheory.RowMoveAt
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem actO_chi_right (j : ℕ) (M : GA D (G.V (.grid (j + 1) D.R.m)))
    (x : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))) :
    actO _ _ (G.toPair (.chi j D.R.m) 1 M)⁻¹.1 (G.toPair (.chi j D.R.m) 1 M)⁻¹.2 x =
      (x : Matrix _ _ (AE D)) * mt (G.V (.grid (j + 1) D.R.m)) M := by
  simp only [actO, GridData.toPair, Prod.fst_inv, Prod.snd_inv, inv_inv, inv_one]
  rw [show mt (G.pT (.chi j D.R.m : Pair T)) 1 = 1 from rfl, Matrix.one_mul]
  rfl

theorem actO_chi_left (j : ℕ) (M : GA D (G.V (.grid (j + 1) D.R.m)))
    (x : WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T))) :
    actO _ _ (G.toPair (.chi (j + 1) D.R.m) M 1)⁻¹.1 (G.toPair (.chi (j + 1) D.R.m) M 1)⁻¹.2 x =
      mt (G.V (.grid (j + 1) D.R.m)) M⁻¹ * (x : Matrix _ _ (AE D)) := by
  simp only [actO, GridData.toPair, Prod.fst_inv, Prod.snd_inv, inv_inv, map_one, inv_one]
  rw [show mt (G.pS (.chi (j + 1) D.R.m : Pair T)) 1 = 1 from rfl, Matrix.mul_one]

theorem sub_mul_cast {K : Type} [Field K] {a b a' b' : ℕ} (ha : a' = a) (hb : b' = b) (P : GL (Fin a) K) (Q : GL (Fin b) K)
    (Y : Matrix (Fin a) (Fin b) K) (X : Matrix (Fin b) (Fin b) K) :
    ((P⁻¹).val * (Y * X) * Q.val).submatrix (Fin.cast ha) (Fin.cast hb) =
      ((P⁻¹).val * Y * Q.val).submatrix (Fin.cast ha) (Fin.cast hb) * ((Q⁻¹).val * X * Q.val).submatrix (Fin.cast hb) (Fin.cast hb) := by
  rw [← Matrix.submatrix_mul _ _ (Fin.cast ha) (Fin.cast hb) (Fin.cast hb) (finCongr hb).bijective]
  congr 1
  simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]

theorem mul_sub_cast {K : Type} [Field K] {a b a' b' : ℕ} (ha : a' = a) (hb : b' = b) (P : GL (Fin a) K) (Q : GL (Fin b) K)
    (Y : Matrix (Fin a) (Fin b) K) (X : Matrix (Fin a) (Fin a) K) :
    ((P⁻¹).val * (X * Y) * Q.val).submatrix (Fin.cast ha) (Fin.cast hb) =
      ((P⁻¹).val * X * P.val).submatrix (Fin.cast ha) (Fin.cast ha) * ((P⁻¹).val * Y * Q.val).submatrix (Fin.cast ha) (Fin.cast hb) := by
  rw [← Matrix.submatrix_mul _ _ (Fin.cast ha) (Fin.cast ha) (Fin.cast hb) (finCongr ha).bijective]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (P.val), Units.mul_inv, Matrix.one_mul]

theorem inBasis_val {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) :
    (inBasis h β w x).val = (((loc w β)⁻¹).val * (loc w x).val * (loc w β).val).submatrix (Fin.cast h) (Fin.cast h) := by
  ext i j
  rw [GlobalTheory.FunObj.ProdOpen.inBasis_apply, ← map_inv, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
  rfl

end GlobalTheory.RowMoveAt

namespace GlobalTheory.RowMoveAt

theorem rowAt_move : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)) (w : Pl D.host.E), w ∈ locPl G t →
    ∀ (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
    S.rowAt t w (Function.update (Function.update y ⟨j, by omega⟩
        (actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1 (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2
          (y ⟨j, by omega⟩) : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))))
      ⟨j + 1, hj⟩ (actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1
          (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 (y ⟨j + 1, hj⟩) :
          WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T)))) =
    Function.update (Function.update (S.rowAt t w y) j
        (S.rowAt t w y j * @id (Matrix (Fin ((locGrid G t w).rank (j + 1, (locGrid G t w).m)))
            (Fin ((locGrid G t w).rank (j + 1, (locGrid G t w).m))) (Kw w)) (inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w
          (finG (G.V (.grid (j + 1) D.R.m)) k)).val))
      (j + 1) (@id (Matrix (Fin ((locGrid G t w).rank (j + 1, (locGrid G t w).m)))
            (Fin ((locGrid G t w).rank (j + 1, (locGrid G t w).m))) (Kw w)) (inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w
          (finG (G.V (.grid (j + 1) D.R.m)) k))⁻¹.val * S.rowAt t w y (j + 1)) := by
  intro D T L sc G W U S t ht j hj k w hw y
  have hX : DefNode D.R.m (.grid (j + 1) D.R.m) := ⟨by omega, rfl⟩
  obtain ⟨P, e, he, hsupp, hoff⟩ := S.N.u_supp _ hX
  have hn := notOff S ht hw
  have hu := map_mt_eq_one hn he hoff hsupp
  have hu' := map_mt_eq_one hn he hoff (GlobalTheory.StdHalfLat.suppAt_inv' hsupp)
  have hM : (mt _ (moved S j k)).map ((cpt w).comp (toEAf D)) = (loc w (finG (G.V (.grid (j + 1) D.R.m)) k)).val := by
    rw [show mt _ (moved S j k) = mt _ (S.N.u (.grid (j + 1) D.R.m)).1⁻¹ * mt _ k.1 * mt _ (S.N.u (.grid (j + 1) D.R.m)).1 from rfl,
      Matrix.map_mul, Matrix.map_mul, hu, hu', Matrix.one_mul, Matrix.mul_one]
    rfl
  have hM' : (mt _ (moved S j k)⁻¹).map ((cpt w).comp (toEAf D)) = (loc w (finG (G.V (.grid (j + 1) D.R.m)) k⁻¹)).val := by
    rw [show mt _ (moved S j k)⁻¹ = mt _ (S.N.u (.grid (j + 1) D.R.m)).1⁻¹ * mt _ k.1⁻¹ * mt _ (S.N.u (.grid (j + 1) D.R.m)).1 from by
      rw [RowVertexInv.moved]; simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc]; rfl,
      Matrix.map_mul, Matrix.map_mul, hu, hu', Matrix.one_mul, Matrix.mul_one]
    rfl
  funext i

  by_cases h1 : i = j + 1
  · subst h1
    rw [Function.update_self]
    simp only [GridChoice.rowAt, dif_pos hj, Function.update_self, Frames.coord]
    rw [actO_chi_left, Matrix.map_mul, hM']
    erw [Matrix.transpose_transpose, Matrix.transpose_transpose, id_eq]
    rw [← map_inv (inBasis _ (S.B.β (j + 1) D.R.m) w), map_inv (finG (G.V (Node.grid (j + 1) D.R.m))) k, inBasis_val, mul_sub_cast]
    rfl
  by_cases h2 : i = j
  · subst h2
    rw [Function.update_of_ne (by omega), Function.update_self]
    have hj' : i < D.R.m := by omega
    simp only [GridChoice.rowAt, dif_pos hj', Frames.coord]
    rw [Function.update_of_ne (fun h => by simp [Fin.ext_iff] at h), Function.update_self, actO_chi_right, Matrix.map_mul, hM]
    erw [Matrix.transpose_transpose, Matrix.transpose_transpose, id_eq]
    rw [inBasis_val, sub_mul_cast]
    rfl
  · rw [Function.update_of_ne h1, Function.update_of_ne h2]
    simp only [GridChoice.rowAt]
    by_cases hi : i < D.R.m
    · rw [dif_pos hi, dif_pos hi, Function.update_of_ne (fun h => h1 (by simpa [Fin.ext_iff] using h)),
        Function.update_of_ne (fun h => h2 (by simpa [Fin.ext_iff] using h))]
    · rw [dif_neg hi, dif_neg hi]
end GlobalTheory.RowMoveAt
