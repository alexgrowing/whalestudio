import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.FlatPlace

namespace NormalJac

theorem jacobiDualColumn_scalar_identity {K : Type} [Field K] (X : K) (hX : X ≠ 0) (i k : ℕ) :
    (X ^ (i + 1 + k))⁻¹ * (-((-X) ^ (i + 1 + k) * X ^ (i + 1 + k)) / X) * (-1 / X) ^ k = (-X) ^ i := by
  have h1 : ((-1 : K) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [neg_pow X, neg_pow X, div_pow]
  field_simp
  linear_combination (X * X ^ i * X ^ k * (-1) ^ i) * h1

theorem mul_col_eq {ι' ι κ μ K : Type} [Fintype ι] [Field K] (P : Matrix ι' ι K) (Y : Matrix ι κ K) (Z : Matrix ι μ K)
    (c : κ) (c' : μ) (h : ∀ l, Y l c = Z l c') (r : ι') : (P * Y) r c = (P * Z) r c' := by
  simp only [mul_apply, h]

theorem hz_besAt {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {t : T} {M : Vol G} (hM : M.Is t)
    (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (vN : GlobalTheory.Unf.VolN (besDecAt G j σ hj)) {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) :
    p.hz (besAt G hM j σ hj vN) = -((-p.xi) ^ σ * p.xi ^ σ) := by
  simp only [Place.hz, besAt, dotProduct, mulVec]
  show p.pr (∑ i : Fin 1, star (fun _ : Fin 1 => D.host.xi0 ^ σ) i * ∑ i_1 : Fin 1, (GlobalTheory.SeeSaw.Model.nLine D).gram i i_1 * D.host.xi0 ^ σ) = _
  simp only [Fin.sum_univ_one, nLine_gram, Pi.star_apply, star_pow, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, Place.xi, Place.pr, map_mul, map_neg, map_pow, map_one]
  ring

theorem pr_mul' {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
    (x y : D.host.E) : p.pr (x * y) = p.pr x * p.pr y := map_mul (p.π.comp (incA D)) x y

theorem place_proj_neg_xi_pow {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (n : ℕ) : p.pr ((-D.host.xi0) ^ n) = (-p.xi) ^ n :=
  (map_pow (p.π.comp (incA D)) _ n).trans (congrArg (· ^ n) (map_neg (p.π.comp (incA D)) _))

theorem neg_mul_neg_one_eq_of_eq {K : Type} [Field K] (y a S : K) (h : S = a) : -(y * a) * -1 = S * y := by rw [h]; ring

end NormalJac

open NormalJac in
set_option maxHeartbeats 1600000 in

theorem big_jacP : Big fun ch => JacP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch hsc => ?_⟩⟩
  clear hε hx hsc hch s
  intro t w hw p hp M hM j σ hj vN a ha c hc
  have h1 := ch.S.row t trivial w hw (j + 1) (by omega)
  have hm : (locGrid ch.G t w).m = D.R.m := rfl
  obtain rfl : c = 2 * σ := by
    have h2 := topRank_add (G := locGrid ch.G t w) one_le_sLen (j + 1)
    rw [hm] at h2; omega
  have hpr : ∀ x, p.pr x = algebraMap D.host.E (Kw w) x := fun x =>
    (hp.2.1 _).trans (Comparison₂.cpt_tmul w x)
  have hxi : p.xi ≠ 0 := by
    rw [Place.xi, hpr]; exact (map_ne_zero _).2 (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D)
  have hE : (epsV ch.G t w (D.R.m, j + 1)).val =
      diagonal fun q => if topRank (locGrid ch.G t w) (j + 1) + σ ≤ q.val then -1 else 1 := by
    by_cases hσ : σ = 0
    · subst hσ
      rw [epsV_eq_one _ _ (by omega), Units.val_one]
      ext q q'
      rw [Matrix.one_apply, diagonal_apply, if_neg (show ¬ (topRank (locGrid ch.G t w) (j + 1) + 0 ≤ q.val) by have := q.2; omega)]
    · have hodd : Odd (j + 1) := by
        obtain ⟨b, hb⟩ := D.R.m_even
        exact ⟨j / 2, by omega⟩
      rw [epsV_apply, if_pos (mem_idx.2 ⟨by omega, by omega⟩), sgnAt, GlobalTheory.SplitFlip.diagGL_val]
      congr 1
      funext q
      have e : (D.R.m - 1 - (j + 1)) / 2 = σ := by omega
      simp only [e, hodd, true_and]
      split_ifs <;> simp
  have h₁ : j + 1 < D.R.m := by omega
  have h₂ : D.R.m - 1 - (j + 1) = 2 * σ := by omega
  obtain ⟨T0, T1, T2⟩ : (mt _ a).map p.π * (rowJac ch.G (j + 1) h₁ σ h₂).i₀.map p.pr = (rowJac ch.G (j + 1) h₁ σ h₂).i₀.map p.pr ∧
      (mt _ a).map p.π * (rowJac ch.G (j + 1) h₁ σ h₂).e.map p.pr =
        ((rowJac ch.G (j + 1) h₁ σ h₂).e * diagonal fun a : Fin σ => (D.host.xi0 ^ a.1)⁻¹).map p.pr ∧
      (mt _ a).map p.π * (rowJac ch.G (j + 1) h₁ σ h₂).e'.map p.pr =
        ((rowJac ch.G (j + 1) h₁ σ h₂).e' * diagonal fun a : Fin σ => star (D.host.xi0 ^ a.1)).map p.pr := by
    rcases ha with ⟨rfl, rfl⟩ | ⟨δ, hδ, hδa⟩
    · refine ⟨?_, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
      rw [show mt (ch.G.V (Node.grid D.R.m (j + 1))) 1 = 1 by simp [Formalism.L2.Theta.mt], Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    · obtain ⟨e0, e1, e2⟩ := hδ.2.2 σ h₁ h₂
      have key : ∀ {n : ℕ} (X Y : Matrix (Fin (ch.G.V (Node.grid D.R.m (j + 1))).rank) (Fin n) D.host.E),
          HMul.hMul (mt _ δ) (X.map (incA D)) = Y.map (incA D) → (mt _ a).map p.π * X.map p.pr = Y.map p.pr := by
        intro n X Y h
        have := congrArg (fun Z => Z.map p.π) h
        simp only [Matrix.map_mul, Matrix.map_map] at this
        rw [hδa]
        exact this
      exact ⟨key _ _ e0, key _ _ e1, key _ _ e2⟩
  have hfl : ∀ {a c b : ℕ} (h : a + c = b) (x : Fin a), ((frame h (Sum.inl x)) : ℕ) = x := by intros; simp [frame]
  have hfr : ∀ {a c b : ℕ} (h : a + c = b) (q : Fin c), ((frame h (Sum.inr q)) : ℕ) = a + q := by intros; simp [frame]
  clear ha
  have T0' : ∀ {n : Type} [Fintype n] (Z : Matrix (Fin (ch.G.V (Node.top (j + 1))).rank) n (Kw w)), (mt _ a).map p.π * ((rowJac ch.G (j + 1) h₁ σ h₂).i₀.map p.pr * Z) =
      (rowJac ch.G (j + 1) h₁ σ h₂).i₀.map p.pr * Z := by
    intro n _ Z; rw [← Matrix.mul_assoc, T0]
  dsimp only [Place.IsJacFrame, jacAt]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro r x
    simp only [mvFr, frRow, frOf, frTop, submatrix_apply, id, hE, mul_diagonal]
    rw [if_neg (by rw [hfl]; omega), mul_one]
    refine (mul_col_eq _ _ ((rowJac ch.G (j + 1) h₁ σ h₂).i₀.map p.pr *
      (loc w (ch.S.βp (j + 1))).val.submatrix id (Fin.cast (topRank_eq ch.G t w h₁.le))) _ x (fun l => ?_) r).trans
      (congrFun (congrFun (T0' _) r) x)
    have e1 := congrFun (congrFun h1 l) (Sum.inl (Fin.cast (topRank_eq ch.G t w h₁.le) x))
    simp only [submatrix_apply, id, fromCols_apply_inl, mul_apply, Matrix.map_apply] at e1
    simp only [submatrix_apply, id, mul_apply, Matrix.map_apply, hpr]
    refine (congrArg _ (Fin.ext ?_)).trans e1
    simp [frame]
  · intro i jj hij r
    simp only [mvFr, frRow, frOf, submatrix_apply, id, hE, mul_diagonal]
    rw [if_neg (by rw [hfr]; omega), mul_one]
    refine (mul_col_eq _ _ ((rowJac ch.G (j + 1) h₁ σ h₂).e.map p.pr) _ i (fun l => ?_) r).trans ?_
    rotate_left
    · rw [T1]
      have hinv : ∀ x : D.host.E, p.π (incA D x⁻¹) = (p.π (incA D x))⁻¹ := fun x => map_inv₀ (p.π.comp (incA D)) x
      simp only [Matrix.map_apply, mul_diagonal, Place.pr, Place.xi, map_mul, hinv, map_pow]
      have hx : p.π (incA D D.host.xi0) ≠ 0 := hxi
      have e : p.π (incA D D.host.xi0) ^ σ = p.π (incA D D.host.xi0) ^ (σ - i.val) * p.π (incA D D.host.xi0) ^ i.val := by
        rw [← pow_add]; congr 1; omega
      rw [e]
      field_simp
    · have e1 := congrFun (congrFun h1 l) (Sum.inr (Fin.cast h₂.symm jj))
      simp only [submatrix_apply, id, fromCols_apply_inr, mul_diagonal, Matrix.map_apply] at e1
      rw [if_neg (Nat.succ_ne_zero j), pow_zero, mul_one, frameSign, if_neg (by simp only [Fin.val_cast]; omega), mul_one] at e1
      simp only [submatrix_apply, id, Matrix.map_apply, hpr]
      refine (congrArg _ (Fin.ext ?_)).trans (e1.trans ?_)
      · simp [frame, topRank_eq ch.G t w h₁.le]
      · have he : (rowJac ch.G (j + 1) h₁ σ h₂).e l i = (ch.G.rowDec (j + 1) h₁).a l (Fin.castLE (by omega) i) := rfl
        rw [he]
        exact congrArg _ (congrArg _ (Fin.ext (by simp; omega)))
  · intro i jj hij r
    simp only [mvFr, frRow, frOf, submatrix_apply, id, hE, mul_diagonal]
    rw [if_pos (by rw [hfr]; omega)]
    refine (congrArg (· * (-1)) (mul_col_eq _ _ (-((rowJac ch.G (j + 1) h₁ σ h₂).e'.map p.pr)) _ i (fun l => ?_) r)).trans ?_
    rotate_left
    · rw [Matrix.mul_neg, Matrix.neg_apply, T2, hz_besAt]
      simp only [Matrix.neg_apply, Matrix.map_apply, mul_diagonal, pr_mul', star_pow, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, place_proj_neg_xi_pow]
      have key := jacobiDualColumn_scalar_identity p.xi hxi i (σ - 1 - i)
      rw [show (i : ℕ) + 1 + (σ - 1 - i) = σ by omega] at key
      exact neg_mul_neg_one_eq_of_eq _ _ _ key
    · have e1 := congrFun (congrFun h1 l) (Sum.inr (Fin.cast h₂.symm jj))
      simp only [submatrix_apply, id, fromCols_apply_inr, mul_diagonal, Matrix.map_apply] at e1
      rw [if_neg (Nat.succ_ne_zero j), pow_zero, mul_one, frameSign, if_pos (by simp only [Fin.val_cast]; omega), mul_neg_one] at e1
      simp only [submatrix_apply, id, Matrix.neg_apply, Matrix.map_apply, hpr]
      refine (congrArg _ (Fin.ext ?_)).trans (e1.trans ?_)
      · simp [frame, topRank_eq ch.G t w h₁.le]
      · simp only [rowJac, jacDec, submatrix_apply, id]
        exact congrArg _ (congrArg _ (congrArg _ (Fin.ext (by simp; omega))))

end GlobalTheory.FlatPlace
