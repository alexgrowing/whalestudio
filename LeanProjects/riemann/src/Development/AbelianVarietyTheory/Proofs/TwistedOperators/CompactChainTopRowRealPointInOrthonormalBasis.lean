import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqConjOfInFrame

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowReal

theorem mul_adaptedFrame_of_blocks {N r c N' : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (F : Matrix (Fin N) (Fin r) ℂ)
    (O Mmm : Matrix (Fin r) (Fin r) ℂ) (Zc : Matrix (Fin N) (Fin 1) ℂ) (y : Matrix (Fin c) (Fin c) ℂ)
    (hr : r = c) (hc : c + 1 = N') (hN : N = N') (hO : IsUnit O.det)
    (h1 : A * F = F * Mmm) (h2 : Mmm = O * y.submatrix (Fin.cast hr) (Fin.cast hr) * O⁻¹) (h3 : A * Zc = Zc) :
    A * Matrix.of (fun a k => Sum.elim (fun b : Fin c => (F * O) a (Fin.cast hr.symm b)) (fun _ : Fin 1 => Zc a 0)
      ((finSumFinEquiv.trans (finCongr hc)).symm (Fin.cast hN k))) =
    Matrix.of (fun a k => Sum.elim (fun b : Fin c => (F * O) a (Fin.cast hr.symm b)) (fun _ : Fin 1 => Zc a 0)
      ((finSumFinEquiv.trans (finCongr hc)).symm (Fin.cast hN k))) *
      (Matrix.reindex (finSumFinEquiv.trans (finCongr hc)) (finSumFinEquiv.trans (finCongr hc))
        (Matrix.fromBlocks y 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))).submatrix (Fin.cast hN) (Fin.cast hN) := by
  subst hr hc hN
  set e := finSumFinEquiv (m := r) (n := 1)
  have hT : Matrix.of (fun a k => Sum.elim (fun b : Fin r => (F * O) a (Fin.cast rfl b)) (fun _ : Fin 1 => Zc a 0)
      ((e.trans (finCongr rfl)).symm (Fin.cast rfl k))) = (Matrix.fromCols (F * O) Zc).submatrix id e.symm := by
    ext a k
    simp only [Matrix.of_apply, Fin.cast_eq_self, Matrix.submatrix_apply, id]
    rcases h : e.symm k with b | b
    · simp [h, Matrix.fromCols]
    · simp [h, Matrix.fromCols, Subsingleton.elim b 0]
  have hK : (Matrix.reindex (e.trans (finCongr rfl)) (e.trans (finCongr rfl))
        (Matrix.fromBlocks y 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))).submatrix (Fin.cast rfl) (Fin.cast rfl) =
      (Matrix.fromBlocks y 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ)).submatrix e.symm e.symm := by
    ext a k
    simp [Matrix.reindex_apply]
  rw [hT, hK, Matrix.submatrix_mul_equiv]
  have hL : A * (Matrix.fromCols (F * O) Zc).submatrix id e.symm = (A * Matrix.fromCols (F * O) Zc).submatrix id e.symm := by
    ext a k
    rfl
  rw [hL, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks, h3]
  congr 2
  · rw [← Matrix.mul_assoc, h1, h2]
    simp only [Fin.cast_eq_self, Matrix.submatrix_id_id, Matrix.mul_zero, add_zero, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hO, Matrix.mul_one]
    congr 2
  · simp

theorem ptTop_inOnb : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) (g : Gc D.what₂.Tau (GlobalTheory.RowReal.rowSizes D)) (n : Fin (D.R.m + 1)),
    ((n : ℕ) = D.R.m → ∀ τ, W.onb (.top D.R.m) τ = GlobalTheory.RowReal.topFrame W τ) → ∀ τ,
    (W.onb (.top n) τ)⁻¹ * compAt W.θ τ (mt _ (GlobalTheory.RowReal.ptTop W g n)) * W.onb (.top n) τ =
      (rowComp (GlobalTheory.RowReal.rowSizes D) g n τ).1.submatrix (Fin.cast (GlobalTheory.RowReal.rank_top G (Nat.lt_succ_iff.1 n.2)))
        (Fin.cast (GlobalTheory.RowReal.rank_top G (Nat.lt_succ_iff.1 n.2))) := by
  intro D T L sc G μ0 hL W g n hn τ
  by_cases h : (n : ℕ) < D.R.m
  · have hP : PosOnb W (.top (⟨n, h⟩ : Fin D.R.m)) := posOnb_of_defNode W μ0 hL (X := .top (⟨n, h⟩ : Fin D.R.m)) h.le
    have hd : IsUnit (W.onb (.top (⟨n, h⟩ : Fin D.R.m)) τ).det := Matrix.isUnit_det_of_left_inverse (hP τ)
    have e1 := compAt_kappa_fst g ⟨n, h⟩ hP τ
    have e2 : ∀ k : Fin D.R.m, (rowComp (rowSizes D) g (Fin.castSucc k) τ).1 = (g.1 k τ).1 := fun k => by
      simp only [rowComp, MonoidHom.coe_mk, OneHom.coe_mk]
      exact congrArg (fun x => (x τ).1) (Fin.snoc_castSucc (α := fun j : Fin ((rowSizes D).m + 1) => UG D.what₂.Tau ((rowSizes D).nR j))
        (embed (rowSizes D).nC_succ (g.2 (Fin.last _))) g.1 k)
    obtain ⟨k, rfl⟩ : ∃ k : Fin D.R.m, n = Fin.castSucc k := ⟨⟨n, h⟩, Fin.ext rfl⟩
    rw [ptTop_lt W g h]
    erw [e1]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]
    erw [e2 k]
    rfl
  · have hm : (n : ℕ) = D.R.m := by have := n.2; omega
    obtain rfl : n = Fin.last D.R.m := Fin.ext hm
    have hF := hn rfl
    have hPt : PosOnb W (.top D.R.m) := posOnb_of_defNode W μ0 hL (X := .top D.R.m) le_rfl
    have hPg : PosOnb W (.grid (Fin.last D.R.m : Fin (D.R.m + 1)) D.R.m) :=
      posOnb_of_defNode W μ0 hL (X := .grid (Fin.last D.R.m : Fin (D.R.m + 1)) D.R.m) ⟨Nat.lt_succ_iff.1 (Fin.last D.R.m).2, rfl⟩
    have hdT : IsUnit (topFrame W τ).det := by
      rw [← hF τ]; exact Matrix.isUnit_det_of_left_inverse (hPt τ)
    have hdO : IsUnit (W.onb (.grid D.R.m D.R.m) τ).det := Matrix.isUnit_det_of_left_inverse (hPg τ)
    have h1 : compAt W.θ τ (mt (G.V (.top D.R.m)) (kappaTop W g)) *
        (frameMat (G.V (.top D.R.m)) (G.V (.grid D.R.m D.R.m)) G.sp.topDec.ι).map (tauE D τ) =
        (frameMat (G.V (.top D.R.m)) (G.V (.grid D.R.m D.R.m)) G.sp.topDec.ι).map (tauE D τ) *
          compAt W.θ τ (mt (G.V (.grid D.R.m D.R.m)) ((kappa W g).2 (Fin.last D.R.m))) := (archM_kappaTop W g τ).1
    have h3 : compAt W.θ τ (mt (G.V (.top D.R.m)) (kappaTop W g)) * G.sp.topDec.a.map (tauE D τ) =
        G.sp.topDec.a.map (tauE D τ) := (archM_kappaTop W g τ).2
    have h2 : compAt W.θ τ (mt (G.V (.grid D.R.m D.R.m)) ((kappa W g).2 (Fin.last D.R.m))) =
        W.onb (.grid D.R.m D.R.m) τ * (g.2 (Fin.last D.R.m) τ).1.submatrix (Fin.cast (rank_gridM G (i := D.R.m) le_rfl))
          (Fin.cast (rank_gridM G (i := D.R.m) le_rfl)) * (W.onb (.grid D.R.m D.R.m) τ)⁻¹ :=
      compAt_kappa_snd g (Fin.last D.R.m) hPg τ
    have hA := mul_adaptedFrame_of_blocks (c := (rowSizes D).nC D.R.m) _ _ _ _ _
      ((g.2 (Fin.last D.R.m) τ).1 : Matrix (Fin ((rowSizes D).nC D.R.m)) (Fin ((rowSizes D).nC D.R.m)) ℂ)
      (rank_gridM G (i := D.R.m) le_rfl) (rowSizes D).nC_succ (rank_top G (j := D.R.m) le_rfl) hdO h1 h2 h3
    have key : (topFrame W τ)⁻¹ * compAt W.θ τ (mt _ (kappaTop W g)) * topFrame W τ =
        (embed (rowSizes D).nC_succ (g.2 (Fin.last D.R.m)) τ).1.submatrix
          (Fin.cast (rank_top G (j := D.R.m) le_rfl)) (Fin.cast (rank_top G (j := D.R.m) le_rfl)) := by
      have hA' : compAt W.θ τ (mt _ (kappaTop W g)) * topFrame W τ = topFrame W τ *
          (embed (rowSizes D).nC_succ (g.2 (Fin.last D.R.m)) τ).1.submatrix
            (Fin.cast (rank_top G (j := D.R.m) le_rfl)) (Fin.cast (rank_top G (j := D.R.m) le_rfl)) := hA
      rw [Matrix.mul_assoc, hA', ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdT, Matrix.one_mul]
    have hlast : rowComp (rowSizes D) g (Fin.last D.R.m) = embed (rowSizes D).nC_succ (g.2 (Fin.last D.R.m)) := by
      simp only [rowComp, MonoidHom.coe_mk, OneHom.coe_mk]; exact Fin.snoc_last (α := fun j : Fin ((rowSizes D).m + 1) => UG D.what₂.Tau ((rowSizes D).nR j)) _ _
    rw [show ptTop W g ((Fin.last D.R.m : Fin (D.R.m + 1)) : ℕ) = kappaTop W g from ptTop_m W g]
    erw [hlast, hF τ]
    exact key

end GlobalTheory.RowReal
