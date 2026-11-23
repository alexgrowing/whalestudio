import Formalism.HermitianCurvature.StatementHeads
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLift
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGFormJ

open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section step

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (j s : ℕ) (hj : j ≤ P.r)
  (w : List C.Letter) (h h' : C.LPt) (τ τ' : ℂ) (ha : D.ptSize (h ++ [(s, τ)]) = j)
  (ha' : D.ptSize (h' ++ [(s, τ')]) = j)

def Wl (ys : List ℝ) : ℂ :=
  KB.pairJ (p.form j hj w) ys (KB.slv p.T F j hj (KB.plusW ys w) (h ++ [(s, τ)]) ha)
    (KB.slv p.T F j hj (KB.minusW ys w) (h' ++ [(s, τ')]) ha')

theorem wl_step (hs : 1 ≤ s) (hsj : s ≤ j)
    (hSP : SlicePoly p.T F j hj (h ++ [(s, τ)]) ha) (hSP' : SlicePoly p.T F j hj (h' ++ [(s, τ')]) ha')
    (hLD : LiftDeg p.T F j s hj h τ ha) (hLD' : LiftDeg p.T F j s hj h' τ' ha')
    (hN : ∀ w' : List C.Letter, ∃ ε, ∀ a'', JC.NiceCoef (p.T.bs j) ε (KB.slv p.T F j hj w' (h ++ [(s, τ)]) ha a''))
    (hN' : ∀ w' : List C.Letter, ∃ ε, ∀ a'', JC.NiceCoef (p.T.bs j) ε (KB.slv p.T F j hj w' (h' ++ [(s, τ')]) ha' a''))
    (ys : List ℝ) :
    ∃ c : Fin (2 * (j - s) + s + 1) → ℂ,
      c (Fin.last (2 * (j - s) + s)) = ((-1 : ℂ) ^ (s - 1) * (τ⁻¹ - τ'⁻¹)) * Wl p F j s hj w h h' τ τ' ha ha' ys ∧
      ∀ y : ℝ, Wl p F j s hj w h h' τ τ' ha ha' (y :: ys) = ∑ q : Fin (2 * (j - s) + s + 1), ((y : ℂ) ^ (q : ℕ)) * c q := by
  classical
  set Ξ := p.form j hj w with hΞ
  have hΞ' : Ξ = D.formLev p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w := rfl
  obtain ⟨C0, hC0l, hC0n, hC0⟩ := hSP (KB.plusW ys w) true 0 0
  obtain ⟨D0, hD0l, hD0n, hD0⟩ := hSP' (KB.minusW ys w) false 1 0
  obtain ⟨E, hEn, hE0, hEt, hEJ⟩ := reduceJ p.T F j s hj h τ ha hsj hSP hLD (KB.plusW ys w) (hN _) true 0
  obtain ⟨E', hE'n, hE'0, hE't, hE'J⟩ := reduceJ p.T F j s hj h' τ' ha' hsj hSP' hLD' (KB.minusW ys w) (hN' _) false 1
  have dC0 : ∀ l, DecV (C0 l) := fun l => by obtain ⟨ε, hε⟩ := hC0n l; exact decV_of_nice hε
  have dD0 : ∀ l, DecV (D0 l) := fun l => by obtain ⟨ε, hε⟩ := hD0n l; exact decV_of_nice hε
  have dE : ∀ l, DecV (E l) := fun l => by obtain ⟨ε, hε⟩ := hEn l; exact decV_of_nice hε
  have dE' : ∀ l, DecV (E' l) := fun l => by obtain ⟨ε, hε⟩ := hE'n l; exact decV_of_nice hε
  have zL : ∀ (y' : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)), DecV y' →
      KB.pairJ Ξ ys 0 y' = 0 := by
    intro y' hy
    have := pairJ_sesq_left P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys 0 0 y' 1 decV_zero decV_zero hy
    rw [one_smul, add_zero, one_mul, ← hΞ'] at this
    linear_combination -this
  have zR : ∀ (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)), DecV x →
      KB.pairJ Ξ ys x 0 = 0 := by
    intro x hx
    have := pairJ_sesq_right P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys x 0 0 1 hx decV_zero decV_zero
    rw [one_smul, add_zero, map_one, one_mul, ← hΞ'] at this
    linear_combination -this

  have hX : ∀ y : ℝ, Wl p F j s hj w h h' τ τ' ha ha' (y :: ys) =
      ∑ l : Fin (j + 1), ∑ m : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) * ((y : ℂ) ^ (m : ℕ)) *
        (KB.pairJ Ξ ys (E l) (D0 m) - KB.pairJ Ξ ys (C0 l) (E' m)) := by
    intro y
    show KB.pairJ Ξ ys (fun e => KB.slv p.T F j hj ((true, y) :: KB.plusW ys w) (h ++ [(s, τ)]) ha (Fin.cons 1 e))
        (fun e => KB.slv p.T F j hj ((false, y + 1) :: KB.minusW ys w) (h' ++ [(s, τ')]) ha' (Fin.cons 0 e)) -
      KB.pairJ Ξ ys (fun e => KB.slv p.T F j hj ((true, y) :: KB.plusW ys w) (h ++ [(s, τ)]) ha (Fin.cons 0 e))
        (fun e => KB.slv p.T F j hj ((false, y + 1) :: KB.minusW ys w) (h' ++ [(s, τ')]) ha' (Fin.cons 1 e)) = _
    have hy0 : ((true, y) : C.Letter) = (true, y + 0) := by rw [add_zero]

    obtain ⟨εa, hεa⟩ := hN ((true, y) :: KB.plusW ys w)
    obtain ⟨εb, hεb⟩ := nice_lincomb (Bs := p.T.bs j) E hEn (fun l : Fin (j + 1) => (y : ℂ) ^ (l : ℕ))
    have t1 : KB.pairJ Ξ ys (fun e => KB.slv p.T F j hj ((true, y) :: KB.plusW ys w) (h ++ [(s, τ)]) ha (Fin.cons 1 e))
        (fun e => KB.slv p.T F j hj ((false, y + 1) :: KB.minusW ys w) (h' ++ [(s, τ')]) ha' (Fin.cons 0 e)) =
        KB.pairJ Ξ ys (∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • E l) (∑ m : Fin (j + 1), ((y : ℂ) ^ (m : ℕ)) • D0 m) := by
      rw [hΞ', pairJ_congrJ_left P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w (min εa εb) ys _
        (∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • E l) _
        (fun a => nice_mono (hεa _) (min_le_left _ _)) (fun a => nice_mono (hεb a) (min_le_right _ _))
        (fun a g hg => by have := hEJ y a g hg; rwa [add_zero] at this)]
      exact pairJ_formLev_congrGV p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys _ _ _ _ (eqGV_refl _) (hD0 y)
    have t2 : KB.pairJ Ξ ys (fun e => KB.slv p.T F j hj ((true, y) :: KB.plusW ys w) (h ++ [(s, τ)]) ha (Fin.cons 0 e))
        (fun e => KB.slv p.T F j hj ((false, y + 1) :: KB.minusW ys w) (h' ++ [(s, τ')]) ha' (Fin.cons 1 e)) =
        KB.pairJ Ξ ys (∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • C0 l) (∑ m : Fin (j + 1), ((y : ℂ) ^ (m : ℕ)) • E' m) := by
      rw [hΞ', pairJ_congrJ_right P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys _ _
        (∑ m : Fin (j + 1), ((y : ℂ) ^ (m : ℕ)) • E' m) (fun a g hg => hE'J y a g hg)]
      have h0 := hC0 y
      rw [add_zero] at h0
      exact pairJ_formLev_congrGV p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys _ _ _ _ h0 (eqGV_refl _)
    rw [t1, t2, hΞ', pairJ_sum_sum P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys _ _ _ _ E D0 dE dD0,
      pairJ_sum_sum P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys _ _ _ _ C0 E' dC0 dE', ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rw [conj_tpow]
    ring
  set N := 2 * (j - s) + s with hNdef
  have hNj : N = 2 * j - s := by omega
  set P1 : Fin (j + 1) → Fin (j + 1) → ℂ := fun l m => KB.pairJ Ξ ys (E l) (D0 m) with hP1
  set P2 : Fin (j + 1) → Fin (j + 1) → ℂ := fun l m => KB.pairJ Ξ ys (C0 l) (E' m) with hP2
  have P1z : ∀ l m : Fin (j + 1), j - s < (l : ℕ) → P1 l m = 0 := by
    intro l m hl; simp only [hP1]; rw [hE0 l hl]; exact zL _ (dD0 m)
  have P2z : ∀ l m : Fin (j + 1), j - s < (m : ℕ) → P2 l m = 0 := by
    intro l m hm; simp only [hP2]; rw [hE'0 m hm]; exact zR _ (dC0 l)
  have Xz : ∀ l m : Fin (j + 1), N < (l : ℕ) + m → P1 l m - P2 l m = 0 := by
    intro l m hlm
    have := l.isLt; have := m.isLt
    rw [P1z l m (by omega), P2z l m (by omega), sub_zero]
  refine ⟨fun q => ∑ l : Fin (j + 1), ∑ m : Fin (j + 1), if (l : ℕ) + m = q then P1 l m - P2 l m else 0, ?_,
    fun y => ?_⟩
  · dsimp only
    simp only [Fin.val_last]
    have hsplit : ∀ l m : Fin (j + 1), (if (l : ℕ) + m = N then P1 l m - P2 l m else 0) =
        (if (l : ℕ) + m = N then P1 l m else 0) - (if (l : ℕ) + m = N then P2 l m else 0) := by
      intro l m; split_ifs <;> simp
    simp only [hsplit, Finset.sum_sub_distrib]
    have hA : (∑ l : Fin (j + 1), ∑ m : Fin (j + 1), if (l : ℕ) + m = N then P1 l m else 0) =
        P1 ⟨j - s, by omega⟩ (Fin.last j) := by
      rw [Finset.sum_eq_single ⟨j - s, by omega⟩]
      · rw [Finset.sum_eq_single (Fin.last j)]
        · rw [if_pos (by simp; omega)]
        · intro m _ hm
          have := m.isLt
          have hm' : (m : ℕ) ≠ j := fun e => hm (Fin.ext (by simp [e]))
          rw [if_neg (by simp; omega)]
        · simp
      · intro l _ hl
        apply Finset.sum_eq_zero
        intro m _
        split_ifs with hlm
        · have := l.isLt; have := m.isLt
          have hl' : (l : ℕ) ≠ j - s := fun e => hl (Fin.ext (by simp [e]))
          exact P1z l m (by omega)
        · rfl
      · simp
    have hB : (∑ l : Fin (j + 1), ∑ m : Fin (j + 1), if (l : ℕ) + m = N then P2 l m else 0) =
        P2 (Fin.last j) ⟨j - s, by omega⟩ := by
      rw [Finset.sum_eq_single (Fin.last j)]
      · rw [Finset.sum_eq_single ⟨j - s, by omega⟩]
        · rw [if_pos (by simp; omega)]
        · intro m _ hm
          have := m.isLt
          have hm' : (m : ℕ) ≠ j - s := fun e => hm (Fin.ext (by simp [e]))
          rw [if_neg (by simp; omega)]
        · simp
      · intro l _ hl
        apply Finset.sum_eq_zero
        intro m _
        split_ifs with hlm
        · have := l.isLt; have := m.isLt
          have hl' : (l : ℕ) ≠ j := fun e => hl (Fin.ext (by simp [e]))
          exact P2z l m (by omega)
        · rfl
      · simp
    rw [hA, hB]
    have dXP : DecV (KB.slv p.T F j hj (KB.plusW ys w) (h ++ [(s, τ)]) ha) := by
      obtain ⟨ε, hε⟩ := hN (KB.plusW ys w); exact decV_of_nice hε
    have dXM : DecV (KB.slv p.T F j hj (KB.minusW ys w) (h' ++ [(s, τ')]) ha') := by
      obtain ⟨ε, hε⟩ := hN' (KB.minusW ys w); exact decV_of_nice hε
    have e1 : P1 ⟨j - s, by omega⟩ (Fin.last j) = cLift s τ true * Wl p F j s hj w h h' τ τ' ha ha' ys := by
      simp only [hP1]
      rw [hEt, hD0l, if_pos rfl]
      have := pairJ_sesq_left P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys 0
        (KB.slv p.T F j hj (KB.plusW ys w) (h ++ [(s, τ)]) ha)
        (KB.slv p.T F j hj (KB.minusW ys w) (h' ++ [(s, τ')]) ha') (cLift s τ true) decV_zero dXP dXM
      rw [zero_add, ← hΞ', zL _ dXM, zero_add] at this
      rw [this]; rfl
    have e2 : P2 (Fin.last j) ⟨j - s, by omega⟩ = conj (cLift s τ' false) * Wl p F j s hj w h h' τ τ' ha ha' ys := by
      simp only [hP2]
      rw [hE't, hC0l, if_pos rfl]
      have := pairJ_sesq_right P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys
        (KB.slv p.T F j hj (KB.plusW ys w) (h ++ [(s, τ)]) ha) 0
        (KB.slv p.T F j hj (KB.minusW ys w) (h' ++ [(s, τ')]) ha') (cLift s τ' false) dXP decV_zero dXM
      rw [zero_add, ← hΞ', zR _ dXP, zero_add] at this
      rw [this]; rfl
    rw [e1, e2]
    simp only [cLift, if_true, Bool.false_eq_true, if_false, map_mul, map_pow, map_neg, map_one, map_inv₀,
      Complex.conj_conj]
    ring
  · rw [hX y]
    have key : ∀ l m : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) * ((y : ℂ) ^ (m : ℕ)) *
        (KB.pairJ Ξ ys (E l) (D0 m) - KB.pairJ Ξ ys (C0 l) (E' m)) =
        ∑ q : Fin (2 * (j - s) + s + 1), ((y : ℂ) ^ (q : ℕ)) * (if (l : ℕ) + m = q then P1 l m - P2 l m else 0) := by
      intro l m
      by_cases hlm : (l : ℕ) + m ≤ N
      · rw [Finset.sum_eq_single ⟨(l : ℕ) + m, by omega⟩]
        · rw [if_pos rfl, pow_add]
        · intro q _ hq
          rw [if_neg, mul_zero]
          intro e
          exact hq (Fin.ext e.symm)
        · simp
      · have hz := Xz l m (by omega)
        simp only [hP1, hP2] at hz
        rw [hz, mul_zero]
        symm
        apply Finset.sum_eq_zero
        intro q _
        rw [if_neg, mul_zero]
        have := q.isLt
        omega
    simp only [key]
    refine (Finset.sum_congr rfl (fun l _ => Finset.sum_comm)).trans ?_
    refine Finset.sum_comm.trans ?_
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.mul_sum]

end step

section final

theorem degLift_of (hL : LiftDegAll) : KB.DegLift := by
  intro Wp Wq _ _ _ _ _ _ P p F j s hj w h h' t t' ha ha' K grid hF hgrid
  have hsz : D.ptSize (h ++ [(s, t)]) = D.ptSize h + s := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h s t
  have hs1 : 1 ≤ s := (ha.1 (s, t) (by simp)).1
  have hsj : s ≤ j := by rw [← ha.2, hsz]; omega
  have hN : ∀ (q : C.LPt) (hq : D.IsLocPt q j) (w' : List C.Letter), ∃ ε, ∀ a'',
      JC.NiceCoef (p.T.bs j) ε (KB.slv p.T F j hj w' q hq.2 a'') := fun q hq w' =>
    nice_vec_of_cpt (p.T.bs j) (fun a'' => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj w' q hq hF a'')
  set W : ℕ → (Fin K → ℝ) → ℂ := fun m y => Wl p F j s hj w h h' t t' ha.2 ha'.2 (Lst K m y) with hW
  have hPS : F7.PolyStep K (2 * (j - s) + s) (fun _ => (-1 : ℂ) ^ (s - 1) * (t⁻¹ - t'⁻¹)) W := by
    intro a y
    obtain ⟨c, hc, hcs⟩ := wl_step p F j s hj w h h' t t' ha.2 ha'.2 hs1 hsj
      (slicePolyAll Wp Wq P p F hF j hj _ ha) (slicePolyAll Wp Wq P p F hF j hj _ ha')
      (hL Wp Wq P p F hF j s hj h t ha) (hL Wp Wq P p F hF j s hj h' t' ha') (hN _ ha) (hN _ ha') (Lst K a y)
    refine ⟨c, ?_, fun u => ?_⟩
    · rw [hc, smul_eq_mul]
    · simp only [hW]
      rw [lst_succ, hcs u]
      simp only [smul_eq_mul]
  have hinj : ∀ a, Function.Injective (fun i => grid (Fin.rev a) i) := fun a => hgrid _
  have hE := Formalism.FourierDecayAlt.P.extract_K_bound ℂ K (2 * (j - s) + s) (fun _ => (-1 : ℂ) ^ (s - 1) * (t⁻¹ - t'⁻¹)) W
    (fun a => grid (Fin.rev a)) hPS hinj (fun _ => 0)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hE
  have hW0 : W 0 (fun _ => 0) = p.RR F j w (h ++ [(s, t)]) (h' ++ [(s, t')]) := by
    simp only [hW, KB.Pl.RR, D.RRplace, dif_pos (And.intro ha ha'), dif_pos hj]
    rfl
  rw [hW0] at hE
  rw [hE]
  refine Fintype.sum_equiv ((Fin.revPerm).arrowCongr (Equiv.refl _)) _ _ (fun n => ?_)
  simp only [hW, smul_eq_mul]
  rw [lst_full]
  have e1 : (fun b : Fin K => grid (Fin.rev (Fin.rev b)) (n (Fin.rev b))) =
      fun b => grid b ((Fin.revPerm.arrowCongr (Equiv.refl (Fin (2 * (j - s) + s + 1)))) n b) := by
    funext b
    simp [Equiv.arrowCongr_apply, Fin.revPerm]
  have e2 : (∏ a : Fin K, F7.lagCo (grid (Fin.rev a)) (n a)) =
      ∏ a : Fin K, F7.lagCo (grid a) ((Fin.revPerm.arrowCongr (Equiv.refl (Fin (2 * (j - s) + s + 1)))) n a) := by
    refine Fintype.prod_equiv Fin.revPerm _ _ (fun a => ?_)
    simp [Equiv.arrowCongr_apply, Fin.revPerm]
  rw [e1, e2]
  rfl

end final

end Formalism.FourierDecayAlt.P.PBG
