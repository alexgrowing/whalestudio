import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MemLevelZeroOfMemGroup
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGDegLift
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.XiExistsOfBesselXiIntegrable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegrableWeightNormSq

namespace GlobalTheory.LiftBoundCpt

noncomputable section

open Matrix Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG Formalism.REAL Formalism.QuantumDeterminants
open scoped ComplexConjugate

section step

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (j s : ℕ) (hj : j ≤ P.r)
  (w : List C.Letter) (h h' : C.LPt) (τ τ' : ℂ) (ha : D.ptSize (h ++ [(s, τ)]) = j)
  (ha' : D.ptSize (h' ++ [(s, τ')]) = j)

theorem lift_pairing_poly (hXi : B.XiExists) (hs : 1 ≤ s) (hsj : s ≤ j)
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
    have := FormsFromXi.pairing_add_smul_left hXi P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys 0 0 y' 1 decV_zero decV_zero hy
    rw [one_smul, add_zero, one_mul, ← hΞ'] at this
    linear_combination -this
  have zR : ∀ (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)), DecV x →
      KB.pairJ Ξ ys x 0 = 0 := by
    intro x hx
    have := FormsFromXi.pairing_add_smul_right hXi P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys x 0 0 1 hx decV_zero decV_zero
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
    rw [t1, t2, hΞ', FormsFromXi.pairing_sum_sum hXi P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys _ _ _ _ E D0 dE dD0,
      FormsFromXi.pairing_sum_sum hXi P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys _ _ _ _ C0 E' dC0 dE', ← Finset.sum_sub_distrib]
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
      have := FormsFromXi.pairing_add_smul_left hXi P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys 0
        (KB.slv p.T F j hj (KB.plusW ys w) (h ++ [(s, τ)]) ha)
        (KB.slv p.T F j hj (KB.minusW ys w) (h' ++ [(s, τ')]) ha') (cLift s τ true) decV_zero dXP dXM
      rw [zero_add, ← hΞ', zL _ dXM, zero_add] at this
      rw [this]; rfl
    have e2 : P2 (Fin.last j) ⟨j - s, by omega⟩ = conj (cLift s τ' false) * Wl p F j s hj w h h' τ τ' ha ha' ys := by
      simp only [hP2]
      rw [hE't, hC0l, if_pos rfl]
      have := FormsFromXi.pairing_add_smul_right hXi P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys
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

theorem degLift_of_liftDeg (hXi : B.XiExists) (hL : LiftDegAll) : KB.DegLift := by
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
    obtain ⟨c, hc, hcs⟩ := lift_pairing_poly p F j s hj w h h' t t' ha.2 ha'.2 hXi hs1 hsj
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

theorem degLift_of_xiExists (hXi : B.XiExists) : KB.DegLift :=
  degLift_of_liftDeg hXi (liftDegAll_of left_fubini_normalized_tower LeftFubiniLemmas.normal_form_left_hypothesis right_average_smooth_comm)

end

end GlobalTheory.LiftBoundCpt

namespace GlobalTheory.LiftBoundCpt

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx5 Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal ComplexOrder

noncomputable section

open Classical

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem form_cauchySchwarz (hXi : B.XiExists) (hA : P5.ThmPActualCpt) (hFP : PBL.FormPosCpt) (p : KB.Pl P Wp Wq) (j : ℕ)
    (hj : j ≤ P.r) (w : List C.Letter) (hw : KB.CutWord P p.l0 w)
    (x y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hx : PBL.CV (p.T.bs j) x) (hy : PBL.CV (p.T.bs j) y) :
    ‖p.form j hj w x y‖ ^ 2 ≤ (p.form j hj w x x).re * (p.form j hj w y y).re := by
  let VT := Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)
  have hadd : ∀ x y : VT, PBL.CV (p.T.bs j) x → PBL.CV (p.T.bs j) y → PBL.CV (p.T.bs j) (x + y) :=
    fun _ _ => PBL.cv_add
  have hsmul : ∀ (c : ℂ) (x : VT), PBL.CV (p.T.bs j) x → PBL.CV (p.T.bs j) (c • x) := fun c _ => PBL.cv_smul c
  have hl : ∀ (x₁ x₂ y : VT) (c : ℂ), PBL.CV (p.T.bs j) x₁ → PBL.CV (p.T.bs j) x₂ → PBL.CV (p.T.bs j) y →
      p.form j hj w (x₁ + c • x₂) y = p.form j hj w x₁ y + c * p.form j hj w x₂ y :=
    fun x₁ x₂ y c h₁ h₂ h₃ => by
      obtain ⟨ε, -, a, b, d⟩ := PBL.exists_norm_bound_three_families h₁ h₂ h₃
      exact FormsFromXi.formLev_add_smul_left hXi P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w x₁ x₂ y c
        (PBG.decV_of_nice a) (PBG.decV_of_nice b) (PBG.decV_of_nice d)
  have hr : ∀ (x y₁ y₂ : VT) (c : ℂ), PBL.CV (p.T.bs j) x → PBL.CV (p.T.bs j) y₁ → PBL.CV (p.T.bs j) y₂ →
      p.form j hj w x (y₁ + c • y₂) = p.form j hj w x y₁ + conj c * p.form j hj w x y₂ :=
    fun x y₁ y₂ c h₁ h₂ h₃ => by
      obtain ⟨ε, -, a, b, d⟩ := PBL.exists_norm_bound_three_families h₁ h₂ h₃
      exact FormsFromXi.formLev_add_smul_right hXi P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w x y₁ y₂ c
        (PBG.decV_of_nice a) (PBG.decV_of_nice b) (PBG.decV_of_nice d)
  have hp : ∀ x : VT, PBL.CV (p.T.bs j) x → 0 ≤ p.form j hj w x x :=
    fun x hx => hFP hA Wp Wq P p j hj w hw x hx
  refine cs_abs (PBL.CV (p.T.bs j)) (p.form j hj w) hadd hsmul hl hr hp x y hx hy ?_
  exact PBL.herm_of_nonneg (PBL.CV (p.T.bs j)) (p.form j hj w) PBL.cv_zero hadd hsmul hl hr hp x y hx hy

theorem form_re_nonneg_cpt (hA : P5.ThmPActualCpt) (hFP : PBL.FormPosCpt) (p : KB.Pl P Wp Wq) (j : ℕ)
    (hj : j ≤ P.r) (w : List C.Letter) (hw : KB.CutWord P p.l0 w)
    (x : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (hx : PBL.CV (p.T.bs j) x) :
    0 ≤ (p.form j hj w x x).re :=
  (Complex.nonneg_iff.1 (hFP hA Wp Wq P p j hj w hw x hx)).1

theorem slice_cv (p : KB.Pl P Wp Wq) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef p.T.base F) (j : ℕ)
    (hj : j ≤ P.r) (w : List C.Letter) (a : C.LPt) (ha : D.IsLocPt a j) :
    PBL.CV (p.T.bs j) (KB.slv p.T F j hj w a ha.2) :=
  fun e => slice_compact_support_coefficient _ _ P p F j hj w a ha hF e

theorem liftBound_at (hXi : B.XiExists) (hA : P5.ThmPActualCpt) (hSS : KB.SizeStdCpt) (hFP : PBL.FormPosCpt) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ)
    (hF : KB.CptCoef p.T.base F) (hnn : ∀ y, 0 < nn y) (hgrid : LiftGrid p nn Y Λ K N) :
    TBB.KernelArgumentHypothesisScalar p nn F Y Λ K N := by
  intro b s hb hs hbs h hh w hw hN t t' ht ht'
  set j := b + s - 1 with hjdef
  have hj : j ≤ P.r := hbs
  obtain ⟨grid, hinj, hY, hcut, hsum⟩ := hgrid b s hb hs hbs w hw hN
  simp only [ysOf] at hsum hcut
  have ha := li_locPt h b s t hb hs hh ht
  have ha' := li_locPt h b s t' hb hs hh ht'
  set u := Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t)])) with hudef
  set u' := Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t')])) with hu'def
  set n := TBB.normC nn w with hndef
  have hn : 0 < n := normC_pos nn hnn w
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hu' : 0 ≤ u' := Real.sqrt_nonneg _
  have hα : 0 ≤ u * u' / n := by positivity
  set x := KB.slv p.T F j hj w _ ha.2 with hxdef
  set x' := KB.slv p.T F j hj w _ ha'.2 with hx'def
  have hNP : ‖TBB.NP p nn F j w (h ++ [(s, t)]) (h ++ [(s, t')])‖ = (u * u' / n) * ‖p.form j hj w x x'‖ := by
    rw [li_np p nn F j hj w _ _ ha ha', norm_mul, Complex.norm_real, Real.norm_of_nonneg hα]

  have c1 : ‖TBB.NP p nn F j w (h ++ [(s, t)]) (h ++ [(s, t')])‖ ≤
      (TBB.Ew p nn F j w (h ++ [(s, t)]) + TBB.Ew p nn F j w (h ++ [(s, t')])) / 2 := by
    have hx : PBL.CV (p.T.bs j) x := slice_cv p hF j hj w _ ha
    have hx' : PBL.CV (p.T.bs j) x' := slice_cv p hF j hj w _ ha'
    have hcs := form_cauchySchwarz hXi hA hFP p j hj w hw.1 x x' hx hx'
    have hf := form_re_nonneg_cpt hA hFP p j hj w hw.1 x hx
    have hf' := form_re_nonneg_cpt hA hFP p j hj w hw.1 x' hx'
    have key := scal_cs (u * u' / n) (u * u / n) (u' * u' / n) ‖p.form j hj w x x'‖ 1 1 1
      (p.form j hj w x x).re (p.form j hj w x' x').re hα (by field_simp) (by positivity) (by positivity)
      one_pos one_pos one_pos (norm_nonneg _) hf hf' (by rw [mul_one]; exact hcs)
    rw [hNP, li_ew p nn F j hj w _ ha, li_ew p nn F j hj w _ ha']
    refine key.trans ?_
    simp only [mul_one, div_one, Real.sqrt_one, one_mul]
    exact sqrt_mul_le_avg _ _ (mul_nonneg (by positivity) hf) (mul_nonneg (by positivity) hf')

  have hEnn : ∀ (w' : List C.Letter) (a : C.LPt) (ha : D.IsLocPt a j), KB.CutWord P p.l0 w' →
      0 ≤ TBB.Ew p nn F j w' a := by
    intro w' a ha hw'
    rw [li_ew p nn F j hj w' a ha]
    have hxa := slice_cv p hF j hj w' a ha
    exact mul_nonneg (div_nonneg (mul_self_nonneg _) (normC_pos nn hnn w').le)
      (form_re_nonneg_cpt hA hFP p j hj w' hw' _ hxa)

  have hdeg := degLift_of_xiExists hXi Wp Wq P p F j s hj w h h t t' ha ha' K grid hF hinj
  rw [PBL.rr_eq_form p F j hj w _ _ ha ha'] at hdeg
  have hper : ∀ m : Fin K → Fin (2 * (j - s) + s + 1),
      (u * u' / n) * ‖KB.pairJ (p.form j hj w) (List.ofFn fun a => grid a (m a))
          (KB.slv p.T F j hj (KB.plusW (List.ofFn fun a => grid a (m a)) w) _ ha.2)
          (KB.slv p.T F j hj (KB.minusW (List.ofFn fun a => grid a (m a)) w) _ ha'.2)‖ ≤
        Real.sqrt (((List.ofFn fun a => grid a (m a)).map nn).prod *
          ((List.ofFn fun a => grid a (m a)).map fun y => nn (y + 1)).prod /
          ((List.ofFn fun a => grid a (m a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod) *
        ((TBB.Ew p nn F j (KB.plusW (List.ofFn fun a => grid a (m a)) w) (h ++ [(s, t)]) +
          TBB.Ew p nn F j (KB.minusW (List.ofFn fun a => grid a (m a)) w) (h ++ [(s, t')])) / 2) := by
    intro m
    set ys := List.ofFn fun a => grid a (m a) with hys
    obtain ⟨hqpos, hSSm⟩ := hSS hA Wp Wq P p j hj w ys (hcut m).1 (hcut m).2.1 (hcut m).2.2
    have hx := slice_cv p hF j hj (KB.plusW ys w) _ ha
    have hx' := slice_cv p hF j hj (KB.minusW ys w) _ ha'
    have hcs := hSSm _ _ hx hx'
    set fp := (p.form j hj (KB.plusW ys w) (KB.slv p.T F j hj (KB.plusW ys w) (h ++ [(s, t)]) ha.2)
      (KB.slv p.T F j hj (KB.plusW ys w) (h ++ [(s, t)]) ha.2)).re with hfp
    set fm := (p.form j hj (KB.minusW ys w) (KB.slv p.T F j hj (KB.minusW ys w) (h ++ [(s, t')]) ha'.2)
      (KB.slv p.T F j hj (KB.minusW ys w) (h ++ [(s, t')]) ha'.2)).re with hfm
    have hf : 0 ≤ fp := form_re_nonneg_cpt hA hFP p j hj _ (hcut m).1 _ hx
    have hf' : 0 ≤ fm := form_re_nonneg_cpt hA hFP p j hj _ (hcut m).2.1 _ hx'
    have hq : 0 < (ys.map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod := by
      refine List.prod_pos fun z hz => ?_
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
      exact hqpos y hy
    have hQ₁ := prod_map_pos nn hnn ys
    have hQ₂ := prod_map_pos (fun y => nn (y + 1)) (fun y => hnn _) ys
    have key := scal_cs (u * u' / n) (u * u / n) (u' * u' / n) _ _ _ _ fp fm hα (by field_simp) (by positivity)
      (by positivity) hq hQ₁ hQ₂ (norm_nonneg _) hf hf' hcs
    refine key.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    rw [li_ew p nn F j hj _ _ ha, li_ew p nn F j hj _ _ ha', normC_plusW, normC_minusW, ← hfp, ← hfm]
    have e₁ : u * u / n * fp / (ys.map nn).prod = u * u / ((ys.map nn).prod * n) * fp := by
      field_simp
    have e₂ : u' * u' / n * fm / (ys.map fun y => nn (y + 1)).prod =
        u' * u' / ((ys.map fun y => nn (y + 1)).prod * n) * fm := by
      field_simp
    rw [e₁, e₂]
    exact sqrt_mul_le_avg _ _ (by positivity) (by positivity)
  set g : (Fin K → Fin (2 * (j - s) + s + 1)) → ℝ := fun m =>
    (TBB.Ew p nn F j (KB.plusW (List.ofFn fun a => grid a (m a)) w) (h ++ [(s, t)]) +
      TBB.Ew p nn F j (KB.minusW (List.ofFn fun a => grid a (m a)) w) (h ++ [(s, t')])) / 2 with hg
  have hg0 : ∀ m, 0 ≤ g m := fun m =>
    div_nonneg (add_nonneg (hEnn _ _ ha (hcut m).1) (hEnn _ _ ha' (hcut m).2.1)) zero_le_two
  obtain ⟨m₀, hm₀⟩ := sum_le_max (fun m => |∏ a, F7.lagCo (grid a) (m a)| *
      Real.sqrt (((List.ofFn fun a => grid a (m a)).map nn).prod *
        ((List.ofFn fun a => grid a (m a)).map fun y => nn (y + 1)).prod /
        ((List.ofFn fun a => grid a (m a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod))
    g (Λ ^ K) (fun m => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hg0 hsum
  have c2 : ‖t⁻¹ - t'⁻¹‖ ^ K * ‖TBB.NP p nn F j w (h ++ [(s, t)]) (h ++ [(s, t')])‖ ≤ Λ ^ K * g m₀ := by
    have hn1 : ‖((-1 : ℂ) ^ (s - 1) * (t⁻¹ - t'⁻¹)) ^ K * p.form j hj w x x'‖ =
        ‖t⁻¹ - t'⁻¹‖ ^ K * ‖p.form j hj w x x'‖ := by
      rw [norm_mul, norm_pow, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [hNP]
    calc ‖t⁻¹ - t'⁻¹‖ ^ K * (u * u' / n * ‖p.form j hj w x x'‖)
        = u * u' / n * ‖((-1 : ℂ) ^ (s - 1) * (t⁻¹ - t'⁻¹)) ^ K * p.form j hj w x x'‖ := by rw [hn1]; ring
      _ ≤ u * u' / n * ∑ m : Fin K → Fin (2 * (j - s) + s + 1), ‖((∏ a, F7.lagCo (grid a) (m a) : ℝ) : ℂ)‖ *
          ‖KB.pairJ (p.form j hj w) (List.ofFn fun a => grid a (m a))
            (KB.slv p.T F j hj (KB.plusW (List.ofFn fun a => grid a (m a)) w) _ ha.2)
            (KB.slv p.T F j hj (KB.minusW (List.ofFn fun a => grid a (m a)) w) _ ha'.2)‖ := by
          refine mul_le_mul_of_nonneg_left ?_ hα
          rw [hdeg]
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun m _ => norm_mul _ _
      _ = ∑ m : Fin K → Fin (2 * (j - s) + s + 1), |∏ a, F7.lagCo (grid a) (m a)| *
          (u * u' / n * ‖KB.pairJ (p.form j hj w) (List.ofFn fun a => grid a (m a))
            (KB.slv p.T F j hj (KB.plusW (List.ofFn fun a => grid a (m a)) w) _ ha.2)
            (KB.slv p.T F j hj (KB.minusW (List.ofFn fun a => grid a (m a)) w) _ ha'.2)‖) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Complex.norm_real, Real.norm_eq_abs]
          ring
      _ ≤ ∑ m : Fin K → Fin (2 * (j - s) + s + 1), |∏ a, F7.lagCo (grid a) (m a)| *
          (Real.sqrt (((List.ofFn fun a => grid a (m a)).map nn).prod *
            ((List.ofFn fun a => grid a (m a)).map fun y => nn (y + 1)).prod /
            ((List.ofFn fun a => grid a (m a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod) *
            g m) :=
          Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (hper m) (abs_nonneg _)
      _ = ∑ m : Fin K → Fin (2 * (j - s) + s + 1), |∏ a, F7.lagCo (grid a) (m a)| *
          Real.sqrt (((List.ofFn fun a => grid a (m a)).map nn).prod *
            ((List.ofFn fun a => grid a (m a)).map fun y => nn (y + 1)).prod /
            ((List.ofFn fun a => grid a (m a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod) *
            g m := Finset.sum_congr rfl fun m _ => by ring
      _ ≤ Λ ^ K * g m₀ := hm₀
  rcases mn_pick Λ ‖t⁻¹ - t'⁻¹‖ _ _ (g m₀) K (norm_nonneg _) c1 (fun _ => c2) with hc | hc
  · exact ⟨w, w, isExt_self P p.l0 Y N K w hw (by omega), isExt_self P p.l0 Y N K w hw (by omega), hc⟩
  · refine ⟨KB.plusW (List.ofFn fun a => grid a (m₀ a)) w, KB.minusW (List.ofFn fun a => grid a (m₀ a)) w,
      isExt_plusW P p.l0 Y N K w _ hN (by simp) (ysOf_mem grid hY m₀) (hcut m₀).1,
      isExt_minusW P p.l0 Y N K w _ hN (by simp) (ysOf_mem grid hY m₀) (hcut m₀).2.1, hc⟩

end

theorem liftBound_of_xiExists (hXi : B.XiExists) : P5.ThmPActualCpt → KB.SizeStdCpt → PBL.FormPosCpt →
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ),
      KB.CptCoef p.T.base F → (∀ y, 0 < nn y) → TBBx5.LiftGrid p nn Y Λ K N → TBB.KernelArgumentHypothesisScalar p nn F Y Λ K N :=
  fun hA hSS hFP _ _ _ _ _ _ _ _ _ p nn F Y Λ K N hF hnn hgrid =>
    liftBound_at hXi hA hSS hFP p nn F Y Λ K N hF hnn hgrid

end GlobalTheory.LiftBoundCpt
