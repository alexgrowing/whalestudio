import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqConjOfInFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoInfMulProd

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem hasInfExp_attChr_chi {μ0 : T} (hL : L.Is μ0) {i : ℕ} (hi : i < D.R.m) (n : ℕ) (τ : D.what₂.Tau) :
    HasInfExp D (Formalism.IndefR.Lift.attChr (G.ch.chi (D.R.m - i)) L.eta n) τ
      ((cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd n then 1 / 2 else 0) := by
  have hm1 : 1 ≤ D.R.m - i := by omega
  have hm2 : D.R.m - i ≤ D.R.m := by omega
  have h0 : HasInfExp D (G.ch.chi (D.R.m - i)) τ (cen D sc.cGap τ (D.R.m - i) : ℚ) :=
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ)) (G.ch.chi_eq _ hm1 hm2)
      ⟨fun τ => 2 * cen D sc.cGap τ (D.R.m - i), fun τ => by push_cast; ring, G.ch.inf _ hm1 hm2⟩ τ
  have heta : HasInfExp D L.eta τ (1 / 2) :=
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
      (GlobalTheory.Chain.StepVac.hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  unfold Formalism.IndefR.Lift.attChr
  split_ifs
  · rw [sub_eq_add_neg]
    exact GlobalTheory.Chain.StepVac.hasInfExp_mul h0 (GlobalTheory.Chain.StepVac.hasInfExp_inv heta)
  · simpa using h0

theorem rowEntries_c_rev (τ : D.what₂.Tau) (i : Fin D.R.m) :
    (rowEntries D sc.cGap τ).c i.rev = cen D sc.cGap τ (D.R.m - i) := by
  show (num D sc.cGap τ).cen ((i.rev : ℕ) + 1) = _
  rw [Fin.val_rev, show D.R.m - (i + 1) + 1 = D.R.m - i by omega]
  rfl

theorem half_ceil (n : ℕ) : (((n + 1) / 2 : ℕ) : ℚ) = (n : ℚ) / 2 + if Odd n then 1 / 2 else 0 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [if_neg (Nat.not_odd_iff_even.2 ⟨k, hk⟩), hk, show (k + k + 1) / 2 = k by omega]
    push_cast; ring
  · rw [if_pos ⟨k, hk⟩, hk, show (2 * k + 1 + 1) / 2 = k + 1 by omega]
    push_cast; ring

theorem det_compAt_ptGrid {μ0 : T} (hL : L.Is μ0) (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (n : ℕ) (hn : n < D.R.m + 1)
    (τ : D.what₂.Tau) :
    (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.grid n D.R.m)) (ptGrid W g n))).det =
      Matrix.det (g.2 ⟨n, hn⟩ τ).1 := by
  have hX : DefNode D.R.m (.grid n D.R.m) := ⟨Nat.lt_succ_iff.1 hn, rfl⟩
  have hW := posOnb_of_defNode W μ0 hL hX
  have hB : IsUnit (W.onb (.grid n D.R.m) τ).det := by
    have h := congrArg Matrix.det (hW τ)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at h
    exact isUnit_iff_ne_zero.2 fun h0 => by rw [h0, mul_zero] at h; exact zero_ne_one h
  rw [ptGrid_le W g hn, compAt_kappa_snd g ⟨n, hn⟩ hW τ, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv,
    mul_right_comm, Ring.mul_inverse_cancel _ hB, one_mul]
  exact Matrix.det_submatrix_equiv_self (finCongr (rank_gridM G (Nat.lt_succ_iff.1 hn))) _

theorem om_ptGrid_movedVec : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) {U : Set T} (S : GridChoice W U) (g : Gc D.what₂.Tau (GlobalTheory.RowReal.rowSizes D)) (t : T) (i : Fin D.R.m)
    (d : FinDatum G t (.chi i D.R.m)), S.Z.HasVec d →
    W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (GlobalTheory.RowReal.ptGrid W g i) (GlobalTheory.RowReal.ptGrid W g (i + 1))) (movedVec t S d) =
      GlobalTheory.RowReal.colScal (GlobalTheory.RowReal.rowEntries D sc.cGap) i g • movedVec t S d := by
  intro D T L sc G μ0 hL W U S g t i d hd
  have hp : DefPair D.R.m (.chi (i : ℕ) D.R.m : Pair T) := ⟨i.2, rfl⟩
  have hn := DefPair.nodes hp
  have hom := W.om_is (.chi (i : ℕ) D.R.m) (by
    simp only [DefPair, DefNode] at hp hn; simp only [Pair.InRange, Node.InRange]; omega)
  obtain ⟨h1, h2⟩ := GlobalTheory.T.gridFiniteDatumVector_theta_fockVacuum W S.Z hp d hd
  have hf : IsThetaFunO W.ψ _ _ (movedVec t S d) ∧ ∀ τ, IsFockVacAt (heisO W.ψ _ _) W.θ τ
      (cplxO (G.cartS W.cart (.chi (i : ℕ) D.R.m) τ) (G.onT W.cart (.chi (i : ℕ) D.R.m) τ)) (movedVec t S d) :=
    GlobalTheory.T.weil_finitePoint_preserves_fockVacuum D W.ψ W.θ _ _ _ _ (W.om _) hom W.θ_is _ _ _ h1 h2 _
      (GlobalTheory.FockReal.negGA_mem_GfC _ (S.N.u _).2) _ (S.N.u _).2
  have hrS : (G.pS (.chi (i : ℕ) D.R.m : Pair T)).rank = (rowSizes D).nC ((i : ℕ) + 1) := rank_gridM G (by omega)
  have hrT : (G.pT (.chi (i : ℕ) D.R.m : Pair T)).rank = (rowSizes D).nC (i : ℕ) := rank_gridM G (by omega)
  have key := GlobalTheory.FockReal.om_fockIn hL W W.onb hp (fun X hX τ => GlobalTheory.FockReal.onb_def hL W hX τ)
    (fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd (G.pS (.chi (i : ℕ) D.R.m : Pair T)).rank then 1 / 2 else 0)
    (fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd (G.pT (.chi (i : ℕ) D.R.m : Pair T)).rank then 1 / 2 else 0)
    (fun τ => hasInfExp_attChr_chi hL i.2 _ τ) (fun τ => hasInfExp_attChr_chi hL i.2 _ τ)
    (fun τ => (rowEntries D sc.cGap τ).c i.rev - (((rowSizes D).nC i.succ + 1) / 2 : ℕ))
    (fun τ => -(rowEntries D sc.cGap τ).c i.rev + (((rowSizes D).nC i.castSucc + 1) / 2 : ℕ))
    (fun τ => ?_) (fun τ => ?_) _ hf.1 hf.2 (ptGrid W g i) (ptGrid_mem W g i) (ptGrid W g (i + 1))
    (ptGrid_mem W g (i + 1)) 1
  · have e1 : fockIn W W.onb (.chi (i : ℕ) D.R.m) (movedVec t S d) 1 = movedVec t S d :=
      GlobalTheory.FiniteFock.pureTensorO_one _ _ _ _ _ _ _ _ _
    rw [show GlobalTheory.FockReal.realSubst W W.onb (.chi (i : ℕ) D.R.m) (ptGrid W g i) (ptGrid W g (i + 1)) 1 = 1 from
      map_one _, e1] at key
    rw [key]
    congr 1
    simp only [GlobalTheory.FockReal.realChar, GridData.toPair, mt_negGA]
    simp only [det_compAt_ptGrid hL W g (i : ℕ) (by omega), det_compAt_ptGrid hL W g ((i : ℕ) + 1) (by omega)]
    simp only [colScal, detChar, detU, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul, Units.coe_prod,
      Units.val_zpow_eq_zpow_val, MonoidHom.coe_toHomUnits, MonoidHom.coe_comp, Function.comp_apply]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [mul_comm]
    rfl
  · simp only [GlobalTheory.FockReal.sgnP, rowEntries_c_rev, Fin.val_succ, rank_gridM G (show (i : ℕ) + 1 ≤ D.R.m by omega),
      Int.cast_sub, Int.cast_natCast, half_ceil]
    ring
  · simp only [GlobalTheory.FockReal.sgnP, rowEntries_c_rev, Fin.val_castSucc, hrT, Int.cast_add, Int.cast_neg, Int.cast_natCast,
      half_ceil]
    ring

end GlobalTheory.RowReal
