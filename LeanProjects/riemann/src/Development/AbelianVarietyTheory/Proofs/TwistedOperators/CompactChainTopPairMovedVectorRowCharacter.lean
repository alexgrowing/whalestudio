import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqConjOfInFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridFiniteDatumVectorThetaFockVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsColIntertwiner
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

section EigTop

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem cart_eq_one_of_posOnb (W : G.Weil) {X : Node} (hX : X.InRange D.R.m) (hP : PosOnb W X) (τ : D.what₂.Tau) :
    W.cart X τ = 1 := by
  obtain ⟨ε, h1, h2⟩ := W.onb_is X hX τ
  rw [hP τ] at h1
  rw [← h1, Matrix.mul_one] at h2
  have hd : IsUnit (W.onb X τ).det := Matrix.isUnit_det_of_left_inverse (hP τ)
  calc W.cart X τ = W.cart X τ * W.onb X τ * (W.onb X τ)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    _ = 1 := by rw [h2, Matrix.mul_nonsing_inv _ hd]

theorem compAt_mt_eq_archM (θ : InfFam D) (V : HSp D) (k : GA D V) (τ : D.what₂.Tau) :
    compAt θ τ (mt V k) = Formalism.L2.Pj.archM V (θ τ) k := by
  have e := GlobalTheory.RealType.realFr_coe θ V 1 k τ
  rw [GlobalTheory.RealType.realFr_one] at e
  rw [show compAt θ τ (mt V k) = ((GlobalTheory.CoefModel.realGL θ V k τ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) from rfl, e]
  simp

theorem det_conj_submatrix {a b : ℕ} (h : a = b) {B : Matrix (Fin b) (Fin b) ℂ} (hB : IsUnit B.det)
    (u : Matrix (Fin a) (Fin a) ℂ) :
    (B * u.submatrix (Fin.cast h.symm) (Fin.cast h.symm) * B⁻¹).det = u.det := by
  subst h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', mul_comm, ← mul_assoc,
    inv_mul_cancel₀ hB.ne_zero, one_mul]
  rfl

end EigTop

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section EigTop2

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem det_compAt_ptTop (W : G.Weil) (μ0 : T) (hL : L.Is μ0) {U : Set T} (N : Std G U)
    (g : Gc D.what₂.Tau (rowSizes D)) (n : Fin (D.R.m + 1)) (τ : D.what₂.Tau) :
    (compAt W.θ τ (mt (G.V (.top n)) (ptTop W g n))).det =
      (rowComp (rowSizes D) g n τ).1.det := by
  induction n using Fin.lastCases with
  | last =>
    show (compAt W.θ τ (mt (G.V (.top D.R.m)) (ptTop W g D.R.m))).det = _
    have hP : PosOnb W (.grid D.R.m D.R.m) :=
      posOnb_of_defNode W μ0 hL (X := .grid D.R.m D.R.m) ⟨le_rfl, rfl⟩
    have hd := fun τ => Matrix.isUnit_det_of_left_inverse (hP τ)
    rw [ptTop_m, kappaTop_apply, compAt_mt_eq_archM]
    have e1 : ∀ (X : Node) (k : GA D (G.V X)), (Formalism.L2.Pj.archM (G.V X) (W.θ τ) k).det =
        ((GlobalTheory.RealType.realAt W.θ N X k τ : GL (Fin (G.V X).rank) ℂ) : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ).det :=
      fun X k => by rw [GlobalTheory.RealType.realAt, GlobalTheory.RealType.realFr_coe, Matrix.det_units_conj']
    rw [e1, (GlobalTheory.RealType.isBlock_realAt W.θ_is N _ τ).det, mul_one, ← e1, ← compAt_mt_eq_archM]
    have e2 := compAt_kappa_snd g (Fin.last _) hP τ
    erw [e2, det_conj_submatrix (rank_gridM G le_rfl).symm (hd τ)]
    have e : rowComp (rowSizes D) g (Fin.last D.R.m) = embed (rowSizes D).nC_succ (g.2 (Fin.last D.R.m)) := by
      simp only [rowComp, MonoidHom.coe_mk, OneHom.coe_mk]
      exact Fin.snoc_last (α := fun j : Fin ((rowSizes D).m + 1) => UG D.what₂.Tau ((rowSizes D).nR j)) _ _
    erw [e]
    show _ = (Matrix.reindex (finSumFinEquiv.trans (finCongr (rowSizes D).nC_succ)) (finSumFinEquiv.trans (finCongr (rowSizes D).nC_succ))
      (Matrix.fromBlocks (g.2 (Fin.last D.R.m) τ).1 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))).det
    rw [Matrix.det_reindex_self]
    exact ((Matrix.det_fromBlocks_zero₂₁ _ _ _).trans (by rw [Matrix.det_one, mul_one]; rfl)).symm
  | cast j =>
    show (compAt W.θ τ (mt (G.V (.top j)) (ptTop W g j))).det = _
    have hP : PosOnb W (.top j) := posOnb_of_defNode W μ0 hL (X := .top j) j.2.le
    rw [ptTop_lt W g j.2, compAt_kappa_fst g j hP τ, det_conj_submatrix (rank_top G j.2.le).symm (Matrix.isUnit_det_of_left_inverse (hP τ))]
    have e : rowComp (rowSizes D) g j.castSucc = g.1 j := by
      simp only [rowComp, MonoidHom.coe_mk, OneHom.coe_mk]
      exact Fin.snoc_castSucc (α := fun j : Fin ((rowSizes D).m + 1) => UG D.what₂.Tau ((rowSizes D).nR j)) _ _ j
    rw [e]

end EigTop2

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section EigTop3

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem movedVec_theta_fock (W : G.Weil) (μ0 : T) (hL : L.Is μ0) {U : Set T} (S : GridChoice W U) (t : T) {j : ℕ}
    (hj : j + 1 ≤ D.R.m) (d : FinDatum G t (.top t j)) (hd : S.Z.HasVec d) :
    IsThetaFunO W.ψ (G.pS (.top t j)) (G.pT (.top t j)) (movedVec t S d) ∧
      ∀ τ, IsFockVacAt (heisO W.ψ (G.pS (.top t j)) (G.pT (.top t j))) W.θ τ (cplxO 1 1) (movedVec t S d) := by
  have hr : (Pair.top t j : Pair T).InRange D.R.m := hj
  have hW := W.om_is _ hr
  have hX0 : DefNode D.R.m (.top j) := by show j ≤ D.R.m; omega
  have hX1 : DefNode D.R.m (.top (j + 1)) := hj
  have hc0 := cart_eq_one_of_posOnb W hX0.inRange (posOnb_of_defNode W μ0 hL hX0)
  have hc1 := cart_eq_one_of_posOnb W hX1.inRange (posOnb_of_defNode W μ0 hL hX1)
  obtain ⟨hv1, hv2⟩ := GlobalTheory.FockRealVec.vec_theta_fock W S.Z (p := .top t j) hj d hd
  have hv : ∀ τ, IsFockVacAt (heisO W.ψ (G.pS (.top t j)) (G.pT (.top t j))) W.θ τ (cplxO 1 1) (S.Z.vec d) := fun τ => by
    have := hv2 τ
    rwa [show G.cartS W.cart (.top t j) τ = 1 from hc0 τ, show G.onT W.cart (.top t j) τ = 1 from hc1 τ] at this
  refine ⟨hW.om_pres _ _ hv1, fun τ z => ?_⟩
  unfold movedVec
  generalize G.toPair (.top t j) (S.N.u (Pair.top t j).small).1 (S.N.u (Pair.top t j).big).1 = q
  obtain ⟨a, b⟩ := q
  obtain ⟨z₀, rfl⟩ : ∃ z₀ : Matrix (Fin (G.pT (.top t j)).rank) (Fin (G.pS (.top t j)).rank) ℂ, z = compAt W.θ τ (mt _ b) * z₀ * compAt W.θ τ (mt _ a⁻¹) := by
    refine ⟨compAt W.θ τ (mt _ b⁻¹) * z * compAt W.θ τ (mt _ a), ?_⟩
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.OrientedHeis.compAt_mt_mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      GlobalTheory.OrientedHeis.compAt_mt_mul_inv, Matrix.mul_one]
  have h0 := congrArg (W.om _ (a, b)) (hv τ z₀)
  rw [GlobalTheory.FockMove.om_annih hW W.θ_is a b τ (by rw [Matrix.one_mul, Matrix.mul_one])
    (by rw [Matrix.one_mul, Matrix.mul_one]) z₀ hv1, map_zero] at h0
  exact h0

theorem cast_half {K : Type} [Field K] [CharZero K] {n : ℕ} (hn : Even n) : (((n / 2 : ℕ) : ℤ) : K) = (n : K) / 2 := by
  obtain ⟨k, rfl⟩ := hn
  rw [show (k + k) / 2 = k by omega]
  push_cast
  ring

end EigTop3

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

theorem om_ptTop_movedVec : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) {U : Set T} (S : GridChoice W U) (g : Gc D.what₂.Tau (GlobalTheory.RowReal.rowSizes D)) (t : T) (j : Fin D.R.m)
    (d : FinDatum G t (.top t j)), S.Z.HasVec d →
    W.om (.top t j) (G.toPair (.top t j) (GlobalTheory.RowReal.ptTop W g j) (GlobalTheory.RowReal.ptTop W g (j + 1))) (movedVec t S d) =
      GlobalTheory.RowReal.rowScal (GlobalTheory.RowReal.rowEntries D sc.cGap) j g • movedVec t S d := by
  intro D T L sc G μ0 hL W U S g t j d hd
  have hj : (j : ℕ) + 1 ≤ D.R.m := j.2
  have hr : (Pair.top t (j : ℕ) : Pair T).InRange D.R.m := hj
  have hW := W.om_is _ hr
  have hX0 : DefNode D.R.m (.top j) := j.2.le
  have hX1 : DefNode D.R.m (.top ((j : ℕ) + 1)) := hj
  have hc0 := cart_eq_one_of_posOnb W hX0.inRange (posOnb_of_defNode W μ0 hL hX0)
  have hc1 := cart_eq_one_of_posOnb W hX1.inRange (posOnb_of_defNode W μ0 hL hX1)
  have hS : ∀ τ, IsCartanInv (gramAt D (G.V (.top j)) τ) 1 := fun τ => by
    have := W.cart_is _ hX0.inRange τ
    rwa [hc0 τ] at this
  have hT : ∀ τ, IsCartanInv (gramAt D (G.V (.top ((j : ℕ) + 1))) τ) 1 := fun τ => by
    have := W.cart_is _ hX1.inRange τ
    rwa [hc1 τ] at this
  obtain ⟨hm, hv⟩ := movedVec_theta_fock W μ0 hL S t hj d hd
  have ev0 : Even (G.V (.top j)).rank := by rw [rank_top G j.2.le]; exact even_nR _
  have ev1 : Even (G.V (.top ((j : ℕ) + 1))).rank := by rw [rank_top G hj]; exact even_nR _
  have hχS : G.chrS (.top t j) = L.mu t ((j : ℕ) + 1) := by
    show Formalism.IndefR.Lift.attChr (L.mu t ((j : ℕ) + 1)) L.eta (G.V (.top j)).rank = _
    simp [Formalism.IndefR.Lift.attChr, Nat.not_odd_iff_even.2 ev0]
  have hχT : G.chrT (.top t j) = L.mu t ((j : ℕ) + 1) := by
    show Formalism.IndefR.Lift.attChr (L.mu t ((j : ℕ) + 1)) L.eta (G.V (.top ((j : ℕ) + 1))).rank = _
    simp [Formalism.IndefR.Lift.attChr, Nat.not_odd_iff_even.2 ev1]
  have hexp : ∀ τ, HasInfExp D (L.mu t ((j : ℕ) + 1)) τ (-(((rowEntries D sc.cGap τ).e j : ℤ) : ℚ)) := fun τ => by
    have h := GlobalTheory.GridJoin.ColIt.hasInfExp_mu L hL t j τ
    have e : (((rowEntries D sc.cGap τ).e j : ℤ) : ℚ) = (D.hc τ).e j := by
      show (((num D sc.cGap τ).e ((j : ℕ) + 1) : ℤ) : ℚ) = _
      rw [num_e D sc.cGap τ (by omega) hj]
      rfl
    rwa [e]
  have key := GlobalTheory.VacuumCharacter.vacuum_character D W.ψ W.θ (G.V (.top j)) (G.V (.top ((j : ℕ) + 1)))
    (G.chrS (.top t j)) (G.chrT (.top t j)) (W.om (.top t j)) hW W.θ_is (hX0.sigOK G) (hX1.sigOK G) (fun _ => 1) hS hT
    (fun τ => -(((rowEntries D sc.cGap τ).e j : ℤ) : ℚ)) (fun τ => -(((rowEntries D sc.cGap τ).e j : ℤ) : ℚ))
    (fun τ => by rw [hχS]; exact hexp τ) (fun τ => by rw [hχT]; exact hexp τ)
    (fun τ => -(rowEntries D sc.cGap τ).e j + ((rowSizes D).nR j.castSucc / 2 : ℕ))
    (fun τ => -(rowEntries D sc.cGap τ).e j - ((rowSizes D).nR j.castSucc / 2 : ℕ))
    (fun τ => (rowEntries D sc.cGap τ).e j - ((rowSizes D).nR j.succ / 2 : ℕ))
    (fun τ => by
      rw [Int.cast_add, Int.cast_neg, Fin.val_castSucc, cast_half (even_nR (S := rowSizes D) j), rank_top G j.2.le])
    (fun τ => by
      rw [Int.cast_sub, Int.cast_neg, Fin.val_castSucc, cast_half (even_nR (S := rowSizes D) j), rank_top G j.2.le])
    (fun τ => by
      rw [Matrix.trace_one, Fintype.card_fin, rank_top G hj, Int.cast_sub, Fin.val_succ,
        cast_half (even_nR (S := rowSizes D) ((j : ℕ) + 1))]
      push_cast
      ring)
    (movedVec t S d) hm hv (ptTop W g j) (ptTop_mem W g j) (ptTop W g ((j : ℕ) + 1)) (ptTop_mem W g _)
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
  rw [show G.toPair (.top t j) (ptTop W g j) (ptTop W g ((j : ℕ) + 1)) = (ptTop W g j, ptTop W g ((j : ℕ) + 1)) from rfl, key]
  congr 1
  clear key hexp hχS hχT ev0 ev1 hm hv hS hT hc0 hc1 hW hr hd
  have a1 : (1 / 2 : ℂ) • ((1 : Matrix (Fin (G.V (.top ((j : ℕ) + 1))).rank) (Fin (G.V (.top ((j : ℕ) + 1))).rank) ℂ) + 1) = 1 := by
    module
  simp only [a1, sub_self, smul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add, Matrix.det_one, one_zpow, mul_one]
  have hg : ∀ τ, (compAt W.θ τ (mt (G.V (.top j)) (ptTop W g j))).det = (rowComp (rowSizes D) g j.castSucc τ).1.det :=
    fun τ => det_compAt_ptTop W μ0 hL S.N g j.castSucc τ
  have hh : ∀ τ, (compAt W.θ τ (mt (G.V (.top ((j : ℕ) + 1))) (ptTop W g ((j : ℕ) + 1)))).det =
      (rowComp (rowSizes D) g j.succ τ).1.det :=
    fun τ => det_compAt_ptTop W μ0 hL S.N g j.succ τ
  simp only [hg, hh]
  simp [rowScal, detChar, detU, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun τ _ => mul_comm _ _

end GlobalTheory.RowReal
