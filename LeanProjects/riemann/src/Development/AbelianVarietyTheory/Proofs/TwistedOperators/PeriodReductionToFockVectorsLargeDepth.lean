import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowUnfoldingBasicHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedVectorsAreCombinationsOfVacuaOfLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnRealDatumFockCombinationLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestCellValueOfStepsLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefinitePeriodDependsOnProductFunction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockRed

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem opPow_smul {ι X : Type} (A : ι → (X → ℂ) → X → ℂ) (hA : ∀ i (c : ℂ) g, A i (c • g) = c • A i g)
    (k : ι →₀ ℕ) (c : ℂ) (f : X → ℂ) : opPow A k (c • f) = c • opPow A k f := by
  unfold opPow
  induction (Finsupp.toMultiset k).toList with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, ih, hA]

theorem pureTensorL_smul {ι X : Type} (A : ι → (X → ℂ) → X → ℂ) (hA : ∀ i (c : ℂ) g, A i (c • g) = c • A i g)
    (c : ℂ) (f : X → ℂ) : pureTensorL A (c • f) = c • pureTensorL A f := by
  refine (MvPolynomial.basisMonomials ι ℂ).ext fun k => ?_
  simp only [pureTensorL, Module.Basis.constr_basis, LinearMap.smul_apply, opPow_smul A hA]

theorem dRho_smul {m n : ℕ} (hs : Mx D m n → (Mx D m n → ℂ) → Mx D m n → ℂ)
    (hhs : ∀ w (c : ℂ) g, hs w (c • g) = c • hs w g) (θ : InfFam D) (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ)
    (c : ℂ) (g : Mx D m n → ℂ) : Datum.dRho hs θ τ z (c • g) = c • Datum.dRho hs θ τ z g := by
  funext x
  simp only [Datum.dRho, hhs, Pi.smul_apply, smul_eq_mul]
  exact deriv_const_mul_field c

theorem aPlusAll_smul {m n : ℕ} (hs : Mx D m n → (Mx D m n → ℂ) → Mx D m n → ℂ)
    (hhs : ∀ w (c : ℂ) g, hs w (c • g) = c • hs w g) (θ : InfFam D) J B B' (k : FVar D m n) (c : ℂ) (g : Mx D m n → ℂ) :
    aPlusAll hs θ J B B' k (c • g) = c • aPlusAll hs θ J B B' k g := by
  simp only [aPlusAll, aPlus, crea, dRho_smul hs hhs, smul_comm _ c, smul_sub]

theorem fock_smul (W : G.Weil) (p : Pair T) (c : ℂ) (f : WO (G.pS p) (G.pT p) → ℂ) (Q : PolF D (G.pT p).rank (G.pS p).rank) :
    W.fock p (c • f) Q = c • W.fock p f Q := by
  have hh : ∀ w (c : ℂ) g, heisO W.ψ (G.pS p) (G.pT p) w (c • g) = c • heisO W.ψ (G.pS p) (G.pT p) w g := by
    intro w c g; funext x; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
  simp only [GridData.Weil.fock, pureTensorO]
  rw [pureTensorL_smul _ (fun i c g => aPlusAll_smul _ hh _ _ _ _ i c g)]
  rfl

end GlobalTheory.FockRed

namespace GlobalTheory.FockRed

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem liftA_smul_left (W : G.Weil) (M : Vol G) (a : Arrow T) (f : Sch G a) (c : ℂ) (F : Fn G a.src) :
    liftA W M a f (c • F) = c • liftA W M a f F := by
  funext g
  simp only [liftA, Formalism.IndefR.Lift.liftInt, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext h; ring

theorem liftA_smul_right (W : G.Weil) (M : Vol G) (a : Arrow T) (ha : ∀ i, a ≠ .coreUp i) (c : ℂ) (f : Sch G a)
    (F : Fn G a.src) : liftA W M a (c • f) F = c • liftA W M a f F := by
  funext g
  simp only [liftA, Formalism.IndefR.Lift.liftInt, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext h
  cases a with
  | coreUp i => exact absurd rfl (ha i)
  | _ => simp only [GridData.Weil.kerA, GridData.Weil.ker, thetaKO, map_smul, LinearMap.smul_apply, Module.End.smul_def, Pi.smul_apply, smul_eq_mul]; ring

theorem pathLift_column_smul_univ (W : G.Weil) (M : Vol G) (t : T) : ∀ (n : ℕ) (s : Fin n → ℂ) (g : ∀ j : Fin n, Sch G (.col t j))
    (φ : Fn G (.top 0)), liftP W M (colPath t n) (colFam t n fun j => s j • g j) φ =
      (∏ j, s j) • liftP W M (colPath t n) (colFam t n g) φ
  | 0, s, g, φ => by simp [colPath, liftP]
  | n + 1, s, g, φ => by
    show liftA W M (.col t n) (s (Fin.last n) • g (Fin.last n))
        (liftP W M (colPath t n) (colFam t n fun j => s j.castSucc • g j.castSucc) φ) =
      (∏ j, s j) • liftA W M (.col t n) (g (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => g j.castSucc) φ)
    rw [pathLift_column_smul_univ W M t n (fun j => s j.castSucc) (fun j => g j.castSucc) φ, liftA_smul_left,
      liftA_smul_right W M _ (fun i h => by cases h), Fin.prod_univ_castSucc, smul_smul, mul_comm]

theorem pathLift_row_smul_univ (W : G.Weil) (M : Vol G) (m : ℕ) : ∀ (n : ℕ) (s : Fin n → ℂ) (g : ∀ i : Fin n, Sch G (.right i m))
    (F : Fn G (.grid 0 m)), liftP W M (rowPath T m n) (rowFam m n fun i => s i • g i) F =
      (∏ i, s i) • liftP W M (rowPath T m n) (rowFam m n g) F
  | 0, s, g, F => by simp [rowPath, liftP]
  | n + 1, s, g, F => by
    show liftA W M (.right n m) (s (Fin.last n) • g (Fin.last n))
        (liftP W M (rowPath T m n) (rowFam m n fun i => s i.castSucc • g i.castSucc) F) =
      (∏ i, s i) • liftA W M (.right n m) (g (Fin.last n)) (liftP W M (rowPath T m n) (rowFam m n fun i => g i.castSucc) F)
    rw [pathLift_row_smul_univ W M m n (fun i => s i.castSucc) (fun i => g i.castSucc) F, liftA_smul_left,
      liftA_smul_right W M _ (fun i h => by cases h), Fin.prod_univ_castSucc, smul_smul, mul_comm]

end GlobalTheory.FockRed

namespace GlobalTheory.FockRed

theorem defPer_of_smul {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (t : T) (M : Vol G) (Q : PolCol G) (P : PolRow G) (d : PureDat G t) (φ : Fn G (.top 0))
    (F : Fn G (.grid 0 D.R.m)) (s s' : Fin D.R.m → ℂ) (g : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))) → ℂ)
    (f : SchRow G) (h1 : ∀ j : Fin D.R.m, movedVec t S (d.1 j) = s j • g j) (h2 : ∀ i : Fin D.R.m, movedVec t S (d.2 i) = s' i • f i) :
    defPer t S M (Q, P) d φ F = ((∏ j, s j) * ∏ i, s' i) * ∫ h in M.fd (.grid D.R.m D.R.m),
      liftP W M (colPath t D.R.m) (colFam t D.R.m fun j => W.fock (.top t j) (g j) (Q j)) φ (stabilizerEmbedding G.sp.topDec h) *
        liftP W M (rowPath T D.R.m D.R.m) (rowFam D.R.m D.R.m fun i => W.fock (.chi i D.R.m) (f i) (P i)) F h
        ∂M.ν (.grid D.R.m D.R.m) := by
  have e1 : (fun j : Fin D.R.m => (W.fock (.top t j) (movedVec t S (d.1 j)) (Q j) : Sch G (.col t j))) =
      fun j : Fin D.R.m => s j • (W.fock (.top t j) (g j) (Q j) : Sch G (.col t j)) := funext fun j => by
    rw [h1 j]; exact fock_smul W (.top t j) _ _ _
  have e2 : (fun i : Fin D.R.m => (W.fock (.chi i D.R.m) (movedVec t S (d.2 i)) (P i) : Sch G (.right i D.R.m))) =
      fun i : Fin D.R.m => s' i • (W.fock (.chi i D.R.m) (f i) (P i) : Sch G (.right i D.R.m)) := funext fun i => by
    rw [h2 i]; exact fock_smul W (.chi i D.R.m) _ _ _
  have e3 := (congrArg (fun x => liftP W M (colPath t D.R.m) (colFam t D.R.m x) φ) e1).trans
    (pathLift_column_smul_univ W M t D.R.m s (fun j => W.fock (.top t j) (g j) (Q j)) φ)
  have e4 := (congrArg (fun x => liftP W M (rowPath T D.R.m D.R.m) (rowFam D.R.m D.R.m x) F) e2).trans
    (pathLift_row_smul_univ W M D.R.m D.R.m s' (fun i => W.fock (.chi i D.R.m) (f i) (P i)) F)
  unfold defPer
  rw [← integral_const_mul]
  congr 1
  funext h
  have e5 := congrFun e3 (stabilizerEmbedding G.sp.topDec h)
  have e6 := congrFun e4 h
  simp only [Pi.smul_apply, smul_eq_mul] at e5 e6
  refine (congrArg₂ (· * ·) e5 e6).trans ?_
  ring

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

set_option maxHeartbeats 1600000 in

theorem fockAt_of_steps (ch : Choice R) (hB : BasicAt ch) (hMv : MovedAt ch) (hCF : ColFock ch)
    (hL : ∀ (t : T) (M : Vol ch.G), IsHaarDef M → ∀ (f : SchRow ch.G), (∀ i, IsThetaFunO ch.W.ψ _ _ (f i)) →
      ∀ (P : PolRow ch.G) (y : (R.HX t).H), GlobalTheory.Unf.IsContAut _ (liftP ch.W M (rowPath T D.R.m D.R.m)
        (rowFam D.R.m D.R.m fun i => ch.W.fock (.chi i D.R.m) (f i) (P i)) (formTop ch t y))) : FockAt ch := by
  classical
  obtain ⟨_, _, _, _, _, hBgood', _⟩ := hB
  obtain ⟨v, hv, κ, κ', z, hz, hmv⟩ := hMv
  refine ⟨fun t => ∏ j : Fin D.R.m, z t j, fun t => Subgroup.prod_mem _ fun j _ => hz t j, ?_⟩
  intro C hC P
  obtain ⟨σc, hσc⟩ := hCF v hv C hC
  obtain ⟨K, hK⟩ : ∃ K : ℂ, K = (∏ j : Fin D.R.m, ((κ j : ℂˣ) : ℂ))⁻¹ * (∏ i : Fin D.R.m, ((κ' i : ℂˣ) : ℂ))⁻¹ := ⟨_, rfl⟩
  refine ⟨K • σc.mapDomain (fun Q => (Q, P)), ?_⟩
  intro t a β M hM hS τ c hτ hc y
  obtain ⟨Z, hZ⟩ : ∃ Z : ℂ, Z = ∏ j : Fin D.R.m, ((z t j : ℂˣ) : ℂ) := ⟨_, rfl⟩
  have hone : Z⁻¹ * K * ((∏ j : Fin D.R.m, ((κ j * z t j : ℂˣ) : ℂ)) * ∏ i : Fin D.R.m, ((κ' i : ℂˣ) : ℂ)) = 1 := by
    have n1 : (∏ j : Fin D.R.m, ((κ j : ℂˣ) : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => (κ j).ne_zero
    have n2 : (∏ j : Fin D.R.m, ((κ' j : ℂˣ) : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => (κ' j).ne_zero
    have n3 : (∏ j : Fin D.R.m, ((z t j : ℂˣ) : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => (z t j).ne_zero
    simp only [Units.val_mul, Finset.prod_mul_distrib]
    rw [hK, hZ]
    field_simp
  have key : ∀ d ∈ τ.support, per ch.W M t (combC ch.W (c d) C) (combR ch.rm (c d)) P (colFn ch a) (formTop ch t y) =
      σc.sum fun Q x => x * (Z⁻¹ * K * defPer t ch.S.toGridChoice M (Q, P) d (colFn ch a) (formTop ch t y)) := by
    intro d hd
    obtain ⟨h1, h2⟩ := hmv t a β τ c hS hτ hc d hd
    have hfin : ∀ j, j < D.R.m → IsFinComb ((c d).1 j) := fun j hj => ((hc d hd).1 ⟨j, hj⟩).1
    have hth := (hBgood' C hC (c d) hfin).2
    refine (hσc t M hM a (c d) hfin _ (hL t M hM (combR ch.rm (c d)) hth P y)).trans ?_
    refine Finset.sum_congr rfl fun Q _ => ?_
    dsimp only
    rw [defPer_of_smul ch.S.toGridChoice t M Q P d (colFn ch a) (formTop ch t y) (fun j => ((κ j * z t j : ℂˣ) : ℂ))
      (fun i => ((κ' i : ℂˣ) : ℂ)) (fun j => comb ch.W.ψ _ _ ((c d).1 j) (v j)) (combR ch.rm (c d)) h1 h2,
      ← mul_assoc (Z⁻¹ * K), hone, one_mul]
  rw [defTot_smul, Units.coe_prod, ← hZ]
  unfold defTot
  rw [Finsupp.sum_mapDomain_index_inj (fun Q Q' h => (Prod.ext_iff.1 h).1), Finsupp.sum_comm]
  simp only [Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [key d hd, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Q _ => ?_
  ring

end

theorem fockAt_big : Big fun ch => FockAt ch := by
  obtain ⟨a0, ha⟩ := Big.and (Big.and GlobalTheory.T.lastRow_unfolding_basicHypotheses GlobalTheory.T.movedVectorsAreCombinationsOfVacua_of_large_depth) GlobalTheory.T.columnRealDatum_fockCombination_largeDepth
  refine ⟨a0, fun ε CF hC => ?_⟩
  obtain ⟨x, hx⟩ := ha ε CF hC
  refine ⟨x, fun D large₂ he hxx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch hsc => ?_⟩
  obtain ⟨⟨hB, hMv⟩, hCF⟩ := hx D large₂ he hxx Γ Pl0 T A Ks R F s ch hch hsc
  refine fockAt_of_steps ch hB hMv hCF fun t M hM f hf P y => ?_
  have hN : ∀ X, DefNode D.R.m X → X ≠ .top D.R.m → GlobalTheory.RowTens.Nice M X := fun X hX hX' => by
    refine ⟨?_, hM X hX hX'⟩
    rcases X with ⟨i, j⟩ | i | j
    all_goals first
      | exact hX.elim
      | exact GlobalTheory.DefConv.posDef_of_node ch.G s.core.lev hX rfl
      | (obtain ⟨h1, rfl⟩ := hX
         exact GlobalTheory.DefConv.posDef_of_node ch.G s.core.lev ⟨h1, le_rfl⟩ (by simp [Node.neg]))
  have := GlobalTheory.RowTens.row_invCont ch.W hN (hB.2.1 t y) D.R.m le_rfl _
    fun k : Fin D.R.m => GlobalTheory.RowTens.fock_theta ch.W _ (hf k) (P k)
  exact ⟨this.2, this.1⟩

end GlobalTheory.FockRed
