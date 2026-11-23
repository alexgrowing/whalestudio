import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneHomothetyCarriesSelfDualOfSplitComponentStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFrameFinitePartMulOfCarriesLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMatrixOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.BaseMoveAt

theorem val_of_reGL_eq_inv_diagGL {k : Type} [Field k] {a b : ℕ} (h : a = b) (Y : GL (Fin a) k) (c : Fin b → kˣ)
    (hY : GlobalTheory.StepData.reGL (finCongr h) Y = (GlobalTheory.SplitFlip.diagGL c)⁻¹) :
    (Y : Matrix (Fin a) (Fin a) k) = diagonal fun i => (((c (Fin.cast h i))⁻¹ : kˣ) : k) := by
  subst h
  have e : GlobalTheory.StepData.reGL (finCongr (rfl : a = a)) Y = Y := by
    ext i j
    simp [GlobalTheory.StepData.reGL]
  rw [e] at hY
  rw [hY]
  rfl

theorem submatrix_mulVec_comp {k : Type} [CommRing k] {m n ι : Type} [Fintype n] [Fintype ι] (M : Matrix m n k) (F : ι ≃ n)
    (y : n → k) : (M.submatrix id F) *ᵥ (fun i => y (F i)) = M *ᵥ y := by
  funext i
  simp only [mulVec, dotProduct, submatrix_apply, id]
  exact Fintype.sum_equiv F _ _ fun _ => rfl

end GlobalTheory.BaseMoveAt

namespace GlobalTheory.BaseMoveAt

set_option maxHeartbeats 1000000 in

theorem lat_moves_at_place : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → ∀ (G : GridData L sc) (W : G.Weil) (U : Set T) (S : GridChoice W U) (t : T), t ∈ U → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → ∀ b : Pts G, IsBase t S.B b → ∀ w ∈ locPl G t, ∀ p : GlobalTheory.FinPl.SplitPt D (Kw w), Formalism.L2.NTheta.IsIdemAt p.e w → (∀ a : AE D, p.pr a = cpt w (Lev.swapAE D (finPart D a))) → ∀ x : Fin (G.V (.grid D.R.m 0)).rank → Kw w, ((fun i => p.sec (x i)) ∈ GlobalTheory.FinPl.latV _ (G.Λ (.grid D.R.m 0)) (· = p.v) ↔ (fun i => p.sec (((Formalism.L2.Theta.mt _ (b 0)).map p.pr *ᵥ x) i)) ∈ GlobalTheory.FinPl.latV _ (GlobalTheory.RowShape.rowN G 0) (· = p.v)) := by
  intro D T L sc μ₀ hL hde G W U S t ht hc b hb w hw p hpw hpr x
  have h0 : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hpr' : ∀ a : D.host.E, p.pr (incA D a) = algebraMap D.host.E (Kw w) a := fun a =>
    (hpr _).trans (GlobalTheory.FunObj.Good.cpt_incA w a)
  have hN : (Formalism.L2.Theta.mt _ (b 0)).map p.pr =
      ((GlobalTheory.StdFrames.loc w (Lev.finE (G.V (.grid D.R.m 0)) (b 0)) : GL _ (Kw w)) : Matrix _ _ (Kw w)) := by
    ext i j
    rw [Matrix.map_apply, hpr]
    rfl
  obtain ⟨e, -, -, hloc⟩ := hb.1
  have hl := hloc ⟨w, hw⟩
  simp only [GlobalTheory.FunObj.inBasis, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_inv_apply] at hl
  have hY := val_of_reGL_eq_inv_diagGL _ _ _ hl
  simp only [Fin.coe_cast, topRank_eq G t w (Nat.zero_le _), map_mul, map_inv] at hY
  have hrow := S.row t ht w hw 0 h0
  unfold GlobalTheory.FunObj.IsSumFrame at hrow
  simp only [if_true] at hrow
  have hΛ : G.Λ (.grid D.R.m 0) = (G.rowDec 0 h0).lat (G.Λ (.top 0)) (stairId (G.pl.stA sc) (G.pl.stAbar sc) (D.R.m - 1 - 0)) :=
    G.sp.colLat D.R.m h0 le_rfl
  have hR : GlobalTheory.RowShape.rowN G 0 = (G.rowDec 0 h0).lat (G.Λ (.top 0)) (GlobalTheory.RowShape.rowId D 0) := by
    simp [GlobalTheory.RowShape.rowN, h0]

  obtain ⟨δ, hδ⟩ : ∃ δ : Fin (G.V (.grid D.R.m 0)).rank → Kw w, δ = fun i =>
      ((((unifAt w) ^ (cosExp G w * (i.1 + 1 - (G.V (.top 0)).rank)))⁻¹ : (Kw w)ˣ) : Kw w) := ⟨_, rfl⟩
  have hcomm : ((GlobalTheory.StdFrames.loc w (Lev.finE (G.V (.grid D.R.m 0)) (b 0)) : GL _ (Kw w)) : Matrix _ _ (Kw w)) *
      ((GlobalTheory.StdFrames.loc w (S.B.β D.R.m 0) : GL _ (Kw w)) : Matrix _ _ (Kw w)) =
      ((GlobalTheory.StdFrames.loc w (S.B.β D.R.m 0) : GL _ (Kw w)) : Matrix _ _ (Kw w)) * diagonal δ := by
    rw [hδ, ← hY, ← Units.val_mul, ← Units.val_mul]
    congr 1
    group

  obtain ⟨s, hs⟩ : ∃ s : Fin (D.R.m - 1 - 0) → Kw w, s = fun r =>
      frameSign (Kw w) (D.R.m - 1 - 0) r * ((unifAt w : Kw w) ^ (cosExp G w * (r.1 + 1))) := ⟨_, rfl⟩
  obtain ⟨M', hM'⟩ : ∃ M' : Matrix (Fin (G.V (.grid D.R.m 0)).rank) (Fin (G.V (.top 0)).rank ⊕ Fin (D.R.m - 1 - 0)) (Kw w),
      M' = (fromCols (frameMat (G.V (.grid D.R.m 0)) (G.V (.top 0)) (G.rowDec 0 h0).ι) (G.rowDec 0 h0).a).map
        (fun a => p.pr (incA D a)) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin (G.V (.top 0)).rank ⊕ Fin (D.R.m - 1 - 0)) (Fin (G.V (.top 0)).rank ⊕ Fin (D.R.m - 1 - 0)) (Kw w),
      Q = fromBlocks ((GlobalTheory.StdFrames.loc w (S.βp 0) : GL _ (Kw w)) : Matrix _ _ (Kw w)) 0 0 (diagonal s) := ⟨_, rfl⟩
  have hLb : ((GlobalTheory.StdFrames.loc w (S.B.β D.R.m 0) : GL _ (Kw w)) : Matrix _ _ (Kw w)).submatrix id
      (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank) = M' * Q := by
    have hM'' : M' = fromCols ((frameMat (G.V (.grid D.R.m 0)) (G.V (.top 0)) (G.rowDec 0 h0).ι).map
        (algebraMap D.host.E (Kw w))) ((G.rowDec 0 h0).a.map (algebraMap D.host.E (Kw w))) := by
      rw [hM']
      ext i j
      rcases j with j | j <;> simp [hpr']
    rw [hrow, hM'', hQ, fromCols_mul_fromBlocks, hs]
    simp only [Matrix.mul_zero, add_zero, zero_add]

  have hδl : ∀ i, δ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank (Sum.inl i)) = 1 := by
    intro i
    have hi : i.1 + 1 - (G.V (.top 0)).rank = 0 := by have := i.2; omega
    simp [hδ, GlobalTheory.FunObj.frame, hi]
  have hδr : ∀ r, δ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank (Sum.inr r)) =
      ((unifAt w : Kw w) ^ (cosExp G w * (r.1 + 1)))⁻¹ := by
    intro r
    have hi : (G.V (.top 0)).rank + r.1 + 1 - (G.V (.top 0)).rank = r.1 + 1 := by omega
    simp [hδ, GlobalTheory.FunObj.frame, hi]
  have hQc : Q * diagonal (fun s => δ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank s)) =
      diagonal (fun s => δ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank s)) * Q := by
    ext i j
    rw [mul_diagonal, diagonal_mul, hQ]
    rcases i with i | i <;> rcases j with j | j
    · simp [hδl]
    · simp
    · simp
    · by_cases h : i = j
      · subst h; exact mul_comm _ _
      · simp [diagonal_apply, h]
  obtain ⟨z, hx, hNx⟩ : ∃ z, M' *ᵥ z = x ∧
      ((GlobalTheory.StdFrames.loc w (Lev.finE (G.V (.grid D.R.m 0)) (b 0)) : GL _ (Kw w)) : Matrix _ _ (Kw w)) *ᵥ x =
        M' *ᵥ (diagonal (fun s => δ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank s)) *ᵥ z) := by
    obtain ⟨y, hy⟩ : ∃ y : Fin (G.V (.grid D.R.m 0)).rank → Kw w, y = (((GlobalTheory.StdFrames.loc w (S.B.β D.R.m 0))⁻¹ : GL _ (Kw w)) : Matrix _ _ (Kw w)) *ᵥ x := ⟨_, rfl⟩
    have hxy : ((GlobalTheory.StdFrames.loc w (S.B.β D.R.m 0) : GL _ (Kw w)) : Matrix _ _ (Kw w)) *ᵥ y = x := by
      rw [hy, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    refine ⟨Q *ᵥ fun i => y (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank i), ?_, ?_⟩
    · rw [mulVec_mulVec, ← hLb, submatrix_mulVec_comp, hxy]
    · rw [← hxy, mulVec_mulVec, hcomm, ← mulVec_mulVec, ← submatrix_mulVec_comp _ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank), hLb]
      have hv : (fun i => (diagonal δ *ᵥ y) (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank i)) =
          diagonal (fun s => δ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank s)) *ᵥ fun i => y (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank i) := by
        funext i
        simp [mulVec_diagonal]
      rw [hv]
      simp only [mulVec_mulVec]
      rw [Matrix.mul_assoc, hQc]

  have h1 := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1
  have h2 := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L G.pl sc
  have h3 := GlobalTheory.FunObj.ne_zero_of_conj h2.1 h2.2
  have h1' := GlobalTheory.FunObj.ne_zero_of_conj h1.1 h1.2
  have hA := GlobalTheory.FunObj.count_AA_AAbar w (GlobalTheory.FunObj.Good.badInt_notMem hL hde hc hw)
  have hmo : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact G.pl.modul_ne_bot sc
  have hmb : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    intro h
    have h4 := h2.1
    rw [GlobalTheory.ChiGrid.Places.stA, h, _root_.inv_zero, mul_zero] at h4
    exact h4 rfl
  have hI1 : ∀ r, stairId (G.pl.stA sc) (G.pl.stAbar sc) (D.R.m - 1 - 0) r ≠ 0 := fun r =>
    mul_ne_zero (pow_ne_zero _ h2.1) (inv_ne_zero (pow_ne_zero _ h3))
  have hn1 : ∀ r : Fin (D.R.m - 1 - 0), FractionalIdeal.count D.host.E w
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (D.R.m - 1 - 0) r) = ((cosExp G w * (r.1 + 1) : ℕ) : ℤ) := by
    intro r
    rw [GlobalTheory.FunObj.count_stairId h2.1 h3, GlobalTheory.ChiGrid.Places.stA, GlobalTheory.ChiGrid.Places.stAbar,
      FractionalIdeal.count_mul _ _ h1.1 (inv_ne_zero hmb), FractionalIdeal.count_mul _ _ h1' (inv_ne_zero hmo),
      FractionalIdeal.count_inv, FractionalIdeal.count_inv, GlobalTheory.FunObj.count_modulBar G hw, GlobalTheory.FunObj.count_modul, hA.1, hA.2]
    push_cast
    ring
  have hrId : ∀ r, GlobalTheory.RowShape.rowId D 0 r = stairId D.host.AA D.host.AAbar (D.R.m - 1 - 0) r := by
    intro r
    simp [GlobalTheory.RowShape.rowId, GlobalTheory.RowShape.tiltSc]
  have hI2 : ∀ r, GlobalTheory.RowShape.rowId D 0 r ≠ 0 := fun r => by
    rw [hrId]
    exact mul_ne_zero (pow_ne_zero _ h1.1) (inv_ne_zero (pow_ne_zero _ h1'))
  have hn2 : ∀ r, FractionalIdeal.count D.host.E w (GlobalTheory.RowShape.rowId D 0 r) = ((0 : ℕ) : ℤ) := by
    intro r
    rw [hrId, GlobalTheory.FunObj.count_stairId h1.1 h1', hA.1, hA.2]
    simp
  have hϖ := GlobalTheory.SplitFlip.IsUnif.irreducible (isUnif_unifAt w)
  rw [hN, hNx]
  subst hx
  subst hM'
  rw [hΛ, hR, GlobalTheory.LatticeMembershipValuation.sec_mem_lat_iff p (G.rowDec 0 h0) (neg_ne_zero.2 one_ne_zero),
    GlobalTheory.LatticeMembershipValuation.sec_mem_lat_iff p (G.rowDec 0 h0) (neg_ne_zero.2 one_ne_zero)]
  simp only [mulVec_diagonal, hδl, one_mul, hδr]
  refine and_congr Iff.rfl (forall_congr' fun r => ?_)
  rw [GlobalTheory.LatticeMembershipValuation.sec_mem_idV_iff p hpw hϖ (hI1 r) (hn1 r), GlobalTheory.LatticeMembershipValuation.sec_mem_idV_iff p hpw hϖ (hI2 r) (hn2 r)]
  have hq : ((unifAt w : Kw w) ^ (cosExp G w * (r.1 + 1))) ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
  constructor
  · rintro ⟨o, ho⟩
    refine ⟨o, ?_⟩
    rw [ho, pow_zero, one_mul, ← mul_assoc]
    exact (inv_mul_cancel₀ hq).symm ▸ (one_mul _)
  · rintro ⟨o, ho⟩
    refine ⟨o, ?_⟩
    rw [pow_zero, one_mul] at ho
    rw [← ho, ← mul_assoc]
    exact ((mul_inv_cancel₀ hq).symm ▸ (one_mul _)).symm

end GlobalTheory.BaseMoveAt
