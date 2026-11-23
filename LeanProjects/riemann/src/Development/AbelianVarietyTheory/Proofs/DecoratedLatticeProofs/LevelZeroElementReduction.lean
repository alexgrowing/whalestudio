import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BesselCompatibility
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselCharacterLocalElementEqSimpleEntrySum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LambdaValueEdgeSumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReductionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardOrderSymmInr
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NChainChar

theorem map_conj_local {D : D7} {u : D.what₂.Word} {d : GlobalTheory.SeeSaw.Dat D u} {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E} {PP : Pl D.host.E} (G : GlobalTheory.LocMod.GAt d τ PP) {π' : Lev.EAf D →+* G.k} (hπ : ∀ a, π' (toEAf D a) = G.q.pr a) {n : GA D (d.st 0).V} {q : GL (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1)) G.k}
    (hloc : (GlobalTheory.LocMod.ofSplit G.q).IsLoc (G.FY 0 (G.s + 1) (Nat.zero_add _)) n q)
    (σ : Fin (d.st 0).V.rank → GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1)) (hσ : Function.Bijective σ)
    (hM : GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit G.q) (d.st 0).V (d.t 0) (d.st 0).β
      (((G.FY 0 (G.s + 1) (Nat.zero_add _)).β * ((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _)).val).submatrix id σ)) :
    (((d.st 0).β⁻¹ * finE (d.st 0).V ((d.t 0)⁻¹ * n * d.t 0) * (d.st 0).β).val).map π' =
      ((((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _))⁻¹).val * q.val *
        ((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _)).val).submatrix σ σ := by
  set F := G.FY 0 (G.s + 1) (Nat.zero_add _) with hF
  set B := (G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _) with hB
  set p := GlobalTheory.LocMod.ofSplit G.q with hp
  have hβ := GlobalTheory.LocMod.StepVec.map_eq_of_movedTo p F (π' := π') hπ B.val σ hM
  have hfin : ∀ g : GA D (d.st 0).V, (finE (d.st 0).V g).val.map π' = (mt (d.st 0).V g).map p.π := by
    intro g
    rw [GlobalTheory.LevSplit.finE_val]
    ext i j
    exact hπ _
  have hBB : (B⁻¹).val * B.val = 1 := Units.inv_mul B
  have hmt : ∀ g h : GA D (d.st 0).V, (mt (d.st 0).V (g * h)).map p.π = (mt (d.st 0).V g).map p.π * (mt (d.st 0).V h).map p.π :=
    fun g h => Matrix.map_mul
  have ht1 : (mt (d.st 0).V (d.t 0)).map p.π * (mt (d.st 0).V (d.t 0)⁻¹).map p.π = 1 := by
    rw [← hmt, mul_inv_cancel]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  set W := (mt (d.st 0).V (d.t 0)⁻¹).map p.π * F.β * B.val with hW
  set W' := (B⁻¹).val * F.γ * (mt (d.st 0).V (d.t 0)).map p.π with hW'
  have hWW : W' * W = 1 := by
    rw [hW, hW']
    calc (B⁻¹).val * F.γ * (mt (d.st 0).V (d.t 0)).map p.π * ((mt (d.st 0).V (d.t 0)⁻¹).map p.π * F.β * B.val)
        = (B⁻¹).val * (F.γ * ((mt (d.st 0).V (d.t 0)).map p.π * (mt (d.st 0).V (d.t 0)⁻¹).map p.π) * F.β) * B.val := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ht1, Matrix.mul_one, F.γβ, Matrix.mul_one, hBB]
  have hβ' : (d.st 0).β.val.map π' = W.submatrix id σ := by
    rw [hβ]; rfl
  have hinv : ((d.st 0).β⁻¹).val.map π' = W'.submatrix σ id := by
    refine Matrix.left_inv_eq_left_inv (A := (d.st 0).β.val.map π') ?_ ?_
    · rw [← Matrix.map_mul, Units.inv_mul]; exact Matrix.map_one _ (map_zero _) (map_one _)
    · rw [hβ', ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hWW]
      exact Matrix.submatrix_one_equiv (Equiv.ofBijective σ hσ)
  have hn : (mt (d.st 0).V n).map p.π = F.β * q.val * F.γ := hloc.2
  rw [Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, hinv, hfin, hβ', hmt, hmt, hn]
  have hs : ∀ (X : Matrix (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1)) (Fin (d.st 0).V.rank) G.k)
      (Mid : Matrix (Fin (d.st 0).V.rank) (Fin (d.st 0).V.rank) G.k)
      (Z : Matrix (Fin (d.st 0).V.rank) (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1)) G.k),
      X.submatrix σ id * Mid * Z.submatrix id σ = (X * Mid * Z).submatrix σ σ := fun X Mid Z => Matrix.ext fun i j => rfl
  rw [hs]
  congr 1
  rw [hW, hW']
  have ht2 : (mt (d.st 0).V (d.t 0)⁻¹).map p.π * (mt (d.st 0).V (d.t 0)).map p.π = 1 := by
    rw [← hmt, inv_mul_cancel]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  calc (B⁻¹).val * F.γ * (mt (d.st 0).V (d.t 0)).map p.π *
        ((mt (d.st 0).V (d.t 0)⁻¹).map p.π * (F.β * q.val * F.γ) * (mt (d.st 0).V (d.t 0)).map p.π) *
        ((mt (d.st 0).V (d.t 0)⁻¹).map p.π * F.β * B.val)
      = (B⁻¹).val * (F.γ * ((mt (d.st 0).V (d.t 0)).map p.π * (mt (d.st 0).V (d.t 0)⁻¹).map p.π) * F.β) * q.val *
        (F.γ * ((mt (d.st 0).V (d.t 0)).map p.π * (mt (d.st 0).V (d.t 0)⁻¹).map p.π) * F.β) * B.val := by
        simp only [Matrix.mul_assoc]
    _ = (B⁻¹).val * q.val * B.val := by simp only [ht1, Matrix.mul_one, F.γβ]

theorem edge_sum_typeFrame {K : Type} [Field K] (κ τ s N r p : ℕ) (hr : r ≤ N) (hrk : r = κ + (s + 1))
    (e : GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) 0 ≃ Fin N) (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e) (ϖ : Kˣ)
    (q : GL (GlobalTheory.StepData.XIx (Fin κ) (Fin τ) 0 ⊕ Fin (s + 1)) K) (hq : GlobalTheory.RootEx.InN p q) :
    (∑ i : Fin r, ∑ j : Fin r, if GlobalTheory.chainEdge κ i j then
      (((GlobalTheory.StepData.typeFrame ϖ (GlobalTheory.StepData.stdOrd (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _))).bas⁻¹).val * q.val *
        (GlobalTheory.StepData.typeFrame ϖ (GlobalTheory.StepData.stdOrd (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _))).bas.val)
        (GlobalTheory.StepData.stdOrd (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _) (e.symm (Fin.castLE hr i)))
        (GlobalTheory.StepData.stdOrd (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _) (e.symm (Fin.castLE hr j))) else 0) =
      (ϖ : K) * GlobalTheory.RootEx.simpleSum q := by
  subst hrk
  rw [GlobalTheory.SymChain.NonZeroAt.typeFrame_bas_inv_val, GlobalTheory.SymChain.NonZeroAt.typeFrame_bas_val]
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  let ε : Fin κ ⊕ Fin (s + 1) ≃ Fin (κ + (s + 1)) := finSumFinEquiv
  have hε : ∀ a, e.symm (Fin.castLE hr (ε a)) = Sum.inl a := by
    intro a
    rw [Equiv.symm_apply_eq]
    apply Fin.ext
    rw [he]
    rcases a with a | a <;> simp [ε, GlobalTheory.SymBridge.zPos]
  rw [← ε.sum_comp]
  simp only [← ε.sum_comp (fun j => ite _ _ _), hε]
  have h1 : ∀ i : Fin κ, GlobalTheory.StepData.stdOrd (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _) (Sum.inl (Sum.inl i)) =
      Sum.inl (Sum.inl (Sum.inl i)) := fun i => rfl
  have h2 : ∀ i : Fin (s + 1), GlobalTheory.StepData.stdOrd (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _) (Sum.inl (Sum.inr i)) =
      Sum.inr i := fun i => GlobalTheory.StepData.standardOrderExtendedBasis_apply_low_block (Fin κ) (Fin τ) 0 (s + 1) (Nat.zero_add _) i
  have hX : ∀ a b : GlobalTheory.StepData.XIx (Fin κ) (Fin τ) 0,
      q.val (Sum.inl a) (Sum.inl b) = (1 : Matrix (GlobalTheory.StepData.XIx (Fin κ) (Fin τ) 0 ⊕ Fin (s + 1)) _ K) (Sum.inl a) (Sum.inl b) :=
    fun a b => hq _ _ le_rfl
  have eε1 : ∀ i : Fin κ, (ε (Sum.inl i)).val = i.val := fun i => rfl
  have eε2 : ∀ i : Fin (s + 1), (ε (Sum.inr i)).val = κ + i.val := fun i => rfl
  simp only [Fintype.sum_sum_type, h1, h2, Sum.elim_inl, Sum.elim_inr, one_mul, mul_one, GlobalTheory.chainEdge, eε1, eε2]
  have A : ∀ x : Fin κ, ((∑ x_1 : Fin κ,
            if (x_1 : ℕ) = x + 1 ∧ (x : ℕ) + 1 ≠ κ then q.val (Sum.inl (Sum.inl (Sum.inl x))) (Sum.inl (Sum.inl (Sum.inl x_1)))
            else 0) +
          ∑ x_1 : Fin (s + 1),
            if κ + (x_1 : ℕ) = x + 1 ∧ (x : ℕ) + 1 ≠ κ then q.val (Sum.inl (Sum.inl (Sum.inl x))) (Sum.inr x_1) * (ϖ : K) ^ ((x_1 : ℕ) + 1)
            else 0) = 0 := by
    intro x
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
    · intro x_1 _
      rw [if_neg]
      omega
    · intro x_1 _
      split_ifs with h
      · rw [hX, Matrix.one_apply_ne]
        intro e
        have : x = x_1 := by simpa using e
        subst this
        omega
      · rfl
  have B : ∀ x : Fin (s + 1), ((∑ x_1 : Fin κ,
            if (x_1 : ℕ) = κ + x + 1 ∧ κ + (x : ℕ) + 1 ≠ κ then
              ((ϖ : K) ^ ((x : ℕ) + 1))⁻¹ * q.val (Sum.inr x) (Sum.inl (Sum.inl (Sum.inl x_1)))
            else 0) +
          ∑ x_1 : Fin (s + 1),
            if κ + (x_1 : ℕ) = κ + x + 1 ∧ κ + (x : ℕ) + 1 ≠ κ then
              ((ϖ : K) ^ ((x : ℕ) + 1))⁻¹ * q.val (Sum.inr x) (Sum.inr x_1) * (ϖ : K) ^ ((x_1 : ℕ) + 1)
            else 0) = (ϖ : K) * ∑ x_1 : Fin (s + 1), if (x_1 : ℕ) = x + 1 then q.val (Sum.inr x) (Sum.inr x_1) else 0 := by
    intro x
    rw [Finset.sum_eq_zero, zero_add, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun x_1 _ => ?_
      by_cases h : (x_1 : ℕ) = x + 1
      · rw [if_pos ⟨by omega, by omega⟩, if_pos h, h]
        have hϖ : (ϖ : K) ≠ 0 := ϖ.ne_zero
        field_simp
        ring
      · rw [if_neg (by omega), if_neg h, mul_zero]
    · intro x_1 _
      rw [if_neg]
      have := x_1.2
      omega
  simp only [A, B, Finset.sum_const_zero, zero_add, ← Finset.mul_sum]
  rfl

set_option maxHeartbeats 1000000 in

theorem psi_red_at : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (PP : Pl D.host.E) (G : GlobalTheory.LocMod.GAt d τ PP) (hr : D.R.r ≤ (d.st 0).V.rank) (n : GA D (d.st 0).V) (q : GL (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1)) G.k) (p : ℕ), q ∈ GlobalTheory.RootEx.N G.k _ (G.s + 1) p → (GlobalTheory.LocMod.ofSplit G.q).IsLoc (G.FY 0 (G.s + 1) (Nat.zero_add _)) n q → finE (d.st 0).V ((d.t 0)⁻¹ * n * d.t 0) ∈ St (d.st 0).β → redFn (d.st 0).β PP (finE (d.st 0).V ((d.t 0)⁻¹ * n * d.t 0)) ∈ blockTri (blk2 D.R.r) → ∀ z : 𝓞 D.host.E, Ideal.Quotient.mk PP.asIdeal z = edgeSum (GlobalTheory.chainEdge D.R.k) (upperLeftBlock hr (redFn (d.st 0).β PP (finE (d.st 0).V ((d.t 0)⁻¹ * n * d.t 0)))) → (G.S.ψ (((G.S.ϖ⁻¹ : G.kˣ) : G.k) * (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E)) : ℂ) = (G.S.ψ (GlobalTheory.RootEx.simpleSum q) : ℂ) := by
  intro D u d τ PP G hr n q p hq hloc hS hblk z hz
  obtain ⟨π', hπ, hred, -, -⟩ := GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D G.k G.q PP G.idem
  obtain ⟨e, he, hM⟩ := G.frame 0 (G.s + 1) (Nat.zero_add _)
  have hσ : Function.Bijective (fun i => GlobalTheory.StepData.stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) (Nat.zero_add _) (e.symm i)) :=
    (e.symm.trans (GlobalTheory.StepData.stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) (Nat.zero_add _))).bijective
  have hmat := map_conj_local G hπ hloc _ hσ hM
  obtain ⟨y, hy⟩ := hS
  have hI : (d.st 0).β⁻¹ * finE (d.st 0).V ((d.t 0)⁻¹ * n * d.t 0) * (d.st 0).β = intGL _ _ _ y := by
    rw [← hy]
    simp [frGL, MulAut.conj_apply]
    group
  rw [hI] at hmat
  rw [← hy, redFn_frGL] at hz hblk
  unfold edgeSum at hz
  rw [upper_block_val_submatrix hr hblk] at hz
  have hrk : D.R.r = D.R.k + (G.s + 1) := by
    have := G.hs
    unfold Ranks.r
    omega
  have hN := (GlobalTheory.RootEx.Radical.mem_N_iff q).1 hq
  have hsum : (∑ i : Fin D.R.r, ∑ j : Fin D.R.r, if GlobalTheory.chainEdge D.R.k i j then
      ((((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _))⁻¹).val * q.val *
        ((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _)).val)
        (GlobalTheory.StepData.stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) (Nat.zero_add _) (e.symm (Fin.castLE hr i)))
        (GlobalTheory.StepData.stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) (Nat.zero_add _) (e.symm (Fin.castLE hr j))) else 0) =
      (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q :=
    edge_sum_typeFrame D.R.k D.R.t G.s (d.st 0).V.rank D.R.r p hr hrk e he G.S.ϖ q hN
  set w : Formalism.L2.Herm.intAf D.host.F D.host.E := ∑ i : Fin D.R.r, ∑ j : Fin D.R.r,
    if GlobalTheory.chainEdge D.R.k i j then y.val (Fin.castLE hr i) (Fin.castLE hr j) else 0 with hw
  have hres : resS D.host.F PP w = Ideal.Quotient.mk PP.asIdeal z := by
    rw [hz, hw, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · rfl
    · exact map_zero _
  have hker := (hred.ker (w - Formalism.L2.DIV.oToS D.host.F D.host.E z)).1 (by
    rw [map_sub, hres, Formalism.L2.DIV.resS_oToS, sub_self])
  have hpw : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) w = (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q := by
    rw [← hsum, hw, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · have := congrFun (congrFun hmat (Fin.castLE hr i)) (Fin.castLE hr j)
      exact this
    · exact map_zero _
  have hpz : π' ((Formalism.L2.DIV.oToS D.host.F D.host.E z : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) =
      (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E) := hπ (incA D (z : D.host.E))
  have hv : ValuativeRel.valuation G.k ((GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E) - (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q) < 1 := by
    have h1 : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (w - Formalism.L2.DIV.oToS D.host.F D.host.E z) =
        -((GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E) - (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q) := by
      rw [map_sub, hpw]
      rw [show (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E z) =
        π' ((Formalism.L2.DIV.oToS D.host.F D.host.E z : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) from rfl, hpz]
      ring
    rw [h1, Valuation.map_neg] at hker
    exact hker
  have hone : G.S.ψ (((G.S.ϖ⁻¹ : G.kˣ) : G.k) * ((GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E) - (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q)) = 1 := by
    refine (G.S.cond _).2 ?_ _ le_rfl
    have h5 := (G.S.unif _).1 hv
    have h6 : ValuativeRel.valuation G.k (((G.S.ϖ⁻¹ : G.kˣ) : G.k) * (G.S.ϖ : G.k)) = ValuativeRel.valuation G.k ((1 : G.kˣ) : G.k) := by
      rw [Units.inv_mul, Units.val_one]
    rw [← h6, map_mul, map_mul]
    exact mul_le_mul_right h5 _
  have e2 : ((G.S.ϖ⁻¹ : G.kˣ) : G.k) * (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E) =
      ((G.S.ϖ⁻¹ : G.kˣ) : G.k) * ((GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E) - (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q) +
        GlobalTheory.RootEx.simpleSum q := by
    have : ((G.S.ϖ⁻¹ : G.kˣ) : G.k) * (G.S.ϖ : G.k) = 1 := by rw [Units.inv_mul]
    linear_combination (GlobalTheory.RootEx.simpleSum q) * this
  rw [e2, AddChar.map_add_eq_mul, hone, one_mul]

theorem redFn_conj_eq_one {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {a e : AE D} {P : Finset (Pl D.host.E)}
    {PP Q : Pl D.host.E} (ha : IsIdemSum a P) (hPP : PP ∈ P) (he : Formalism.L2.NTheta.IsIdemAt e PP) {n : GA D V}
    (hn : SuppAt e V n) (t : GA D V) (hS : finE V (t⁻¹ * n * t) ∈ St β) (hQ : Q ∈ P) (hne : PP ≠ Q) :
    redFn β Q (finE V (t⁻¹ * n * t)) = 1 := by
  refine GlobalTheory.DiagLiftFix.redFn_eq_one_of_ne ha hPP he ?_ hS hQ hne
  intro i j
  have h2 : mt V t⁻¹ * mt V t = 1 := by
    show mt V (t⁻¹ * t) = 1
    rw [inv_mul_cancel]; rfl
  have e1 : mt V (t⁻¹ * n * t) - 1 = mt V t⁻¹ * (mt V n - 1) * mt V t := by
    show mt V t⁻¹ * mt V n * mt V t - 1 = _
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h2]
  rw [e1]
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  have := hn m l
  linear_combination (mt V t⁻¹ i m * mt V t l j) * this

theorem levChi_eq_psiBes : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d τ PP.1) (cG : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), d.Base → IsTypePlaces d.c.Pg → GlobalTheory.LocMod.PinGBy G cG → ∀ (PP : d.c.Pg) (n : GA D (d.st 0).V) (q : GL (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (GlobalTheory.LocMod.ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → (d.t 0)⁻¹ * n * d.t 0 ∈ d.lev 0 → levChi (d.st 0).V (d.st 0).β (d.st 0).L ((d.t 0)⁻¹ * n * d.t 0) = psiBes d.c.ψ (d.bes 0 D.R.rS h0).d 1 (vecB (d.bes 0 D.R.rS h0).o (d.bes 0 D.R.rS h0).ζ) n := by
  intro D u d τ G cG h0 hB hTP hPG PP n q hq hloc hlev
  have hm : 0 < D.R.m := by omega
  obtain ⟨hr, ξ, hL⟩ := (hB.st 0 hm).lev
  have hl := hlev.2
  rw [hL] at hl
  change finE (d.st 0).V ((d.t 0)⁻¹ * n * d.t 0) ∈ lev _ _ _ _ at hl
  rw [mem_lev, mem_parLev] at hl
  have hP : (fun PP : d.c.Pg => upperLeftBlock hr (redFn (d.st 0).β PP.1 (finE (d.st 0).V ((d.t 0)⁻¹ * n * d.t 0)))) ∈ d.c.P.H := hl.2
  have hchi : levChi (d.st 0).V (d.st 0).β (d.st 0).L ((d.t 0)⁻¹ * n * d.t 0) = ((d.c.P.chi ⟨_, hP⟩ : ℂˣ) : ℂ) := by
    rw [hL]
    unfold levChi levFn
    rw [extendOne_of_mem _ hl.2]
    have e1 : (datY (d.st 0).V.rank D.R.r D.R.t 0 hr d.c.Pg ∅ d.c.P d.c.chi ξ Frm.B).s = 0 := rfl
    have e2 : (datY (d.st 0).V.rank D.R.r D.R.t 0 hr d.c.Pg ∅ d.c.P d.c.chi ξ Frm.B).Q = ∅ := rfl
    simp only [e1, e2, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]
    rfl
  rw [hchi]
  choose x hx using (hPG.grp _).1 hP
  rw [hPG.chr ⟨_, hP⟩ x hx, Units.coe_prod, Finset.prod_eq_single PP]
  · obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (I := PP.1.asIdeal)
      (edgeSum (GlobalTheory.chainEdge D.R.k) (upperLeftBlock hr (redFn (d.st 0).β PP.1 (finE (d.st 0).V ((d.t 0)⁻¹ * n * d.t 0)))))
    rw [GlobalTheory.T.lambda_value_edge_sum D u d τ PP.1 (G PP) (x PP) _ (hx PP) z hz]
    rw [psi_red_at D u d τ PP.1 (G PP) hr n q _ hq hloc hl.1.2.1 (blockTri_blkOf_le _ _ (hl.1.2.2.1 PP.1 PP.2)) z hz]
    rw [GlobalTheory.LocBesChar.psiBes_isLoc D (G PP).k (GlobalTheory.LocMod.ofSplit (G PP).q) d.c.ψ (G PP).S.ψ (G PP).char D.R.rS
      (d.B 0 D.R.rS h0) ((G PP).sc 0) _ ((G PP).s + 1) ((G PP).FX 0 (by omega)) ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _))
      ((G PP).bes 0 D.R.rS h0 ((G PP).s + 1) (Nat.zero_add _)) n q hq hloc]
  · intro PP' _ hne
    obtain ⟨e, he⟩ := hB.com.split
    have h1 := redFn_conj_eq_one he PP.2 (G PP).idem hloc.1 (d.t 0) hl.1.2.1 PP'.2 (fun h => hne (Subtype.ext h).symm)
    have h2 : Ideal.Quotient.mk PP'.1.asIdeal (0 : 𝓞 D.host.E) = edgeSum (GlobalTheory.chainEdge D.R.k)
        (upperLeftBlock hr (redFn (d.st 0).β PP'.1 (finE (d.st 0).V ((d.t 0)⁻¹ * n * d.t 0)))) := by
      rw [h1, map_zero]
      unfold upperLeftBlock
      rw [blockDiagonalExtendByOnePrimeField_one]
      symm
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      split_ifs with hij
      · rw [Units.val_one, Matrix.one_apply_ne]
        intro e; rw [e] at hij; exact absurd hij.1 (by omega)
      · rfl
    rw [GlobalTheory.T.lambda_value_edge_sum D u d τ PP'.1 (G PP') (x PP') _ (hx PP') 0 h2]
    simp [GlobalTheory.LocMod.Place.pr]
  · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.NChainChar
