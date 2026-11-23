import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedBy
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LamEqOfRed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelZeroElementReduction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevZeroChar

theorem map_conj_local {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) {β : GL (Fin (c.V 0).rank) (Lev.EAf D)} {b : GA D (c.V 0)}
    {π' : Lev.EAf D →+* G.k} (hπ : ∀ a, π' (toEAf D a) = G.q.pr a) {n : GA D (c.V 0)}
    {q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1)) G.k}
    (hloc : (ofSplit G.q).IsLoc (G.FY 0 (G.s + 1) (Nat.zero_add _)) n q)
    (σ : Fin (c.V 0).rank → XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1)) (hσ : Function.Bijective σ)
    (hM : MovedTo (ofSplit G.q) (c.V 0) b β
      (((G.FY 0 (G.s + 1) (Nat.zero_add _)).β * ((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _)).val).submatrix id σ)) :
    ((β⁻¹ * finE (c.V 0) (b⁻¹ * n * b) * β).val).map π' =
      ((((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _))⁻¹).val * q.val *
        ((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _)).val).submatrix σ σ := by
  set F := G.FY 0 (G.s + 1) (Nat.zero_add _) with hF
  set B := (G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _) with hB
  set p := ofSplit G.q with hp
  have hβ := GlobalTheory.LocMod.StepVec.map_eq_of_movedTo p F (π' := π') hπ B.val σ hM
  have hfin : ∀ g : GA D (c.V 0), (finE (c.V 0) g).val.map π' = (mt (c.V 0) g).map p.π := by
    intro g
    rw [GlobalTheory.LevSplit.finE_val]
    ext i j
    exact hπ _
  have hBB : (B⁻¹).val * B.val = 1 := Units.inv_mul B
  have hmt : ∀ g h : GA D (c.V 0), (mt (c.V 0) (g * h)).map p.π = (mt (c.V 0) g).map p.π * (mt (c.V 0) h).map p.π :=
    fun g h => Matrix.map_mul
  have ht1 : (mt (c.V 0) b).map p.π * (mt (c.V 0) b⁻¹).map p.π = 1 := by
    rw [← hmt, mul_inv_cancel]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  set W := (mt (c.V 0) b⁻¹).map p.π * F.β * B.val with hW
  set W' := (B⁻¹).val * F.γ * (mt (c.V 0) b).map p.π with hW'
  have hWW : W' * W = 1 := by
    rw [hW, hW']
    calc (B⁻¹).val * F.γ * (mt (c.V 0) b).map p.π * ((mt (c.V 0) b⁻¹).map p.π * F.β * B.val)
        = (B⁻¹).val * (F.γ * ((mt (c.V 0) b).map p.π * (mt (c.V 0) b⁻¹).map p.π) * F.β) * B.val := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ht1, Matrix.mul_one, F.γβ, Matrix.mul_one, hBB]
  have hβ' : β.val.map π' = W.submatrix id σ := by
    rw [hβ]; rfl
  have hinv : (β⁻¹).val.map π' = W'.submatrix σ id := by
    refine Matrix.left_inv_eq_left_inv (A := β.val.map π') ?_ ?_
    · rw [← Matrix.map_mul, Units.inv_mul]; exact Matrix.map_one _ (map_zero _) (map_one _)
    · rw [hβ', ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hWW]
      exact Matrix.submatrix_one_equiv (Equiv.ofBijective σ hσ)
  have hn : (mt (c.V 0) n).map p.π = F.β * q.val * F.γ := hloc.2
  rw [Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, hinv, hfin, hβ', hmt, hmt, hn]
  have hs : ∀ (X : Matrix (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1)) (Fin (c.V 0).rank) G.k)
      (Mid : Matrix (Fin (c.V 0).rank) (Fin (c.V 0).rank) G.k)
      (Z : Matrix (Fin (c.V 0).rank) (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1)) G.k),
      X.submatrix σ id * Mid * Z.submatrix id σ = (X * Mid * Z).submatrix σ σ := fun X Mid Z => Matrix.ext fun i j => rfl
  rw [hs]
  congr 1
  rw [hW, hW']
  calc (B⁻¹).val * F.γ * (mt (c.V 0) b).map p.π *
        ((mt (c.V 0) b⁻¹).map p.π * (F.β * q.val * F.γ) * (mt (c.V 0) b).map p.π) *
        ((mt (c.V 0) b⁻¹).map p.π * F.β * B.val)
      = (B⁻¹).val * (F.γ * ((mt (c.V 0) b).map p.π * (mt (c.V 0) b⁻¹).map p.π) * F.β) * q.val *
        (F.γ * ((mt (c.V 0) b).map p.π * (mt (c.V 0) b⁻¹).map p.π) * F.β) * B.val := by
        simp only [Matrix.mul_assoc]
    _ = (B⁻¹).val * q.val * B.val := by simp only [ht1, Matrix.mul_one, F.γβ]

set_option maxHeartbeats 1000000 in

theorem psi_red_at {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Pl D.host.E) (b : GA D (c.V 0))
    (β : GL (Fin (c.V 0).rank) (Lev.EAf D)) (hL : GlobalTheory.LevZero.LocAt G PP b β) (hr : D.R.r ≤ (c.V 0).rank) (n : GA D (c.V 0))
    (q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1)) G.k) (p : ℕ) (hq : q ∈ GlobalTheory.RootEx.N G.k _ (G.s + 1) p)
    (hloc : (ofSplit G.q).IsLoc (G.FY 0 (G.s + 1) (Nat.zero_add _)) n q) (hS : finE (c.V 0) (b⁻¹ * n * b) ∈ St β)
    (hblk : redFn β PP (finE (c.V 0) (b⁻¹ * n * b)) ∈ blockTri (blk2 D.R.r)) (z : 𝓞 D.host.E)
    (hz : Ideal.Quotient.mk PP.asIdeal z = edgeSum (GlobalTheory.chainEdge D.R.k) (upperLeftBlock hr (redFn β PP (finE (c.V 0) (b⁻¹ * n * b))))) :
    (G.S.ψ (((G.S.ϖ⁻¹ : G.kˣ) : G.k) * (ofSplit G.q).pr (z : D.host.E)) : ℂ) = (G.S.ψ (GlobalTheory.RootEx.simpleSum q) : ℂ) := by
  obtain ⟨π', hπ, hred, -, -⟩ := GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D G.k G.q PP hL.idem
  obtain ⟨e, he, hM⟩ := hL.frame (G.s + 1) (Nat.zero_add _)
  have hσ : Function.Bijective (fun i => stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) (Nat.zero_add _) (e.symm i)) :=
    (e.symm.trans (stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) (Nat.zero_add _))).bijective
  have hmat := map_conj_local G hπ hloc _ hσ hM
  obtain ⟨y, hy⟩ := hS
  have hI : β⁻¹ * finE (c.V 0) (b⁻¹ * n * b) * β = intGL _ _ _ y := by
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
        (stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) (Nat.zero_add _) (e.symm (Fin.castLE hr i)))
        (stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) (Nat.zero_add _) (e.symm (Fin.castLE hr j))) else 0) =
      (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q :=
    GlobalTheory.NChainChar.edge_sum_typeFrame D.R.k D.R.t G.s (c.V 0).rank D.R.r p hr hrk e he G.S.ϖ q hN
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
      (ofSplit G.q).pr (z : D.host.E) := hπ (incA D (z : D.host.E))
  have hv : ValuativeRel.valuation G.k ((ofSplit G.q).pr (z : D.host.E) - (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q) < 1 := by
    have h1 : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (w - Formalism.L2.DIV.oToS D.host.F D.host.E z) =
        -((ofSplit G.q).pr (z : D.host.E) - (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q) := by
      rw [map_sub, hpw]
      rw [show (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E z) =
        π' ((Formalism.L2.DIV.oToS D.host.F D.host.E z : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) from rfl, hpz]
      ring
    rw [h1, Valuation.map_neg] at hker
    exact hker
  have hone : G.S.ψ (((G.S.ϖ⁻¹ : G.kˣ) : G.k) * ((ofSplit G.q).pr (z : D.host.E) - (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q)) = 1 := by
    refine (G.S.cond _).2 ?_ _ le_rfl
    have h5 := (G.S.unif _).1 hv
    have h6 : ValuativeRel.valuation G.k (((G.S.ϖ⁻¹ : G.kˣ) : G.k) * (G.S.ϖ : G.k)) = ValuativeRel.valuation G.k ((1 : G.kˣ) : G.k) := by
      rw [Units.inv_mul, Units.val_one]
    rw [← h6, map_mul, map_mul]
    exact mul_le_mul_right h5 _
  have e2 : ((G.S.ϖ⁻¹ : G.kˣ) : G.k) * (ofSplit G.q).pr (z : D.host.E) =
      ((G.S.ϖ⁻¹ : G.kˣ) : G.k) * ((ofSplit G.q).pr (z : D.host.E) - (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q) +
        GlobalTheory.RootEx.simpleSum q := by
    have : ((G.S.ϖ⁻¹ : G.kˣ) : G.k) * (G.S.ϖ : G.k) = 1 := by rw [Units.inv_mul]
    linear_combination (GlobalTheory.RootEx.simpleSum q) * this
  rw [e2, AddChar.map_add_eq_mul, hone, one_mul]

theorem levChi_eq_psiBes : ∀ {D : D7} {c : Comm D} {v : VCom c} (cm : GlobalTheory.ChainOnto.Com D) (st : StAt (c.V 0)) (b : GA D (c.V 0)) (G : cm.Pg → GLoc v) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.LevZero.Bot cm st b G → ∀ (PP : cm.Pg) (n : GA D (c.V 0)) (q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → b⁻¹ * n * b ∈ levS (c.V 0) st.β st.L → levChi (c.V 0) st.β st.L (b⁻¹ * n * b) = psiBes c.ψ (c.bes 0 D.R.rS h0).d 1 (vecB (c.bes 0 D.R.rS h0).o (c.bes 0 D.R.rS h0).ζ) n := by
  intro D c v cm st b G h0 hB PP n q hq hloc hlev
  obtain ⟨hr, ξ, hL⟩ := hB.mem.lev
  have hL' : st.L = Lev.datY (c.V 0).rank D.R.r D.R.t 0 hr cm.Pg ∅ cm.P cm.chi ξ Lev.Frm.B := hL
  have hl := hlev.2
  rw [hL'] at hl
  change finE (c.V 0) (b⁻¹ * n * b) ∈ lev _ _ _ _ at hl
  rw [mem_lev, mem_parLev] at hl
  have hP : (fun PP : cm.Pg => upperLeftBlock hr (redFn st.β PP.1 (finE (c.V 0) (b⁻¹ * n * b)))) ∈ cm.P.H := hl.2
  have hchi : levChi (c.V 0) st.β st.L (b⁻¹ * n * b) = ((cm.P.chi ⟨_, hP⟩ : ℂˣ) : ℂ) := by
    rw [hL']
    unfold levChi levFn
    rw [extendOne_of_mem _ hl.2]
    have e1 : (Lev.datY (c.V 0).rank D.R.r D.R.t 0 hr cm.Pg ∅ cm.P cm.chi ξ Lev.Frm.B).s = 0 := rfl
    have e2 : (Lev.datY (c.V 0).rank D.R.r D.R.t 0 hr cm.Pg ∅ cm.P cm.chi ξ Lev.Frm.B).Q = ∅ := rfl
    simp only [e1, e2, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]
    rfl
  rw [hchi]
  choose x hx using (hB.grp _).1 hP
  rw [hB.chr ⟨_, hP⟩ x hx, Units.coe_prod, Finset.prod_eq_single PP]
  · obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (I := PP.1.asIdeal)
      (edgeSum (GlobalTheory.chainEdge D.R.k) (upperLeftBlock hr (redFn st.β PP.1 (finE (c.V 0) (b⁻¹ * n * b)))))
    rw [GlobalTheory.LevZero.lam_eq_of_red (G PP) PP.1 (hB.loc PP).idem (x PP) _ (hx PP) z hz]
    rw [psi_red_at (G PP) PP.1 b st.β (hB.loc PP) hr n q _ hq hloc hl.1.2.1 (blockTri_blkOf_le _ _ (hl.1.2.2.1 PP.1 PP.2)) z hz]
    rw [GlobalTheory.LocBesChar.psiBes_isLoc D (G PP).k (ofSplit (G PP).q) c.ψ (G PP).S.ψ (G PP).char D.R.rS
      (c.B 0 D.R.rS h0) ((G PP).sc 0) _ ((G PP).s + 1) ((G PP).FX 0 (by omega)) ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _))
      ((G PP).bes 0 D.R.rS h0 ((G PP).s + 1) (Nat.zero_add _)) n q hq hloc]
  · intro PP' _ hne
    obtain ⟨e, he⟩ := hB.com.split
    have h1 := GlobalTheory.NChainChar.redFn_conj_eq_one he PP.2 (hB.loc PP).idem hloc.1 b hl.1.2.1 PP'.2
      (fun h => hne (Subtype.ext h).symm)
    have h2 : Ideal.Quotient.mk PP'.1.asIdeal (0 : 𝓞 D.host.E) = edgeSum (GlobalTheory.chainEdge D.R.k)
        (upperLeftBlock hr (redFn st.β PP'.1 (finE (c.V 0) (b⁻¹ * n * b)))) := by
      rw [h1, map_zero]
      unfold upperLeftBlock
      rw [blockDiagonalExtendByOnePrimeField_one]
      symm
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      split_ifs with hij
      · rw [Units.val_one, Matrix.one_apply_ne]
        intro e; rw [e] at hij; exact absurd hij.1 (by omega)
      · rfl
    rw [GlobalTheory.LevZero.lam_eq_of_red (G PP') PP'.1 (hB.loc PP').idem (x PP') _ (hx PP') 0 h2]
    simp [GlobalTheory.LocMod.Place.pr]
  · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.LevZeroChar
