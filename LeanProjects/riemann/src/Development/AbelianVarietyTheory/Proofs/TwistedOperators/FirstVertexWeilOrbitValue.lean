import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowMapVUpdateZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EdgeFactorNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridStandardVacuumScalarEqProdLocalPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatHatStabOfHatL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowPt0InvMemStdLatIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetIdeleConjugatedTopPointEqProdLocal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetUnitaryConjAtPlaceEqDetLatticeBasisComponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridRowLevelZeroInfUnitaryEqDatumLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Matrix ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.RowVacScalar GlobalTheory.FirstRowTermLaw GlobalTheory.FirstRowEndLaw

noncomputable section

namespace GlobalTheory.FirstRowScalar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

private theorem cpt_tensor_comm_eq_finAdEquiv (Q : Pl D.host.E) (y : TensorProduct D.host.F (Af D.host.F) D.host.E) :
    GlobalTheory.StdFrames.cpt Q ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) y) =
      (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E y) Q := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | tmul a x =>
    rw [Algebra.TensorProduct.comm_tmul]
    simp only [GlobalTheory.StdFrames.cpt, RingHom.comp_apply]
    rw [GlobalTheory.StdFrames.toAd_spec]
    show _ = (GlobalTheory.LFun.toFinAd D.host.F D.host.E (TensorProduct.tmul D.host.F a x)) Q
    rw [GlobalTheory.LFun.toFinAd_tmul, mul_comm]
    rfl
  | add y z hy hz =>
    simp only [map_add] at *
    rw [hy, hz]
    rfl

private theorem eq_locIdele_of_idemAt {e : AE D} {w : Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e w) (x : (AE D)ˣ) (d : AE D)
    (hx : (x : AE D) = e * d + (1 - e)) (y : (Kw w)ˣ) (hy : (y : Kw w) = GlobalTheory.StdFrames.cpt w (toEAf D d)) :
    x = GlobalTheory.LFun.locIdele D.host.F w y := by
  have hs : IsIdemSum e {w} := ⟨⟨fun _ => e, by simpa using he, by simp⟩, he.1.2.1⟩
  obtain ⟨hinf, hin, hout⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum hs
  apply GlobalTheory.LFun.eq_locIdele
  · show infPart D (x : AE D) = 1
    rw [hx, map_add, map_mul, map_sub, map_one, hinf]
    ring
  · refine Subtype.ext (funext fun Q => ?_)
    have hb := cpt_tensor_comm_eq_finAdEquiv Q (finPart D (x : AE D))
    change GlobalTheory.StdFrames.cpt Q (toEAf D (x : AE D)) = _ at hb
    change (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (x : AE D))) Q =
      Neutral.B1.finiteSingle D.host.E w (y : Kw w) Q
    rw [← hb, hx]
    simp only [map_add, map_mul, map_sub, map_one]
    by_cases hQ : Q = w
    · subst hQ
      rw [GlobalTheory.LFun.finSingle_self, hin Q (by simp), ← hy]
      ring
    · rw [GlobalTheory.LFun.finSingle_ne hQ, hout Q (by simpa using hQ)]
      ring

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem detIdl_conj {e : AE D} {w : Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e w) (V : HSp D) (k u : GfC V) {n : ℕ}
    (h : n = V.rank) (β : GL (Fin V.rank) (Lev.EAf D)) :
    detIdl e V ((u⁻¹ * k * u : GfC V) : GA D V) = GlobalTheory.LFun.locIdele D.host.F w (gdet (inBasis h β w (finG V k))) := by
  have hee : e * e = e := he.1.1
  refine eq_locIdele_of_idemAt he _ (Formalism.L2.Theta.mt V ((u⁻¹ * k * u : GfC V) : GA D V)).det ?_ _ ?_
  · unfold detIdl
    rw [dif_pos hee]
    rfl
  · rw [GlobalTheory.TopLevelInv.det_mt_conj V k u, RingHom.map_det (toEAf D), RingHom.mapMatrix_apply,
      ← GlobalTheory.TopLevelInv.val_finG, Matrix.GeneralLinearGroup.val_det_apply]
    simp only [inBasis, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [GlobalTheory.TopLevelInv.det_val_reGL, GlobalTheory.TopLevelInv.val_loc, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      GlobalTheory.TopLevelInv.det_val_conj_inv]

variable {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem kapAt_mem (S : GridChoice W U) {t : T} {k : FinPt G (.grid 0 D.R.m)}
    (hk : finG (G.V (.grid 0 D.R.m)) k ∈ S.levRow t 0 (Nat.zero_le _)) (w : locPl G t) :
    kapAt S t w.1 k ∈ givenLevel G t w.1 (0, D.R.m) := by
  exact Subgroup.mem_iInf.mp (Subgroup.mem_inf.mp hk).1 w

set_option maxHeartbeats 1000000 in

theorem splitScal_eq (S : GridChoice W U) {μ₀ : T} (hL : L.Is μ₀) {t : T} {k : FinPt G (.grid 0 D.R.m)}
    (hk : finG (G.V (.grid 0 D.R.m)) k ∈ S.levRow t 0 (Nat.zero_le _)) (w : locPl G t) :
    splitScal G (.chi 0 D.R.m) w.1 1 ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 =
      (locGrid G t w).edgeFactor .one (Pi.mulSingle (0, D.R.m) (kapAt S t w k)) (.ex 0 D.R.m) := by
  have hm1 : 1 ≤ D.R.m := (GlobalTheory.FirstRowVertex.firstIx D).pos
  have h1 : detIdl (idemAt w.1) (G.pS (.chi 0 D.R.m)) 1 = 1 := by
    by_cases he : idemAt w.1 * idemAt w.1 = idemAt w.1
    · ext; rw [detIdl_val he]; simp [Formalism.L2.Theta.mt]
    · simp [detIdl, he]
  have hKO := GlobalTheory.FirstRowLat.givenLevel_zero_le_KO G t w.1 D.R.m hm1 _ (kapAt_mem S hk w)
  have hap : ∀ z : ℂ, apow (gdet (Assignment.one.read (kapAt S t w.1 k))) z = 1 := by
    intro z
    have hx : Assignment.one.read (kapAt S t w.1 k) ∈ KO (Kw w.1) (Fin ((locGrid G t w.1).rank (0, D.R.m))) :=
      invT_mem_KO hKO
    simp only [apow, gdet, GlobalTheory.LGrp.nabs_det_of_mem_KO hx, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow]
  have hd := detIdl_conj (GlobalTheory.RowVacScalar.isIdemAt_idemAt hL G t w.2) (G.V (.grid 0 D.R.m)) k
    (S.N.u (.grid 0 D.R.m)) (rank_vertex G t w.1 (X := (0, D.R.m)) ⟨Nat.zero_le _, le_rfl⟩) (S.B.β 0 D.R.m)
  simp only [GlobalTheory.RowVacScalar.splitScal, GlobalTheory.SplitFlip.Grid.edgeFactor, GlobalTheory.SplitFlip.Grid.kappa,
    GlobalTheory.SplitFlip.Grid.blockChar, GlobalTheory.SplitFlip.Edge.src, GlobalTheory.SplitFlip.Edge.tgt, Pi.mulSingle_eq_same]
  rw [GlobalTheory.FirstRowTermLaw.mulSingle_ne _ (show ((0 + 1, D.R.m) : ℕ × ℕ) ≠ (0, D.R.m) by simp), h1]
  simp only [map_one, inv_one, Units.val_one, mul_one, apow_one, hap]
  unfold splitFacO
  simp only [map_one, inv_one, one_mul]
  erw [hd]
  have hpar : Odd (G.pS (.chi 0 D.R.m)).rank ↔ ((locGrid G t w.1).rank (0, D.R.m) + 1) % 2 = 1 := by
    have hr0 : (locGrid G t w.1).rank (0, D.R.m) = D.R.r + D.R.m * D.R.t := by
      rw [rank_vertex G t w.1 (X := (0, D.R.m)) ⟨Nat.zero_le _, le_rfl⟩, ← rank_zero_m G, D.sp.X'_rank]
      rfl
    have hr1 : (G.pS (.chi 0 D.R.m)).rank = D.R.r + D.R.m * D.R.t + 1 * sLen D :=
      (G.sp.V_is 1 D.R.m le_rfl hm1 le_rfl).rank
    have hs : sLen D % 2 = 1 := Nat.odd_iff.mp (odd_sLen (D := D))
    rw [hr0, hr1, Nat.odd_iff]
    generalize D.R.r + D.R.m * D.R.t = a
    omega
  rw [show (locGrid G t w.1).chi ((locGrid G t w.1).m - 0) = (G.ch.chiH D.R.m).loc w.1 from rfl,
    show (locGrid G t w.1).eta = L.C.eta.loc w.1 from rfl,
    ← GlobalTheory.LFun.locChar_eq_of_chrEq (G.ch.chi_eq D.R.m hm1 le_rfl) w.1, ← GlobalTheory.LFun.locChar_eq_of_chrEq hL.eta w.1]
  simp only [GridData.chrS, GridData.chr, Formalism.IndefR.Lift.attChr, Nat.sub_zero]
  unfold FirstRowTermLaw.kapAt
  rcases Nat.mod_two_eq_zero_or_one ((locGrid G t w.1).rank (0, D.R.m) + 1) with h0 | h0
  · have ho : ¬ Odd (G.pS (.chi 0 D.R.m)).rank := fun h => by simp [hpar.mp h] at h0
    rw [if_neg ho, h0]
    simp [GlobalTheory.LFun.locChar]
    done
  · rw [if_pos (hpar.mpr h0), h0]
    simp [GlobalTheory.LFun.locChar, div_eq_mul_inv]
    done

theorem one_lat (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (y : Fin V.rank → TensorProduct D.host.F (Af D.host.F) D.host.E) :
    y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt V 1).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) := by
  have h1 : Formalism.L2.Theta.mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]
  rw [h1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

theorem toPair_zero (G : GridData L sc) (x : GA D (G.V (.grid 0 D.R.m))) :
    G.toPair (.chi 0 D.R.m : Pair T) x 1 = (1, x) := by
  simp [GridData.toPair]

set_option maxHeartbeats 1000000 in

theorem moved_latT (S : GridChoice W U) {μ₀ : T} (hL : L.Is μ₀) {t : T} {k : FinPt G (.grid 0 D.R.m)}
    (hk : finG (G.V (.grid 0 D.R.m)) k ∈ S.levRow t 0 (Nat.zero_le _)) (y) :
    y ∈ latHat D.host.F D.host.E (S.N.latT (.chi 0 D.R.m) : Set (Fin (G.pT (.chi 0 D.R.m)).rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt (G.pT (.chi 0 D.R.m)) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1).map (finPart D)).mulVec y ∈
        latHat D.host.F D.host.E (S.N.latT (.chi 0 D.R.m) : Set (Fin (G.pT (.chi 0 D.R.m)).rank → D.host.E)) := by
  refine GlobalTheory.RowMovedLat.latHat_stab_of_hatL _ _ _ (fun z => ?_) y
  have hU := S.N.u_lat (.grid 0 D.R.m) ⟨Nat.zero_le _, rfl⟩
  have hK : ∀ x, x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.grid 0 D.R.m)) ↔
      (Formalism.IndefR.Lev.finE (G.V (.grid 0 D.R.m)) k.1).val *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.grid 0 D.R.m)) :=
    GlobalTheory.FirstRowLat.levRow_zero_stab S hL t k hk
  have hm : Formalism.IndefR.Lev.finE (G.V (.grid 0 D.R.m)) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 =
      (Formalism.IndefR.Lev.finE (G.V (.grid 0 D.R.m)) (S.N.u (.grid 0 D.R.m)).1)⁻¹ *
        Formalism.IndefR.Lev.finE (G.V (.grid 0 D.R.m)) k.1 * Formalism.IndefR.Lev.finE (G.V (.grid 0 D.R.m)) (S.N.u (.grid 0 D.R.m)).1 := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
  change z ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid 0 D.R.m))) ↔
    (Formalism.IndefR.Lev.finE (G.V (.grid 0 D.R.m)) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1).val *ᵥ z ∈
      Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid 0 D.R.m)))
  rw [hm, hU z, hK, hU, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
  simp only [mul_assoc, mul_inv_cancel_left]

set_option maxHeartbeats 1000000 in

theorem vac_scalar (S : GridChoice W U) {μ₀ : T} (hL : L.Is μ₀) {t : T} {k : FinPt G (.grid 0 D.R.m)}
    (hk : finG (G.V (.grid 0 D.R.m)) k ∈ S.levRow t 0 (Nat.zero_le _)) (c : ℂ)
    (hc : W.om (.chi 0 D.R.m) (G.toPair (.chi 0 D.R.m) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1)
      (S.Z.vac (.chi 0 D.R.m)) = c • S.Z.vac (.chi 0 D.R.m)) :
    c = ∏ w : locPl G t, (locGrid G t w).edgeFactor .one (Pi.mulSingle (0, D.R.m) (kapAt S t w k)) (.ex 0 D.R.m) := by
  set x := (S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m) with hx
  have hm : 0 + 1 ≤ D.R.m := (GlobalTheory.FirstRowVertex.firstIx D).pos
  have hq := toPair_zero G x.1
  have key := GlobalTheory.RowVacScalar.vacScalar_eq_prod S hL t 0 hm (G.toPair (.chi 0 D.R.m) x.1 1)
    (by rw [hq]; exact one_mem _) (by rw [hq]; exact x.2)
    (by rw [hq]; exact fun y => one_lat _ _ y) (by rw [hq]; exact fun y => moved_latT S hL hk y) c hc
  rw [key]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [hq]
  exact splitScal_eq S hL hk w

private theorem iter_lam_eq_prod_chi {S κ K : Type} [CommRing S] [CommRing κ] [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {φ : S →+* κ} {ψ : S →+* K} {r t : ℕ} {μ : ℕ → Kˣ →* ℂˣ} (hμ : ∀ c, IsTame (μ c)) {χ : ℕ → κˣ →* ℂˣ} (n : ℕ)
    (hχ : ∀ c, c < n → GlobalTheory.FunObj.Comparison₂.Compat φ ψ (χ (c + 1)) (μ (c + 1)))
    (M : Matrix (Ix (Fin r) (Fin t) n) (Ix (Fin r) (Fin t) n) S) (u : Fin n → κˣ)
    (hu : ∀ c, (u c : κ) = (Ix.diagonalBlockOfMatrix (M.map φ) c).det)
    (g' : ((TypeDatum.principal K (Fin r)).iter (Fin t) μ hμ n).J)
    (hg' : (g' : GL (Ix (Fin r) (Fin t) n) K).val = M.map ψ) :
    ((TypeDatum.principal K (Fin r)).iter (Fin t) μ hμ n).lam g' = ∏ c : Fin n, χ (c.val + 1) (u c) := by
  induction n with
  | zero =>
    rw [Fin.prod_univ_zero]
    rfl
  | succ n ih =>
    set Q := (TypeDatum.principal K (Fin r)).iter (Fin t) μ hμ n with hQ
    have hmem : (reGL (ixSucc (Fin r) (Fin t) n)).symm (g' : GL (Ix (Fin r) (Fin t) (n + 1)) K) ∈ Q.stepJ (Fin t) := g'.2
    let h : Q.stepJ (Fin t) := ⟨_, hmem⟩
    have hlam : ((TypeDatum.principal K (Fin r)).iter (Fin t) μ hμ (n + 1)).lam g' =
        (Q.step (Fin t) (μ (n + 1)) (hμ _)).lam h := rfl
    have hval : (h : GL (Ix (Fin r) (Fin t) n ⊕ Fin t) K).val =
        (M.map ψ).submatrix (ixSucc (Fin r) (Fin t) n) (ixSucc (Fin r) (Fin t) n) := by
      show ((reGL (ixSucc (Fin r) (Fin t) n)).symm (g' : GL (Ix (Fin r) (Fin t) (n + 1)) K)).val = _
      rw [reGL_symm_val, hg']
    obtain ⟨-, ⟨g0, hg0, eg0⟩, -, -, D, -, eD⟩ := (Q.mem_stepJ (t := Fin t)).1 h.2
    have hlast : χ (n + 1) (u (Fin.last n)) = μ (n + 1) (Matrix.GeneralLinearGroup.det D) :=
      (hχ n (Nat.lt_succ_self n)).det
        (M.submatrix (ixSucc (Fin r) (Fin t) n ∘ Sum.inr) (ixSucc (Fin r) (Fin t) n ∘ Sum.inr))
        (by rw [hu]; rfl) (by rw [Matrix.GeneralLinearGroup.val_det_apply, eD, hval]; rfl)
    have hsmall := ih (fun c hc => hχ c (Nat.lt_succ_of_lt hc))
      (M.submatrix (ixSucc (Fin r) (Fin t) n ∘ Sum.inl) (ixSucc (Fin r) (Fin t) n ∘ Sum.inl))
      (fun c => u c.castSucc) (fun c => by rw [hu]; rfl) ⟨g0, hg0⟩ (by rw [eg0, hval]; rfl)
    rw [hlam, Q.step_lam_eq (μ (n + 1)) (hμ _) h ⟨g0, hg0⟩ eg0 D eD, hsmall, Fin.prod_univ_castSucc, ← hlast]
    rfl

section Red

open GlobalTheory.FunObj.Comparison₂

variable {S κ K : Type} [CommRing S] [CommRing κ] [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {φ : S →+* κ} {ψ : S →+* K} {r t j a : ℕ} {ea : Ix (Fin r) (Fin t) j ≃ Fin a}

theorem iter_lam_eq {μ : ℕ → Kˣ →* ℂˣ} (hμ : ∀ c, IsTame (μ c)) (h : IsRed φ ψ) (ha : IsIx ea) {χ : ℕ → κˣ →* ℂˣ}
    (hχ : ∀ c, c < j → Compat φ ψ (χ (c + 1)) (μ (c + 1))) (N : Matrix (Fin a) (Fin a) S) {g : GL (Fin a) κ}
    (hg : g ∈ blockTri (blkOf r t)) (hgN : g.val = N.map φ)
    (g' : ((TypeDatum.principal K (Fin r)).iter (Fin t) μ hμ j).J)
    (hg' : (g' : GL (Ix (Fin r) (Fin t) j) K).val = (N.submatrix ea ea).map ψ) :
    ((TypeDatum.principal K (Fin r)).iter (Fin t) μ hμ j).lam g' =
      ∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) g) := by
  have hu : ∀ c : Fin j, ((dBlk (blkOf r t) (c.val + 1) g : κˣ) : κ) = (Ix.diagonalBlockOfMatrix ((N.submatrix ea ea).map φ) c).det := by
    intro c
    rw [diagonalBlock_det_blockTriangular ha hg c, hgN]
    rfl
  rw [iter_lam_eq_prod_chi hμ j hχ (N.submatrix ea ea) (fun c => dBlk (blkOf r t) (c.val + 1) g) hu g' hg']
  exact (Finset.prod_range (fun c => χ (c + 1) (dBlk (blkOf r t) (c + 1) g))).symm

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem block_triangular_second_diagonal_block_det_eq (ha : IsIx ea) {g : GL (Fin a) κ} (hg : g ∈ blockTri (blk2 r)) :
    (dBlk (blk2 r) 1 g : κ) = ((g.val.submatrix ea ea).toBlocks₂₂).det := by
  have hmem : ∀ x : Fin j × Fin t, blk2 r (ea (.inr x)) = 1 := by
    rintro ⟨c, s⟩
    simp only [blk2, ha.2.2 c s]
    simp
  let f : Fin j × Fin t → {b : Fin a // blk2 r b = 1} := fun x => ⟨ea (.inr x), hmem x⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      exact Sum.inr_injective (ea.injective (congrArg Subtype.val hxy))
    · rintro ⟨b, hb⟩
      rcases hcase : ea.symm b with i | x
      · exfalso
        have h1 : (ea (.inl i)).val = i.val := ha.2.1 i
        rw [← hcase, Equiv.apply_symm_apply] at h1
        simp [blk2, h1, i.2] at hb
      · refine ⟨x, Subtype.ext ?_⟩
        simp only [f, ← hcase, Equiv.apply_symm_apply]
  rw [diag_block_det_val 1 hg]
  refine (Matrix.det_submatrix_equiv_self (Equiv.ofBijective f hf) _).symm.trans ?_
  congr 1

theorem parahoric_lam_eq {δ : Kˣ →* ℂˣ} (hδ : IsTame δ) (h : IsRed φ ψ) (ha : IsIx ea) {χ : κˣ →* ℂˣ}
    (hχ : Compat φ ψ χ δ) (N : Matrix (Fin a) (Fin a) S) {g : GL (Fin a) κ}
    (hg : g ∈ blockTri (blk2 r)) (hgN : g.val = N.map φ)
    (g' : (parahoric (Fin r) (Fin j × Fin t) δ hδ).J)
    (hg' : (g' : GL (Ix (Fin r) (Fin t) j) K).val = (N.submatrix ea ea).map ψ) :
    (parahoric (Fin r) (Fin j × Fin t) δ hδ).lam g' = χ (dBlk (blk2 r) 1 g) := by
  obtain ⟨-, -, -, -, D, -, eD⟩ := ((TypeDatum.full K (Fin r)).mem_stepJ (t := Fin j × Fin t)).1 g'.2
  rw [parahoric_lam g' D eD]
  exact (hχ.det ((N.submatrix ea ea).toBlocks₂₂)
    (by rw [block_triangular_second_diagonal_block_det_eq ha hg, hgN]; rfl)
    (by rw [Matrix.GeneralLinearGroup.val_det_apply, eD, hg']; rfl)).symm

end Red

open GlobalTheory.FunObj.Comparison₂ in
open Classical in

theorem stepType_lam {μ₀ : T} (hL : L.Is μ₀) (t : T) {j n : ℕ} (hj : j ≤ D.R.m) (w : Pl D.host.E)
    {ea : Ix (Fin D.R.r) (Fin D.R.t) j ≃ Fin n} (ha : IsIx ea) (N : Matrix (Fin n) (Fin n) (OA D)) (g : GL (Fin n) (kP w))
    (hr : g.val = N.map (resS D.host.F w)) (κ : GL (Ix (Fin D.R.r) (Fin D.R.t) j) (Kw w))
    (hv : κ.val = (N.submatrix ea ea).map (cptO w))
    (hP : w ∈ L.Pg → g ∈ blockTri (blkOf D.R.r D.R.t)) (hQ : w ∈ L.Q t → g ∈ blockTri (blk2 D.R.r))
    (hk : κ ∈ stepGroup L t w j) :
    ∃ hk' : κ ∈ (stepType L t w j).J, (stepType L t w j).lam ⟨κ, hk'⟩ =
      (if w ∈ L.Pg then ∏ c ∈ Finset.range j, L.chi (c + 1) w (dBlk (blkOf D.R.r D.R.t) (c + 1) g) else 1) *
        (if w ∈ L.Q t then (L.xiR t w)⁻¹ (dBlk (blk2 D.R.r) 1 g) else 1) := by
  classical
  have hred := isRed (D := D) w
  by_cases hP' : w ∈ L.Pg
  · have hQ' : w ∉ L.Q t := by
      intro hwQ
      obtain ⟨kk, hkk⟩ := (hL.Pg w).1 hP'
      obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hL.Q_pl t w hwQ
      have hkk' : w.under (𝓞 D.host.K) = L.C.P.pb kk := hkk
      have h1 := L.C.P.pb_over kk
      rw [← hkk'] at h1
      have hmem : ((D.host.g kk : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
        have h3 := Ideal.mem_comap.mp h1
        simpa using h3
      have hfin : Finite (Formalism.L2.DIV.kP w) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq.ne_zero)
      haveI := Fintype.ofFinite (Formalism.L2.DIV.kP w)
      have hq0 : ((q : ℕ) : Formalism.L2.DIV.kP w) = 0 := by
        rw [← hcard, Nat.card_eq_fintype_card]
        exact Nat.cast_card_eq_zero _
      have hg0 : ((D.host.g kk : ℕ) : Formalism.L2.DIV.kP w) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk w.asIdeal)]
        exact Ideal.Quotient.eq_zero_iff_mem.2 hmem
      have hcop : Nat.Coprime q (D.host.g kk) := (Nat.coprime_primes hq (D.host.g_prime kk)).2 (hne kk)
      have key := Nat.gcd_eq_gcd_ab q (D.host.g kk)
      rw [hcop.gcd_eq_one] at key
      have h2 := congrArg (Int.cast : ℤ → Formalism.L2.DIV.kP w) key
      push_cast at h2
      rw [hq0, hg0] at h2
      simp only [zero_mul, add_zero] at h2
      haveI : Subsingleton (Formalism.L2.DIV.kP w) := subsingleton_of_zero_eq_one h2.symm
      have hc1 : Nat.card (Formalism.L2.DIV.kP w) = 1 := Nat.card_of_subsingleton (0 : Formalism.L2.DIV.kP w)
      rw [hcard] at hc1
      exact hq.one_lt.ne' hc1
    have hT : stepType L t w j = (TypeDatum.principal (Kw w) (Fin D.R.r)).iter (Fin D.R.t)
        (fun c => ((muBase L c).loc w)⁻¹) (isTame_muBase w) j := by
      simp only [stepType, if_pos hP']
    have hG : stepGroup L t w j = ((TypeDatum.principal (Kw w) (Fin D.R.r)).iter (Fin D.R.t)
        (fun c => ((muBase L c).loc w)⁻¹) (isTame_muBase w) j).J := by
      simp only [stepGroup, if_pos hP']
    rw [hG] at hk
    rw [hT]
    refine ⟨hk, ?_⟩
    rw [if_pos hP', if_neg hQ', mul_one]
    exact iter_lam_eq (isTame_muBase w) hred ha (χ := fun c => L.chi c w)
      (fun c hc => compat_chi w hL hP' (by omega)) N (hP hP') hr ⟨κ, hk⟩ hv
  · by_cases hQ' : w ∈ L.Q t
    · have h0 := isTame_loc (hL.xi_tame t w)
      have htame : IsTame ((L.xiH t).loc w)⁻¹ := by
        intro x hx
        simp [h0 x hx]
      have hp : w ∈ L.Q t ∧ IsTame ((L.xiH t).loc w)⁻¹ := ⟨hQ', htame⟩
      have hT : stepType L t w j = parahoric (Fin D.R.r) (Fin j × Fin D.R.t) _ htame := by
        simp only [stepType, if_neg hP', dif_pos hp]
      have hG : stepGroup L t w j =
          (parahoric (k := Kw w) (Fin D.R.r) (Fin j × Fin D.R.t) 1 fun _ _ => rfl).J := by
        simp only [stepGroup, if_neg hP', if_pos hQ']
      rw [hG] at hk
      have hk2 : κ ∈ (parahoric (Fin D.R.r) (Fin j × Fin D.R.t) _ htame).J :=
        mem_parahoric.2 (mem_parahoric.1 hk)
      have hc0 := compat_of_isRes (hL.xi_tame t w) (hL.xiR t w hQ')
      have hχ : Compat (resS D.host.F w) (cptO w) (L.xiR t w)⁻¹ ((L.xiH t).loc w)⁻¹ := by
        intro s u k hu hk
        simp [hc0 s u k hu hk]
      rw [hT]
      refine ⟨hk2, ?_⟩
      rw [if_neg hP', if_pos hQ', one_mul]
      exact parahoric_lam_eq htame hred ha hχ N (hQ hQ') hr ⟨κ, hk2⟩ hv
    · have hn : ¬ (w ∈ L.Q t ∧ IsTame ((L.xiH t).loc w)⁻¹) := fun h => hQ' h.1
      have hT : stepType L t w j = TypeDatum.full _ _ := by
        simp only [stepType, if_neg hP', dif_neg hn]
      have hG : stepGroup L t w j = KO (Kw w) _ := by
        simp only [stepGroup, if_neg hP', if_neg hQ']
      rw [hG] at hk
      rw [hT]
      refine ⟨hk, ?_⟩
      rw [if_neg hP', if_neg hQ', mul_one]
      rfl

set_option maxHeartbeats 1000000 in
open GlobalTheory.FunObj.Comparison₂ in
open Classical in

theorem endLamAt_eq {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T) {j n : ℕ} (hj : j ≤ D.R.m) (w : Pl D.host.E)
    (h : (locGrid G t w).rank (0, j) = n) (β x : GL (Fin n) (Lev.EAf D)) (hx : x ∈ St β)
    (hP : w ∈ L.Pg → redFn β w x ∈ blockTri (blkOf D.R.r D.R.t)) (hQ : w ∈ L.Q t → redFn β w x ∈ blockTri (blk2 D.R.r))
    (hk : (reGL (ixFin G t w j)).symm (inBasis h β w x) ∈ stepGroup L t w j) :
    endLamAt G t w j (inBasis h β w x) =
      (((if w ∈ L.Pg then ∏ c ∈ Finset.range j, L.chi (c + 1) w (dBlk (blkOf D.R.r D.R.t) (c + 1) (redFn β w x)) else 1) *
        (if w ∈ L.Q t then (L.xiR t w)⁻¹ (dBlk (blk2 D.R.r) 1 (redFn β w x)) else 1) : ℂˣ) : ℂ)⁻¹ := by
  classical
  obtain ⟨y, rfl⟩ := hx
  let ea : Ix (Fin D.R.r) (Fin D.R.t) j ≃ Fin n := (ixFin G t w j).trans (finCongr h)
  have hn : n = D.R.r + j * D.R.t := by
    have := Fintype.card_congr ea
    simp [GlobalTheory.StepData.Ix] at this
    omega
  have ha : IsIx ea := by
    refine ⟨hn, fun i => ?_, fun c s => ?_⟩
    · simp [ea, (ixFin_val G t w j).1 i]
    · simp [ea, (ixFin_val G t w j).2 c s]
  have hr : (redFn β w (frGL β y)).val = (y.val).map (resS D.host.F w) := by
    rw [redFn_frGL]
    rfl
  have hv : ((reGL (ixFin G t w j)).symm (inBasis h β w (frGL β y))).val =
      ((y.val).submatrix ea ea).map (cptO w) := by
    have hc : MulAut.conj β⁻¹ (frGL β y) = intGL D.host.F D.host.E n y := by
      simp [frGL, MulAut.conj_apply, mul_assoc]
    rw [show inBasis h β w (frGL β y) =
        (reGL (finCongr h.symm)) (GlobalTheory.StdFrames.loc w (MulAut.conj β⁻¹ (frGL β y))) from rfl, hc]
    ext i l
    simp [GlobalTheory.TopLevelInv.val_loc, intGL, cptO_apply, ea, GlobalTheory.StepData.reGL, Formalism.UG.bc]
  obtain ⟨hk', hlam⟩ := stepType_lam hL t hj w ha y.val (redFn β w (frGL β y)) hr _ hv hP hQ hk
  unfold endLamAt
  rw [dif_pos hk', hlam, Units.val_inv_eq_inv_val]

set_option maxHeartbeats 1000000 in

theorem levFn_mul_endLamAt {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T)
    (h : ∀ w, (locGrid G t w).rank (0, D.R.m) = D.sp.X'.rank) (x : GL (Fin D.sp.X'.rank) (Lev.EAf D))
    (hx : x ∈ lev D.sp.cm D.sp.X'.gram L.βX (Lev.flag1L (L.datXt t)))
    (hk : ∀ w : locPl G t, (reGL (ixFin G t w D.R.m)).symm (inBasis (h w) L.βX w x) ∈ stepGroup L t w D.R.m) :
    ((levFn L.βX (Lev.flag1L (L.datXt t)) x : ℂˣ) : ℂ) *
      ∏ w : locPl G t, endLamAt G t w D.R.m (inBasis (h w) L.βX w x) = 1 := by
  classical
  have hPg : L.Pg ⊆ locPl G t := fun w hw => Finset.mem_union_left _ (levelChainTypePlaces_subset_chosenPlaces G hL t hw)
  have hQ : L.Q t ⊆ locPl G t := fun w hw => Finset.mem_union_right _ hw
  have hxl : x ∈ Formalism.L2.DIV.parLev D.sp.cm D.sp.X'.gram L.βX (Lev.flag1L (L.datXt t)) := hx.1
  have hSt : x ∈ Formalism.L2.DIV.St L.βX := Formalism.L2.DIV.parLev_St hxl
  set a : Pl D.host.E → ℂˣ := fun w => if w ∈ L.Pg then ∏ c ∈ Finset.range D.R.m, L.chi (c + 1) w
      (dBlk (blkOf D.R.r D.R.t) (c + 1) (redFn L.βX w x)) else 1 with ha
  set b : Pl D.host.E → ℂˣ := fun w => if w ∈ L.Q t then (L.xiR t w)⁻¹ (dBlk (blk2 D.R.r) 1 (redFn L.βX w x))
      else 1 with hb
  have hE : ∀ w : locPl G t, endLamAt G t w D.R.m (inBasis (h w) L.βX w x) = (((a w.1 * b w.1)⁻¹ : ℂˣ) : ℂ) := by
    intro w
    rw [endLamAt_eq hL G t le_rfl w.1 (h w) L.βX x hSt (fun hw => Formalism.L2.DIV.parLev_g hxl hw)
      (fun hw => Formalism.L2.DIV.parLev_q hxl hw) (hk w), Units.val_inv_eq_inv_val]
  have hlev : Formalism.L2.DIV.levFn L.βX (Lev.flag1L (L.datXt t)) x =
      (∏ PP ∈ L.Pg, ∏ c ∈ Finset.range D.R.m, L.chi (c + 1) PP (dBlk (blkOf D.R.r D.R.t) (c + 1) (redFn L.βX PP x))) *
        ∏ PP ∈ L.Q t, (L.xiR t PP)⁻¹ (dBlk (blk2 D.R.r) 1 (redFn L.βX PP x)) := by
    rw [Formalism.L2.DIV.levFn]
    have h1 : Formalism.L2.DIV.ext1 (Lev.flag1L (L.datXt t)).P.H (Lev.flag1L (L.datXt t)).P.chi
        (Formalism.L2.DIV.rTup L.βX (Lev.flag1L (L.datXt t)) x) = 1 := by
      unfold Formalism.L2.DIV.ext1
      split <;> rfl
    rw [h1, one_mul]
    simp [Lev.flag1L, Lev.withP, Formalism.IndefR.Links.LevCh.datXt, Lev.datY]
  have hU : Formalism.L2.DIV.levFn L.βX (Lev.flag1L (L.datXt t)) x * ∏ w ∈ locPl G t, (a w * b w)⁻¹ = 1 := by
    rw [Finset.prod_inv_distrib, Finset.prod_mul_distrib, mul_inv_eq_one, hlev, ha, hb,
      Finset.prod_ite_mem, Finset.prod_ite_mem, Finset.inter_eq_right.mpr hPg, Finset.inter_eq_right.mpr hQ]
  rw [Fintype.prod_congr _ _ hE, Finset.prod_coe_sort (locPl G t) (fun w => (((a w * b w)⁻¹ : ℂˣ) : ℂ)),
    ← Units.coe_prod, ← Units.val_mul, hU, Units.val_one]

private theorem inBasis_eq_of_heq_of_cast {X Y : LSp D} (hXY : X = Y) (β : GL (Fin X.sp.rank) (Lev.EAf D))
    (β' : GL (Fin Y.sp.rank) (Lev.EAf D)) (hβ : HEq β β') (y : GA D X.sp) (w : Pl D.host.E) {n : ℕ}
    (h : n = X.sp.rank) (h' : n = Y.sp.rank) :
    inBasis h β w (Lev.finE X.sp y) =
      inBasis h' β' w (Lev.finE Y.sp (cast (congrArg (fun Z : LSp D => GA D Z.sp) hXY) y)) := by
  subst hXY
  obtain rfl := eq_of_heq hβ
  rfl

private theorem reGL_symm_mem_of_mem_givenLevel (G : GridData L sc) (t : T) (w : Pl D.host.E) {n : ℕ} (hn : 1 ≤ n)
    (κ : GL (Fin ((locGrid G t w).rank (0, n))) (Kw w)) (hκ : κ ∈ givenLevel G t w (0, n)) :
    (reGL (ixFin G t w n)).symm κ ∈ stepGroup L t w n := by
  cases n with
  | zero => omega
  | succ j =>
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hκ
    simpa using hy

set_option maxHeartbeats 1000000 in

theorem chi_mul_endLam {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ₀ : T} (hL : L.Is μ₀) {t : T}
    {k : FinPt G (.grid 0 D.R.m)} (hk : finG (G.V (.grid 0 D.R.m)) k ∈ S.levRow t 0 (Nat.zero_le _))
    (hk' : toXf k ∈ (levEnv D.sp.X' L.βX (L.datXt t)).J) :
    (((levEnv D.sp.X' L.βX (L.datXt t)).χ ⟨toXf k, hk'⟩ : ℂˣ) : ℂ) * ∏ w : locPl G t, endLam G t w.1 (kapAt S t w.1 k) = 1 := by
  have hm1 : 1 ≤ D.R.m := (GlobalTheory.FirstRowVertex.firstIx D).pos
  have h : ∀ w, (locGrid G t w).rank (0, D.R.m) = D.sp.X'.rank := fun w =>
    (rank_vertex G t w (X := (0, D.R.m)) ⟨Nat.zero_le _, le_rfl⟩).trans
      (congrArg (fun X : LSp D => X.sp.rank) (colY_m L))
  set x0 := Lev.finE D.sp.X' (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m L)) k.1) with hx0
  have hχ : (((levEnv D.sp.X' L.βX (L.datXt t)).χ ⟨toXf k, hk'⟩ : ℂˣ) : ℂ) =
      ((levFn L.βX (Lev.flag1L (L.datXt t)) x0 : ℂˣ) : ℂ) := by
    rw [hx0, Lev.finE_eq]
    rfl
  have hx : x0 ∈ lev D.sp.cm D.sp.X'.gram L.βX (Lev.flag1L (L.datXt t)) := by
    rw [hx0, Lev.finE_eq]
    exact hk'
  have hkap : ∀ w : locPl G t, kapAt S t w.1 k = inBasis (h w) L.βX w x0 := fun w =>
    inBasis_eq_of_heq_of_cast (colY_m L) (colFrame L D.R.m) L.βX (colFrame_m L) k.1 w _ _
  have hk2 : ∀ w : locPl G t, (reGL (ixFin G t w D.R.m)).symm (inBasis (h w) L.βX w x0) ∈ stepGroup L t w D.R.m :=
    fun w => by
      rw [← hkap w]
      exact reGL_symm_mem_of_mem_givenLevel G t w.1 hm1 _ (kapAt_mem S hk w)
  have key := levFn_mul_endLamAt hL G t h x0 hx hk2
  rw [hχ]
  simpa only [endLam, hkap] using key

theorem scalar_of_is {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ₀ : T} (hL : L.Is μ₀) (t : T)
    (k : FinPt G (.grid 0 D.R.m)) (hk : finG (G.V (.grid 0 D.R.m)) k ∈ S.levRow t 0 (Nat.zero_le _))
    (hk' : toXf k ∈ (levEnv D.sp.X' L.βX (L.datXt t)).J) (c : ℂ)
    (hc : W.om (.chi 0 D.R.m) (G.toPair (.chi 0 D.R.m) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1)
      (S.Z.vac (.chi 0 D.R.m)) = c • S.Z.vac (.chi 0 D.R.m)) :
    (((levEnv D.sp.X' L.βX (L.datXt t)).χ ⟨toXf k, hk'⟩ : ℂˣ) : ℂ) * c * ∏ w : locPl G t, endLam G t w.1 (kapAt S t w.1 k) =
      ∏ w : locPl G t, (locGrid G t w).edgeFactor .one (Pi.mulSingle (0, D.R.m) (kapAt S t w k)) (.ex 0 D.R.m) := by
  have h1 := vac_scalar S hL hk c hc
  have h2 := chi_mul_endLam S hL hk hk'
  linear_combination c * h2 + h1

theorem scalar : GlobalTheory.FunPr.Hypotheses₂ → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J) (c : ℂ),
      ch.W.om (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1) (ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) = c • ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) →
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) * c *
          ∏ w : locPl ch.G t, GlobalTheory.FirstRowEndLaw.endLam ch.G t w.1 (GlobalTheory.FirstRowTermLaw.kapAt ch.S.toGridChoice t w.1 k) =
        ∏ w : locPl ch.G t, (locGrid ch.G t w).edgeFactor .one
          (Pi.mulSingle (0, D.R.m) (GlobalTheory.FirstRowTermLaw.kapAt ch.S.toGridChoice t w k)) (.ex 0 D.R.m) := by
  intro _ _
  refine ⟨0, fun ε CF _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ t k hk hk' c hc
  exact scalar_of_is ch.S.toGridChoice hS.core.lev t k hk hk' c hc

end GlobalTheory.FirstRowScalar
