import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharacterApplyEqLevelFunctionSwap
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.TwistedCharacterValue
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameKeepsMatricesSplitPlaceReductionLocalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceResidueMapEqReductionStatement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.LevChiRead

open Formalism.L2.DIV

variable {D : D7}

theorem resRep_spec {L : Type} [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L)
    (x : s.v.adicCompletion (maximalRealSubfield L)) (u : 𝓞 L) (hu : u ∉ s.w.asIdeal)
    (hux : Valued.v (s.i (u : L) - x) < 1) :
    NX.resRep s s.w x ∉ s.w.asIdeal ∧
      Ideal.Quotient.mk s.w.asIdeal (NX.resRep s s.w x) = Ideal.Quotient.mk s.w.asIdeal u := by
  have hex : ∃ u : 𝓞 L, u ∉ s.w.asIdeal ∧ Valued.v (s.i (u : L) - x) < 1 := ⟨u, hu, hux⟩
  unfold NX.resRep
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  refine ⟨h1, Ideal.Quotient.eq.2 ?_⟩
  show _ ∈ s.ideal
  rw [s.split_mem_ideal]
  have e : s.i (((hex.choose - u : 𝓞 L)) : L) = (s.i (hex.choose : L) - x) - (s.i (u : L) - x) := by
    rw [show (((hex.choose - u : 𝓞 L)) : L) = (hex.choose : L) - (u : L) by push_cast; ring, map_sub]
    ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h2 hux)

open Classical in

theorem psiU_prod (i : D.ntw.Tw) (b : Bool)
    (hUup : D.nexp.U = NX.Uup (fun kv : (Σ kk : Fin 2, D.nd.PlG kk) => D.host.g kv.1) D.R.r)
    (hgen : NX.IsStdGeneric (fun kv : (Σ kk : Fin 2, D.nd.PlG kk) => D.host.g kv.1) D.R.r (D.nexp.psiU i b))
    (u : G0g D.nd) (hu : u ∈ D.nexp.U) :
    ∏ kv, NX.psiUTot D i b (Pi.mulSingle kv (u kv)) =
      ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) := by
  obtain ⟨θ, -, hθ⟩ := hgen
  have hsingle : ∀ kv, NX.psiUTot D i b (Pi.mulSingle kv (u kv)) =
      ((θ kv (Multiplicative.ofAdd (NX.supSum D.R.r ((u kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
        Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))))) : (FractionRing (D.ntw.O i))ˣ) :
          FractionRing (D.ntw.O i)) := by
    intro kv
    have hu' : u ∈ NX.Uup (fun kv : (Σ kk : Fin 2, D.nd.PlG kk) => D.host.g kv.1) D.R.r := hUup ▸ hu
    have hmem : (Pi.mulSingle kv (u kv) : G0g D.nd) ∈ D.nexp.U := by
      rw [hUup]
      intro kv'
      by_cases h : kv' = kv
      · subst h; rw [Pi.mulSingle_eq_same]; exact hu' kv'
      · rw [Pi.mulSingle_eq_of_ne h]; exact ⟨Matrix.blockTriangular_one, fun a => by simp⟩
    unfold NX.psiUTot
    rw [dif_pos hmem, hθ ⟨_, hmem⟩, NX.stdVal, Finset.prod_eq_single kv]
    · simp only [Pi.mulSingle_eq_same]
    · intro kv' _ hne
      simp only [Pi.mulSingle_eq_of_ne hne, Units.val_one, NX.supSum_one, ofAdd_zero, map_one]
    · intro h; exact absurd (Finset.mem_univ kv) h
  rw [Finset.prod_congr rfl fun kv _ => hsingle kv, hθ ⟨u, hu⟩, NX.stdVal, Units.coe_prod]

theorem secondBlock_blockOf_eq_blockTwo {κ : Type} [CommRing κ] {n r : ℕ} (g : GL (Fin n) κ) (hg : g ∈ blockTri (blkOf r (n - r))) :
    dBlk (blkOf r (n - r)) 1 g = dBlk (blk2 r) 1 g := by
  have hg2 := blockTri_blkOf_le (κ := κ) r (n - r) hg
  unfold dBlk
  rw [extendOne_of_mem _ hg, extendOne_of_mem _ hg2]
  apply Units.ext
  have hiff : ∀ a : Fin n, blk2 r a = 1 ↔ blkOf r (n - r) a = 1 := by
    intro a
    have := a.2
    unfold blk2 blkOf
    split_ifs with h
    · simp
    · simp only [true_iff]; rw [Nat.div_eq_of_lt (by omega)]
  exact (Matrix.det_submatrix_equiv_self (Equiv.subtypeEquivRight hiff)
    (((g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).submatrix
      (Subtype.val : {a : Fin n // blkOf r (n - r) a = 1} → Fin n) Subtype.val)).symm

theorem detRed {V : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {P : principalLevelFrame.RowPsi V n}
    (hP : IdFrame hF P) (hn : V.rank = n) (r : ℕ) {κ : GAf D.host.E n} (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n)
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (hb : redFn (1 : GL (Fin V.rank) (Lev.EAf D)) s.w (Lev.finE V (P.ψ κ)) ∈ blockTri (blk2 r)) :
    NX.detT r (NX.locM s κ) ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) ∧
      ∃ u : 𝓞 D.host.E, Valued.v (s.i (u : D.host.E) - NX.detT r (NX.locM s κ)) < 1 ∧
        ((dBlk (blk2 r) 1 (redFn (1 : GL (Fin V.rank) (Lev.EAf D)) s.w (Lev.finE V (P.ψ κ))) : (kP s.w)ˣ) : kP s.w) =
          Ideal.Quotient.mk s.w.asIdeal u := by
  set K := s.v.adicCompletion (maximalRealSubfield D.host.E)
  set O := s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)
  set R := redFn (1 : GL (Fin V.rank) (Lev.EAf D)) s.w (Lev.finE V (P.ψ κ)) with hR
  have hred := (GlobalTheory.T.frameKeepsMatrices_splitPlace_reduction_local D V n hF P hP hn κ).2 s hκ
  let m : Ideal O :=
    { carrier := {x | Valued.v (x : K) < 1}
      add_mem' := fun {a b} ha hb => by
        show Valued.v ((a : K) + b) < 1
        exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hb)
      zero_mem' := by show Valued.v ((0 : K)) < 1; simp
      smul_mem' := fun c x hx => by
        show Valued.v ((c : K) * x) < 1
        rw [Valuation.map_mul]
        calc Valued.v (c : K) * Valued.v (x : K) ≤ 1 * Valued.v (x : K) := by gcongr; exact c.2
          _ < 1 := by rwa [one_mul] }
  have hm : ∀ x : O, x ∈ m ↔ Valued.v (x : K) < 1 := fun x => Iff.rfl
  have hsurj := fun a c => Ideal.Quotient.mk_surjective ((R : Matrix (Fin V.rank) (Fin V.rank) (kP s.w)) a c)
  choose u hu using hsurj
  let A : Matrix {a : Fin V.rank // blk2 r a = 1} {a : Fin V.rank // blk2 r a = 1} O :=
    fun a c => ⟨NX.locM s κ (Fin.cast hn a.1) (Fin.cast hn c.1), (hred a.1 c.1).1⟩
  let Bm : Matrix {a : Fin V.rank // blk2 r a = 1} {a : Fin V.rank // blk2 r a = 1} O :=
    fun a c => ⟨s.i (u a.1 c.1 : D.host.E), s.split_le_one _⟩
  have hAB : A.map (Ideal.Quotient.mk m) = Bm.map (Ideal.Quotient.mk m) := by
    ext a c
    simp only [Matrix.map_apply]
    rw [Ideal.Quotient.eq, hm]
    have hv := ((hred a.1 c.1).2 (u a.1 c.1)).2 (hu a.1 c.1).symm
    show Valued.v (NX.locM s κ (Fin.cast hn a.1) (Fin.cast hn c.1) - s.i (u a.1 c.1 : D.host.E)) < 1
    rwa [← Valuation.map_neg, neg_sub]
  have hdet : Ideal.Quotient.mk m A.det = Ideal.Quotient.mk m Bm.det := by
    rw [RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hAB]
  let e : {a : Fin V.rank // blk2 r a = 1} ≃ {i : Fin n // r ≤ (i : ℕ)} :=
    { toFun := fun a => ⟨Fin.cast hn a.1, by
        have h := a.2
        unfold blk2 at h
        have h' : ¬ (a.1 : ℕ) < r := fun h' => by simp [h'] at h
        simp only [Fin.val_cast]; omega⟩
      invFun := fun i => ⟨Fin.cast hn.symm i.1, by
        have h := i.2
        unfold blk2
        rw [if_neg (by simp only [Fin.val_cast]; omega)]⟩
      left_inv := fun a => rfl
      right_inv := fun i => rfl }
  have hdetT : NX.detT r (NX.locM s κ) = ((A.det : O) : K) := by
    rw [show ((A.det : O) : K) = O.subtype A.det from rfl, RingHom.map_det]
    unfold NX.detT
    rw [← Matrix.det_submatrix_equiv_self e]
    rfl
  have hdB : ((dBlk (blk2 r) 1 R : (kP s.w)ˣ) : kP s.w) =
      Ideal.Quotient.mk s.w.asIdeal (Matrix.det (fun a c : {a : Fin V.rank // blk2 r a = 1} => u a.1 c.1)) := by
    unfold dBlk
    rw [extendOne_of_mem _ hb]
    show (((R : Matrix (Fin V.rank) (Fin V.rank) (kP s.w)).submatrix Subtype.val Subtype.val).det) = _
    rw [show ((R : Matrix (Fin V.rank) (Fin V.rank) (kP s.w)).submatrix Subtype.val Subtype.val) =
        (Matrix.of fun a c : {a : Fin V.rank // blk2 r a = 1} => u a.1 c.1).map (Ideal.Quotient.mk s.w.asIdeal) from by
      ext a c; exact (hu a.1 c.1).symm]
    exact ((Ideal.Quotient.mk s.w.asIdeal).map_det _).symm
  have hBU : ((Bm.det : O) : K) =
      s.i ((Matrix.det (fun a c : {a : Fin V.rank // blk2 r a = 1} => u a.1 c.1) : 𝓞 D.host.E) : D.host.E) := by
    rw [show ((Bm.det : O) : K) = O.subtype Bm.det from rfl, RingHom.map_det,
      show s.i ((Matrix.det (fun a c : {a : Fin V.rank // blk2 r a = 1} => u a.1 c.1) : 𝓞 D.host.E) : D.host.E) =
        ((s.i : D.host.E →+* K).comp (algebraMap (𝓞 D.host.E) D.host.E))
          (Matrix.det (fun a c : {a : Fin V.rank // blk2 r a = 1} => u a.1 c.1)) from rfl]
    refine Eq.trans ?_ ((((s.i : D.host.E →+* K).comp (algebraMap (𝓞 D.host.E) D.host.E)).map_det
      (Matrix.of fun a c : {a : Fin V.rank // blk2 r a = 1} => u a.1 c.1)).symm)
    rfl
  refine ⟨by rw [hdetT]; exact (A.det).2, _, ?_, hdB⟩
  rw [hdetT, ← hBU]
  have h1 := (hm _).1 (Ideal.Quotient.eq.1 hdet.symm)
  simpa using h1

theorem qPlace {V : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {P : principalLevelFrame.RowPsi V n}
    (hP : IdFrame hF P) (hn : V.rank = n) {κ : GAf D.host.E n} (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n)
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (w : Pl D.host.E) (hw : s.w = w) (r r' : ℕ) (hrr : r' = r)
    (hb : redFn (1 : GL (Fin V.rank) (Lev.EAf D)) w (Lev.finE V (P.ψ κ)) ∈ blockTri (blk2 r')) :
    NX.resRep s w (NX.detT r (NX.locM s κ)) ∉ w.asIdeal ∧
      ((dBlk (blk2 r') 1 (redFn (1 : GL (Fin V.rank) (Lev.EAf D)) w (Lev.finE V (P.ψ κ))) : (kP w)ˣ) : kP w) =
        Ideal.Quotient.mk w.asIdeal (NX.resRep s w (NX.detT r (NX.locM s κ))) := by
  subst hw hrr
  obtain ⟨-, u, hu, hd⟩ := detRed hP hn r' hκ s hb
  haveI : Nontrivial (kP s.w) := Ideal.Quotient.nontrivial_iff.2 s.w.isPrime.ne_top
  have hun : u ∉ s.w.asIdeal := fun hm =>
    (dBlk (blk2 r') 1 (redFn (1 : GL (Fin V.rank) (Lev.EAf D)) s.w (Lev.finE V (P.ψ κ)))).ne_zero
      (by rw [hd]; exact Ideal.Quotient.eq_zero_iff_mem.2 hm)
  obtain ⟨h1, h2⟩ := resRep_spec s _ u hun hu
  exact ⟨h1, hd.trans h2.symm⟩

theorem typePlace {V : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {P : principalLevelFrame.RowPsi V n}
    (hP : IdFrame hF P) (hn : V.rank = n) {κ : GAf D.host.E n} (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n)
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (w : Pl D.host.E) (hw : s.w = w) (q : ℕ) (hq : q.Prime)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod q) (iso : ZMod q ≃+* kP w)
    (r r' : ℕ) (hrr : r' = r) (hrn : r ≤ n) (hrV : r' ≤ V.rank)
    (hb : redFn (1 : GL (Fin V.rank) (Lev.EAf D)) w (Lev.finE V (P.ψ κ)) ∈ blockTri (blk2 r')) :
    (∀ a c : Fin r, iso (NX.redMat s.v red (NX.topR hrn (NX.locM s κ)) a c) =
      ((upperLeftBlock hrV (redFn (1 : GL (Fin V.rank) (Lev.EAf D)) w (Lev.finE V (P.ψ κ))) : GL (Fin r') (kP w)) :
        Matrix (Fin r') (Fin r') (kP w)) (Fin.cast hrr.symm a) (Fin.cast hrr.symm c)) ∧
    ∃ x : (ZMod q)ˣ, red (NX.intLift s.v (NX.detT r (NX.locM s κ))) = x ∧
      iso x = ((dBlk (blk2 r') 1 (redFn (1 : GL (Fin V.rank) (Lev.EAf D)) w (Lev.finE V (P.ψ κ))) : (kP w)ˣ) : kP w) := by
  subst hw hrr
  have hred := (GlobalTheory.T.frameKeepsMatrices_splitPlace_reduction_local D V n hF P hP hn κ).2 s hκ
  refine ⟨fun a c => ?_, ?_⟩
  · rw [upper_block_val_submatrix hrV hb]
    obtain ⟨hint, hiff⟩ := hred (Fin.castLE hrV a) (Fin.castLE hrV c)
    obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective
      (((redFn (1 : GL (Fin V.rank) (Lev.EAf D)) s.w (Lev.finE V (P.ψ κ)) : GL (Fin V.rank) (kP s.w)) :
        Matrix (Fin V.rank) (Fin V.rank) (kP s.w)) (Fin.castLE hrV a) (Fin.castLE hrV c))
    have hv := (hiff u).2 hu.symm
    show iso (red (NX.intLift s.v (NX.locM s κ (Fin.cast hn (Fin.castLE hrV a)) (Fin.cast hn (Fin.castLE hrV c))))) = _
    rw [Formalism.IndefR.NX.intLift_of_mem _ _ hint]
    exact ((GlobalTheory.T.split_place_residue_map_eq_reduction D.host.E s q hq red iso ⟨_, hint⟩ u).1 hv).trans hu
  · obtain ⟨hint, u, hu, hd⟩ := detRed hP hn r' hκ s hb
    have h1 : iso (red (NX.intLift s.v (NX.detT r' (NX.locM s κ)))) =
        ((dBlk (blk2 r') 1 (redFn (1 : GL (Fin V.rank) (Lev.EAf D)) s.w (Lev.finE V (P.ψ κ))) : (kP s.w)ˣ) : kP s.w) := by
      rw [Formalism.IndefR.NX.intLift_of_mem _ _ hint, hd]
      exact (GlobalTheory.T.split_place_residue_map_eq_reduction D.host.E s q hq red iso ⟨_, hint⟩ u).1 hu
    refine ⟨Units.map iso.symm.toRingHom.toMonoidHom
      (dBlk (blk2 r') 1 (redFn (1 : GL (Fin V.rank) (Lev.EAf D)) s.w (Lev.finE V (P.ψ κ)))), ?_, ?_⟩
    · rw [Units.coe_map, ← h1]
      exact (iso.symm_apply_apply _).symm
    · rw [Units.coe_map]
      exact iso.apply_symm_apply _

set_option maxHeartbeats 8000000 in
open Classical in

theorem levChi_read : ∀ (D : D7) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀] (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀) (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (M : NX.MtVReal D i (j.1 + 1) b k Q ψ e W₀ ρ₀ τ) (B : GlobalTheory.ExportSeries.Base (Vc D j) (Wc D j)) (t : Twist D Circle) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi (Vc D j) D.R.nV), IdFrame hF P → B.F.βS = 1 → (∀ PP, PP ∈ B.G.Pg ↔ ∃ kv, PP = NX.pG D kv) → Function.Injective (NX.pG D) → t.Q = M.QP → B.de.Q = M.DP → ∀ (iso : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), ZMod (D.host.g kv.1) ≃+* kP (NX.pG D kv)) (eG : G0g D.nd ≃* G0 B.G.Pg (Wc D j).rank), (∀ (g : G0g D.nd) kv (h : NX.pG D kv ∈ B.G.Pg) (a c : Fin (Wc D j).rank), (eG g ⟨NX.pG D kv, h⟩).val a c = iso kv ((g kv).val (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c))) → (∀ g, eG g ∈ B.G.P.H ↔ g ∈ D.nexp.U) → D.nexp.U = NX.Uup (fun kv : (Σ kk : Fin 2, D.nd.PlG kk) => D.host.g kv.1) D.R.r → Disjoint M.QP M.DP → ∀ (e₀ : FractionRing (D.ntw.O i) →+* ℂ) (ek : NX.Kk D i k →+* ℂ), (∀ x, ek (NX.toKk D i k x) = e₀ x) → NX.IsStdGeneric (fun kv : (Σ kk : Fin 2, D.nd.PlG kk) => D.host.g kv.1) D.R.r (D.nexp.psiU i b) → (∀ (u : D.nexp.U) hu, ((B.G.P.chi ⟨eG u, hu⟩ : ℂˣ) : ℂ) = e₀ (D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ)) → (∀ kv (x : (ZMod (D.host.g kv.1))ˣ) (z : (kP (NX.pG D kv))ˣ), (z : kP (NX.pG D kv)) = iso kv x → ((B.G.muC (NX.pG D kv) z : ℂˣ) : ℂ) = e₀ (τ kv x : (FractionRing (D.ntw.O i))ˣ)) → (∀ PP ∈ M.QP, ∀ u : 𝓞 D.host.E, u ∉ PP.asIdeal → ∀ z : (kP PP)ˣ, (z : kP PP) = Ideal.Quotient.mk PP.asIdeal u → ((t.resC PP z : ℂˣ) : ℂ) = ek (NX.ofOk D i k (NX.tameVal ψ PP e u).1)) → (∀ PP ∈ M.DP, ∀ u : 𝓞 D.host.E, u ∉ PP.asIdeal → ∀ z : (kP PP)ˣ, (z : kP PP) = Ideal.Quotient.mk PP.asIdeal u → ((B.de.resC PP z : ℂˣ) : ℂ) = ek (NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) PP (if b then e else -e) u).1)) → ∀ g (h : g ∈ M.J) (h' : frameEquiv P g ∈ B.levJ t), ek ((M.χ ⟨g, h⟩ : (NX.Kk D i k)ˣ) : NX.Kk D i k) = ((B.levLam t ⟨frameEquiv P g, h'⟩ : ℂˣ) : ℂ) := by
  intro D i j b k Q ψ e W₀ _ _ ρ₀ τ M B t hF P hP hβ hPg hinj htQ hdQ iso eG heG hU hUup hdisj e₀ ek hek hgen hchi hmu
    hres hde g h h'
  obtain ⟨hn, -⟩ := id hP
  have hrW : (Wc D j).rank = D.R.r := FWT.rank_Wc j
  set X : GL (Fin (Vc D j).rank) (Lev.EAf D) := Lev.finE (Vc D j) (P.ψ g) with hX
  have hXlev : X ∈ lev D.sp.cm (Vc D j).gram B.F.βS (B.levS t) := h'
  rw [hβ] at hXlev
  obtain ⟨hparL, hPH⟩ := mem_lev.1 hXlev
  have hPgB : ∀ PP ∈ B.G.Pg, redFn 1 PP X ∈ blockTri (blkOf (Wc D j).rank ((Vc D j).rank - (Wc D j).rank)) :=
    fun PP hPP => parLev_g hparL hPP
  have hQB : ∀ PP ∈ B.de.Q ∪ t.Q, redFn 1 PP X ∈ blockTri (blk2 (Wc D j).rank) := fun PP hPP => parLev_q hparL hPP
  have hUm : g ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV := ((M.J_mem g).1 h).1
  refine (congrArg ek (M.chi_eq g h)).trans ?_
  refine Eq.trans ?_ (congrArg Units.val (GlobalTheory.MtLatConj.levelCharacter_apply_eq_levelFunction_swap B t ⟨_, h'⟩)).symm
  show ek _ = ((levFn B.F.βS (B.levS t) X : ℂˣ) : ℂ)
  rw [hβ]
  unfold levFn
  rw [map_mul, map_mul]
  simp only [Units.val_mul]
  refine (mul_assoc _ _ _).trans ?_
  refine congr (congrArg HMul.hMul ?_) ?_
  · obtain ⟨u, hu_def⟩ := eG.surjective (Subtype.val (⟨_, hPH⟩ : ↥(B.levS t).P.H))
    have hH : eG u ∈ B.G.P.H := by rw [hu_def]; exact hPH
    have hu : u ∈ D.nexp.U := (hU u).1 hH
    have hkv : ∀ kv, ek (NX.gVal D i k b kv (M.sp (NX.pG D kv)) (M.redG kv) (τ kv) (NX.locM (M.sp (NX.pG D kv)) g)) =
        e₀ (NX.psiUTot D i b (Pi.mulSingle kv (u kv))) *
          ((B.G.muC (NX.pG D kv) (dBlk (blkOf (Wc D j).rank ((Vc D j).rank - (Wc D j).rank)) 1
            (redFn 1 (NX.pG D kv) X)) : ℂˣ) : ℂ) := by
      intro kv
      have hPGk : NX.pG D kv ∈ B.G.Pg := (hPg _).2 ⟨kv, rfl⟩
      have hbOf : redFn 1 (NX.pG D kv) X ∈ blockTri (blkOf (Wc D j).rank ((Vc D j).rank - (Wc D j).rank)) :=
        hPgB _ hPGk
      have hw : (M.sp (NX.pG D kv)).w = NX.pG D kv := M.sp_w _ (Or.inr (Or.inr ⟨kv, rfl⟩))
      obtain ⟨hmat, x, hx1, hx2⟩ := typePlace hP hn hUm (M.sp (NX.pG D kv)) (NX.pG D kv) hw (D.host.g kv.1)
        (D.host.g_prime kv.1) (M.redG kv) (iso kv) D.R.r (Wc D j).rank hrW (Nat.le_add_right D.R.r D.R.t) B.hr
        (blockTri_blkOf_le _ _ hbOf)
      have hG : NX.redMat (M.sp (NX.pG D kv)).v (M.redG kv)
          (NX.topR (Nat.le_add_right D.R.r D.R.t) (NX.locM (M.sp (NX.pG D kv)) g)) =
          ((u kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
        ext a c
        apply (iso kv).injective
        refine (hmat a c).trans ?_
        have e1 := heG u kv hPGk (Fin.cast hrW.symm a) (Fin.cast hrW.symm c)
        rw [hu_def] at e1
        exact e1
      have hglOf : NX.glOf (NX.redMat (M.sp (NX.pG D kv)).v (M.redG kv)
          (NX.topR (Nat.le_add_right D.R.r D.R.t) (NX.locM (M.sp (NX.pG D kv)) g))) = u kv := by
        rw [hG]
        exact Units.ext (NX.glOf_val _ (Matrix.isUnits_det_units (u kv)))
      rw [Formalism.IndefR.NX.gVal_of (D := D) (i := i) (b := b) (k := k) (kv := kv) (s := M.sp (NX.pG D kv))
        (red := M.redG kv) (τ' := τ kv) (xm := NX.locM (M.sp (NX.pG D kv)) g) (G := _)
        (hrn := Nat.le_add_right D.R.r D.R.t) (hG := rfl) (u := x) (hu := hx1), map_mul, hek, hek]
      refine congr (congrArg HMul.hMul ?_) ?_
      · exact congrArg (fun z => e₀ (NX.psiUTot D i b (Pi.mulSingle kv z))) hglOf
      refine (hmu kv x _ ?_).symm
      rw [secondBlock_blockOf_eq_blockTwo _ hbOf]
      exact hx2.symm
    rw [map_prod, Finset.prod_congr rfl fun kv _ => hkv kv, Finset.prod_mul_distrib]
    congr 1
    · rw [← map_prod, psiU_prod i b hUup hgen u hu, ← hchi ⟨u, hu⟩ hH, extendOne_of_mem _ hPH]
      exact congrArg (fun z => ((B.G.P.chi z : ℂˣ) : ℂ)) (Subtype.ext hu_def)
    · show _ = ((∏ PP ∈ B.G.Pg, ∏ c ∈ Finset.range 1, B.G.muC PP
        (dBlk (blkOf (Wc D j).rank ((Vc D j).rank - (Wc D j).rank)) (c + 1) (redFn 1 PP X)) : ℂˣ) : ℂ)
      have hPgeq : B.G.Pg = Finset.univ.image (NX.pG D) := by
        ext PP
        simp only [Finset.mem_image, Finset.mem_univ, true_and, hPg PP, eq_comm]
      rw [hPgeq, Finset.prod_image (fun a _ b _ hab => hinj hab), Units.coe_prod]
      refine Finset.prod_congr rfl fun kv _ => ?_
      rw [Finset.prod_range_one]
  · show _ = ((∏ PP ∈ B.de.Q ∪ t.Q, (B.de.locC PP * t.locC PP)
      (dBlk (blk2 (Wc D j).rank) 1 (redFn 1 PP X)) : ℂˣ) : ℂ)
    have hQB' : ∀ PP ∈ B.de.Q ∪ t.Q, redFn 1 PP X ∈ blockTri (blk2 (Wc D j).rank) := hQB
    rw [hdQ, htQ] at hQB' ⊢
    rw [Finset.prod_union hdisj.symm, Units.val_mul, Units.coe_prod, Units.coe_prod, map_prod, map_prod, mul_comm]
    congr 1
    · refine Finset.prod_congr rfl fun PP hPP => ?_
      have hw := M.sp_w PP (Or.inr (Or.inl hPP))
      obtain ⟨hnot, hd⟩ := qPlace hP hn hUm (M.sp PP) PP hw D.R.r _ hrW (hQB' PP (Finset.mem_union_left _ hPP))
      have hnT : PP ∉ t.Q := by rw [htQ]; exact Finset.disjoint_right.1 hdisj hPP
      have hD : PP ∈ B.de.Q := by rw [hdQ]; exact hPP
      rw [MonoidHom.mul_apply, Units.val_mul, Twist.locC, Twist.locC, if_neg hnT, if_pos hD, MonoidHom.one_apply,
        Units.val_one, mul_one]
      exact (hde PP hPP _ hnot _ hd).symm
    · refine Finset.prod_congr rfl fun PP hPP => ?_
      have hw := M.sp_w PP (Or.inl hPP)
      obtain ⟨hnot, hd⟩ := qPlace hP hn hUm (M.sp PP) PP hw D.R.r _ hrW (hQB' PP (Finset.mem_union_right _ hPP))
      have hnD : PP ∉ B.de.Q := by rw [hdQ]; exact Finset.disjoint_left.1 hdisj hPP
      have hT : PP ∈ t.Q := by rw [htQ]; exact hPP
      rw [MonoidHom.mul_apply, Units.val_mul, Twist.locC, Twist.locC, if_neg hnD, if_pos hT, MonoidHom.one_apply,
        Units.val_one, one_mul]
      exact (hres PP hPP _ hnot _ hd).symm

end GlobalTheory.LevChiRead
