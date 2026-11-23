import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameKeepsMatricesSplitPlaceReductionLocalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.MtLev

theorem blockSizes_sub_eq_twoBlock {n : ℕ} (r : ℕ) : (Formalism.L2.DIV.blkOf (n := n) r (n - r)) = Formalism.L2.DIV.blk2 r := by
  funext a
  unfold Formalism.L2.DIV.blkOf Formalism.L2.DIV.blk2
  split_ifs with h
  · rfl
  · have : (a.val - r) / (n - r) = 0 := Nat.div_eq_of_lt (by omega)
    rw [this]

theorem mem_levJ_iff {D : D7} {S T : HSp D} {n : ℕ} (B : Base S T) (t : Twist D Circle) (P : principalLevelFrame.RowPsi S n) (g : GAf D.host.E n) :
    frameEquiv P g ∈ B.levJ t ↔ Lev.finE S (P.ψ g) ∈ Formalism.L2.DIV.lev D.sp.cm S.gram B.F.βS (B.levS t) := Iff.rfl

end GlobalTheory.MtLev

namespace GlobalTheory.MtLev

variable {D : D7} {V : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {P : principalLevelFrame.RowPsi V n}

theorem loc_zero (hP : IdFrame hF P) (hn : V.rank = n) {κ : GAf D.host.E n} (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n)
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (a c : Fin V.rank) :
    Valued.v (NX.locM s κ (Fin.cast hn a) (Fin.cast hn c)) < 1 ↔
      (Formalism.L2.DIV.redFn 1 s.w (Lev.finE V (P.ψ κ)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.DIV.kP s.w)) a c = 0 := by
  have h := ((GlobalTheory.T.frameKeepsMatrices_splitPlace_reduction_local D V n hF P hP hn κ).2 s hκ a c).2 0
  simp only [map_zero, zero_sub, Valuation.map_neg] at h
  exact h

theorem loc_one (hP : IdFrame hF P) (hn : V.rank = n) {κ : GAf D.host.E n} (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n)
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (a : Fin V.rank) :
    Valued.v (NX.locM s κ (Fin.cast hn a) (Fin.cast hn a) - 1) < 1 ↔
      (Formalism.L2.DIV.redFn 1 s.w (Lev.finE V (P.ψ κ)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.DIV.kP s.w)) a a = 1 := by
  have h := ((GlobalTheory.T.frameKeepsMatrices_splitPlace_reduction_local D V n hF P hP hn κ).2 s hκ a a).2 1
  simp only [map_one] at h
  rw [Valuation.map_sub_swap] at h
  exact h

theorem cast_surj (hn : V.rank = n) (a : Fin n) : ∃ a' : Fin V.rank, Fin.cast hn a' = a :=
  ⟨Fin.cast hn.symm a, by simp⟩

theorem inParah_iff (hP : IdFrame hF P) (hn : V.rank = n) {κ : GAf D.host.E n} (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n)
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (r : ℕ) :
    NX.InParah s.v r (NX.locM s κ) ↔ Formalism.L2.DIV.redFn 1 s.w (Lev.finE V (P.ψ κ)) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
  constructor
  · rintro ⟨-, h⟩ i j hij
    unfold Formalism.L2.DIV.blk2 at hij
    split_ifs at hij with h1 h2 <;> try omega
    exact (loc_zero hP hn hκ s i j).1 (h _ _ (by simpa using h2) (by simpa using h1))
  · intro h
    refine ⟨fun a b => ?_, fun a b ha hb => ?_⟩
    · obtain ⟨a', rfl⟩ := cast_surj hn a
      obtain ⟨b', rfl⟩ := cast_surj hn b
      exact ((GlobalTheory.T.frameKeepsMatrices_splitPlace_reduction_local D V n hF P hP hn κ).2 s hκ a' b').1
    · obtain ⟨a', rfl⟩ := cast_surj hn a
      obtain ⟨b', rfl⟩ := cast_surj hn b
      refine (loc_zero hP hn hκ s a' b').2 (Formalism.L2.DIV.mem_blockTri.1 h a' b' ?_)
      simp only [Fin.coe_cast] at ha hb
      unfold Formalism.L2.DIV.blk2
      rw [if_pos hb, if_neg (by omega)]
      exact Nat.zero_lt_one

end GlobalTheory.MtLev

namespace GlobalTheory.MtLev

variable {D : D7} {V : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {P : principalLevelFrame.RowPsi V n}

def UT {m : ℕ} {k : Type} [CommRing k] (r : ℕ) (M : Matrix (Fin m) (Fin m) k) : Prop :=
  ∀ a c : Fin m, (a : ℕ) < r → (c : ℕ) < r → (c < a → M a c = 0) ∧ (a = c → M a c = 1)

theorem inLevG_iff (hP : IdFrame hF P) (hn : V.rank = n) {κ : GAf D.host.E n} (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n)
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (r : ℕ) :
    NX.InLevG s.v r (NX.locM s κ) ↔ Formalism.L2.DIV.redFn 1 s.w (Lev.finE V (P.ψ κ)) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) ∧
      UT r (Formalism.L2.DIV.redFn 1 s.w (Lev.finE V (P.ψ κ)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.DIV.kP s.w)) := by
  unfold NX.InLevG
  refine and_congr (inParah_iff hP hn hκ s r) ⟨fun h a c ha hc => ?_, fun h a b ha hb => ?_⟩
  · have h' := h (Fin.cast hn a) (Fin.cast hn c) (by simpa using ha) (by simpa using hc)
    refine ⟨fun hca => (loc_zero hP hn hκ s a c).1 (h'.1 hca), fun hac => ?_⟩
    subst hac
    exact (loc_one hP hn hκ s a).1 (h'.2 rfl)
  · obtain ⟨a', rfl⟩ := cast_surj hn a
    obtain ⟨b', rfl⟩ := cast_surj hn b
    have h' := h a' b' (by simpa using ha) (by simpa using hb)
    refine ⟨fun hba => (loc_zero hP hn hκ s a' b').2 (h'.1 hba), fun hab => ?_⟩
    have e : a' = b' := by simpa using hab
    subst e
    exact (loc_one hP hn hκ s a').2 (h'.2 rfl)

theorem UT_iff {m r : ℕ} {k : Type} [CommRing k] (hr : r ≤ m) (M : Matrix (Fin m) (Fin m) k) :
    UT r M ↔ ∀ a c : Fin r, (c < a → M (Fin.castLE hr a) (Fin.castLE hr c) = 0) ∧
      (a = c → M (Fin.castLE hr a) (Fin.castLE hr c) = 1) := by
  constructor
  · intro h a c
    have h' := h (Fin.castLE hr a) (Fin.castLE hr c) a.2 c.2
    exact ⟨fun hca => h'.1 hca, fun hac => h'.2 (by rw [hac])⟩
  · intro h a c ha hc
    have h' := h ⟨a, ha⟩ ⟨c, hc⟩
    have ea : Fin.castLE hr ⟨a, ha⟩ = a := Fin.ext rfl
    have ec : Fin.castLE hr ⟨c, hc⟩ = c := Fin.ext rfl
    rw [ea, ec] at h'
    refine ⟨fun hca => h'.1 hca, fun hac => h'.2 (by subst hac; rfl)⟩

end GlobalTheory.MtLev

namespace GlobalTheory.MtLev

theorem rTup_mem_iff (D : D7) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)) (t : Twist D Circle)
    (x : GL (Fin (Vc D j).rank) (Lev.EAf D)) (hPg : ∀ PP, PP ∈ B.G.Pg ↔ ∃ kv, PP = NX.pG D kv)
    (iso : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), ZMod (D.host.g kv.1) ≃+* kP (NX.pG D kv))
    (eG : G0g D.nd ≃* G0 B.G.Pg (Wc D j).rank)
    (hiso : ∀ (g : G0g D.nd) kv (h : NX.pG D kv ∈ B.G.Pg) (a c : Fin (Wc D j).rank), (eG g ⟨NX.pG D kv, h⟩).val a c =
      iso kv ((g kv).val (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c)))
    (hH : ∀ g, eG g ∈ B.G.P.H ↔ g ∈ D.nexp.U)
    (hU : D.nexp.U = NX.Uup (fun kv : (Σ kk : Fin 2, D.nd.PlG kk) => D.host.g kv.1) D.R.r)
    (hblk : ∀ kv, Formalism.L2.DIV.redFn 1 (NX.pG D kv) x ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (Wc D j).rank)) :
    Formalism.L2.DIV.rTup 1 (B.levS t) x ∈ B.G.P.H ↔ ∀ kv, ∀ a c : Fin (Wc D j).rank,
      (c < a → (Formalism.L2.DIV.redFn 1 (NX.pG D kv) x : Matrix (Fin (Vc D j).rank) (Fin (Vc D j).rank) (kP (NX.pG D kv))) (Fin.castLE B.hr a) (Fin.castLE B.hr c) = 0) ∧
      (a = c → (Formalism.L2.DIV.redFn 1 (NX.pG D kv) x : Matrix (Fin (Vc D j).rank) (Fin (Vc D j).rank) (kP (NX.pG D kv))) (Fin.castLE B.hr a) (Fin.castLE B.hr c) = 1) := by
  set y : G0 B.G.Pg (Wc D j).rank := Formalism.L2.DIV.rTup 1 (B.levS t) x with hy
  have key : ∀ kv (h : NX.pG D kv ∈ B.G.Pg) (a c : Fin (Wc D j).rank),
      ((eG.symm y) kv).val (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c) =
        (iso kv).symm ((Formalism.L2.DIV.redFn 1 (NX.pG D kv) x : Matrix (Fin (Vc D j).rank) (Fin (Vc D j).rank) (kP (NX.pG D kv))) (Fin.castLE B.hr a) (Fin.castLE B.hr c)) := by
    intro kv h a c
    have e := hiso (eG.symm y) kv h a c
    rw [MulEquiv.apply_symm_apply] at e
    rw [RingEquiv.eq_symm_apply, ← e]
    have e2 : (y ⟨NX.pG D kv, h⟩ : Matrix (Fin (Wc D j).rank) (Fin (Wc D j).rank) (kP (NX.pG D kv))) =
        (Formalism.L2.DIV.upperLeftBlock B.hr (Formalism.L2.DIV.redFn 1 (NX.pG D kv) x) : Matrix (Fin (Wc D j).rank) (Fin (Wc D j).rank) (kP (NX.pG D kv))) := rfl
    rw [e2, Formalism.L2.DIV.upper_block_val_submatrix B.hr (hblk kv)]
    rfl
  have hmem := hH (eG.symm y)
  rw [MulEquiv.apply_symm_apply] at hmem
  refine hmem.trans ?_
  rw [hU, NX.mem_Uup]
  refine forall_congr' fun kv => ?_
  have h : NX.pG D kv ∈ B.G.Pg := (hPg _).2 ⟨kv, rfl⟩
  have hc : ∀ a' : Fin D.R.r, ∃ a : Fin (Wc D j).rank, Fin.cast (FWT.rank_Wc j) a = a' :=
    fun a' => ⟨Fin.cast (FWT.rank_Wc j).symm a', by simp⟩
  constructor
  · rintro ⟨h1, h2⟩ a c
    refine ⟨fun hca => ?_, fun hac => ?_⟩
    · have e : ((eG.symm y) kv).val (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c) = 0 := h1 hca
      rw [key kv h] at e
      exact (map_eq_zero_iff _ (iso kv).symm.injective).1 e
    · subst hac
      have e := h2 (Fin.cast (FWT.rank_Wc j) a)
      rw [key kv h] at e
      exact (iso kv).symm.injective (by rw [e, map_one])
  · intro H
    refine ⟨fun a' c' hca => ?_, fun a' => ?_⟩
    · obtain ⟨a, rfl⟩ := hc a'
      obtain ⟨c, rfl⟩ := hc c'
      rw [key kv h, (H a c).1 hca, map_zero]
    · obtain ⟨a, rfl⟩ := hc a'
      rw [key kv h, (H a a).2 rfl, map_one]

end GlobalTheory.MtLev

namespace GlobalTheory.MtLev

theorem levMem : ∀ (D : D7) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀] (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀) (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (M : NX.MtVReal D i (j.1 + 1) b k Q ψ e W₀ ρ₀ τ) (B : GlobalTheory.ExportSeries.Base (Vc D j) (Wc D j)) (t : Twist D Circle) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi (Vc D j) D.R.nV), IdFrame hF P → B.F.βS = 1 → (∀ PP, PP ∈ B.G.Pg ↔ ∃ kv, PP = NX.pG D kv) → Function.Injective (NX.pG D) → t.Q = M.QP → B.de.Q = M.DP → ∀ (iso : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), ZMod (D.host.g kv.1) ≃+* kP (NX.pG D kv)) (eG : G0g D.nd ≃* G0 B.G.Pg (Wc D j).rank), (∀ (g : G0g D.nd) kv (h : NX.pG D kv ∈ B.G.Pg) (a c : Fin (Wc D j).rank), (eG g ⟨NX.pG D kv, h⟩).val a c = iso kv ((g kv).val (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c))) → (∀ g, eG g ∈ B.G.P.H ↔ g ∈ D.nexp.U) → D.nexp.U = NX.Uup (fun kv : (Σ kk : Fin 2, D.nd.PlG kk) => D.host.g kv.1) D.R.r → ∀ g, g ∈ M.J ↔ frameEquiv P g ∈ B.levJ t := by
  intro D i j b k Q ψ e W₀ _ _ ρ₀ τ M B t hF P hP hβ hPg hinj htQ hdQ iso eG hiso hH hU g
  classical
  obtain ⟨hn, -⟩ := id hP
  have hrW : (Wc D j).rank = D.R.r := FWT.rank_Wc j
  have hSt := (GlobalTheory.T.frameKeepsMatrices_splitPlace_reduction_local D (Vc D j) D.R.nV hF P hP hn g).1
  have hUA := GlobalTheory.LevSplit.finE_mem_UA (Vc D j) (P.ψ g)
  have levG_iff : ∀ (hU' : g ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV) kv,
      NX.InLevG (M.sp (NX.pG D kv)).v D.R.r (NX.locM (M.sp (NX.pG D kv)) g) ↔
        Formalism.L2.DIV.redFn 1 (NX.pG D kv) (Lev.finE (Vc D j) (P.ψ g)) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (Wc D j).rank) ∧
        UT (Wc D j).rank (Formalism.L2.DIV.redFn 1 (NX.pG D kv) (Lev.finE (Vc D j) (P.ψ g)) :
          Matrix (Fin (Vc D j).rank) (Fin (Vc D j).rank) (kP (NX.pG D kv))) := by
    intro hU' kv
    have h := inLevG_iff hP hn hU' (M.sp (NX.pG D kv)) D.R.r
    rw [M.sp_w _ (Or.inr (Or.inr ⟨kv, rfl⟩))] at h
    rw [h, hrW]
  have par_iff : ∀ (hU' : g ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV) PP, (PP ∈ M.QP ∨ PP ∈ M.DP) →
      (NX.InParah (M.sp PP).v D.R.r (NX.locM (M.sp PP) g) ↔
        Formalism.L2.DIV.redFn 1 PP (Lev.finE (Vc D j) (P.ψ g)) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (Wc D j).rank)) := by
    intro hU' PP hPP
    have h := inParah_iff hP hn hU' (M.sp PP) D.R.r
    rw [M.sp_w _ (hPP.elim Or.inl (fun h => Or.inr (Or.inl h)))] at h
    rw [h, hrW]
  have hblkOf : Formalism.L2.DIV.blkOf (n := (Vc D j).rank) (Wc D j).rank ((Vc D j).rank - (Wc D j).rank) =
      Formalism.L2.DIV.blk2 (Wc D j).rank := blockSizes_sub_eq_twoBlock _
  rw [M.J_mem, mem_levJ_iff, hβ, Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev]
  constructor
  · rintro ⟨hU', hG, hQ, hD⟩
    have hGk := fun kv => (levG_iff hU' kv).1 (hG kv)
    have hblk : ∀ kv, Formalism.L2.DIV.redFn 1 (NX.pG D kv) (Lev.finE (Vc D j) (P.ψ g)) ∈
        Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (Wc D j).rank) := fun kv => (hGk kv).1
    refine ⟨⟨hUA, hSt.1 hU', fun PP hPP => ?_, fun PP hPP => ?_⟩, ?_⟩
    · obtain ⟨kv, rfl⟩ := (hPg PP).1 hPP
      change _ ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf (Wc D j).rank ((Vc D j).rank - (Wc D j).rank))
      rw [hblkOf]
      exact hblk kv
    · change PP ∈ B.de.Q ∪ t.Q at hPP
      rw [hdQ, htQ] at hPP
      rcases Finset.mem_union.1 hPP with h | h
      · exact (par_iff hU' PP (Or.inr h)).1 (hD PP h)
      · exact (par_iff hU' PP (Or.inl h)).1 (hQ PP h)
    · exact (rTup_mem_iff D j B t _ hPg iso eG hiso hH hU hblk).2 fun kv => (UT_iff B.hr _).1 (hGk kv).2
  · rintro ⟨⟨-, hSt', hPg', hQ'⟩, hR⟩
    have hU' := hSt.2 hSt'
    have hblk : ∀ kv, Formalism.L2.DIV.redFn 1 (NX.pG D kv) (Lev.finE (Vc D j) (P.ψ g)) ∈
        Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (Wc D j).rank) := fun kv => by
      have h := hPg' (NX.pG D kv) ((hPg _).2 ⟨kv, rfl⟩)
      change _ ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf (Wc D j).rank ((Vc D j).rank - (Wc D j).rank)) at h
      rwa [hblkOf] at h
    have hR' := (rTup_mem_iff D j B t _ hPg iso eG hiso hH hU hblk).1 hR
    have hQm : ∀ PP, PP ∈ M.QP ∨ PP ∈ M.DP → PP ∈ (B.levS t).Q := fun PP h => by
      change PP ∈ B.de.Q ∪ t.Q
      rw [hdQ, htQ]
      exact h.elim (Finset.mem_union_right _) (Finset.mem_union_left _)
    refine ⟨hU', fun kv => (levG_iff hU' kv).2 ⟨hblk kv, (UT_iff B.hr _).2 (hR' kv)⟩,
      fun PP hPP => (par_iff hU' PP (Or.inl hPP)).2 (hQ' PP (hQm PP (Or.inl hPP))),
      fun PP hPP => (par_iff hU' PP (Or.inr hPP)).2 (hQ' PP (hQm PP (Or.inr hPP)))⟩

end GlobalTheory.MtLev
