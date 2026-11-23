import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FunKit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestExistsCombinationsOfExpansion
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceAtIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExOneEqSelf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.LocAsm

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def exInd {G : GlobalTheory.SplitFlip.Grid k} (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) :
    ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ := fun b =>
  match b with
  | .ex i j => (SetLike.coe (GlobalTheory.SplitFlip.matLat (Fin (G.rank (GlobalTheory.SplitFlip.Edge.ex i j).tgt))
      (GlobalTheory.SplitFlip.stdLat k (Fin (G.rank (GlobalTheory.SplitFlip.Edge.ex i j).src))))).indicator 1
  | .theta i j => φ (.theta i j)

theorem isNatDatum_exInd {G : GlobalTheory.SplitFlip.Grid k} {ϖ : kˣ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) {e : ℕ} {γ : List GlobalTheory.SplitFlip.Edge}
    (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ)
    (hφ : ∀ b ∈ γ, GlobalTheory.SplitFlip.IsNatDatum ϖ e (φ b)) : ∀ b ∈ γ, GlobalTheory.SplitFlip.IsNatDatum ϖ e (exInd φ b) := by
  intro b hb
  cases b with
  | ex i j => exact GlobalTheory.SplitFlip.hasDepth_indicator hϖ e _
  | theta i j => exact hφ _ hb

variable [MeasurableSpace k] [BorelSpace k]

theorem flatTensor_exOne_eq_exInd {G : GlobalTheory.SplitFlip.Grid k} (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k)
    (keep : Bool) (g : G.VertexGroup) (γ : List GlobalTheory.SplitFlip.Edge)
    (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (x : ColArgs G) :
    flatTensor hs ψ ν (moved G keep g (G.lines₂ γ (exOne φ))) x 0 =
      flatTensor hs ψ ν (moved G keep g (G.lines₂ γ (exInd φ))) x 0 := by
  unfold flatTensor
  congr 1
  funext v
  unfold flatIntegrand moved GlobalTheory.SplitFlip.Grid.pathAct GlobalTheory.SplitFlip.Grid.lines₂
  have key : (γ.map fun b => exOne φ b (G.moveArgs .one g (fill hs x 0 v) b)).prod =
      (γ.map fun b => exInd φ b (G.moveArgs .one g (fill hs x 0 v) b)).prod := by
    refine congrArg List.prod (List.map_congr_left fun b _ => ?_)
    cases b with
    | theta i j => rfl
    | ex i j =>
      have h0 : G.moveArgs .one g (fill hs x 0 v) (.ex i j) = 0 := by
        have : fill hs x 0 v (.ex i j) = 0 := by
          unfold fill
          dsimp only
          split_ifs <;> ext <;> simp
        simp [GlobalTheory.SplitFlip.Grid.moveArgs, this]
      rw [h0]
      simp [exOne, exInd, Set.indicator_of_mem (Submodule.zero_mem _)]
  rw [key]

end Local

section Abstract

variable {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type} [∀ j, AddCommGroup (A j)]

open Classical in

theorem sum_reps_mul_indicator_eq_self (SA BA : ∀ j, A j → Prop) (hSA : ∀ j a b, SA j a → SA j b → SA j (a - b)) (R : ∀ j, Finset (A j))
    (hR2 : ∀ j x, BA j x → ∃ r ∈ R j, SA j (x - r)) (hR3 : ∀ j, ∀ r ∈ R j, ∀ r' ∈ R j, SA j (r - r') → r = r')
    (F : (∀ j, A j) → ℂ) (hper : ∀ x a, (∀ j, SA j (a j)) → F (x + a) = F x) (x : ∀ j, A j)
    (hsupp : F x ≠ 0 → ∀ j, BA j (x j)) :
    ∑ q : (∀ j, R j), F (fun j => (q j).1) * ∏ j, (if SA j (x j - (q j).1) then (1 : ℂ) else 0) = F x := by
  by_cases hex : ∃ q : (∀ j, R j), ∀ j, SA j (x j - (q j).1)
  · obtain ⟨q₀, hx⟩ := hex
    rw [Finset.sum_eq_single q₀]
    · rw [Finset.prod_eq_one fun j _ => if_pos (hx j), mul_one]
      have h := hper (fun j => (q₀ j).1) (x - fun j => (q₀ j).1) hx
      rw [add_sub_cancel] at h
      exact h.symm
    · intro q _ hne
      by_contra hz
      apply hne
      have h1 : ∀ j, SA j (x j - (q j).1) := fun j => by
        by_contra h0
        apply hz
        rw [Finset.prod_eq_zero (Finset.mem_univ j) (if_neg h0)]; ring
      refine funext fun j => Subtype.ext ?_
      have := hSA j _ _ (hx j) (h1 j)
      rw [sub_sub_sub_cancel_left] at this
      exact hR3 j _ (q j).2 _ (q₀ j).2 this
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_zero]
    · symm
      by_contra hne
      apply hex
      have sx := hsupp hne
      choose r hr hrs using fun j => hR2 j (x j) (sx j)
      exact ⟨fun j => ⟨r j, hr j⟩, hrs⟩
    · intro q _
      by_contra hz
      apply hex
      refine ⟨q, fun j => ?_⟩
      by_contra h0
      apply hz
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (if_neg h0)]; ring

end Abstract

set_option maxHeartbeats 1000000 in

theorem colFlat_expansion : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (β : CosFam ch.G t) (w : locPl ch.G t) (eL : AE D), IsIdemSum eL {w.1} → ∀ (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ), (∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ b)) → ∃ (I : Type) (S : Finset I) (x : I → ℂ) (d : I → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j)) (c : I → Combs ch.G), (∀ i ∈ S, ∀ j : Fin D.R.m, (d i j).e = eL ∧ IsCombOf ch.W (d i j) ((c i).1 j)) ∧ ∀ y : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), (∀ j, IsHalf eL (y j)) → ∑ i ∈ S, x i * ∏ j, (d i j).fn (y j) = flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne φ))) (ch.S.colAt t w.1 y) 0 := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t β w eL heL φ hφ
  have hL := s.core.lev
  have hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q) := by
    obtain ⟨⟨P, -, -⟩, -⟩ := s.size
    have key : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q) := fun p hp hpp =>
      UpperTheory.Ram.Fun.coprime_QSq_of_splitK D.host hpp (P.level_split p hp)
    exact ⟨key _ D.host.pde_level.1 D.host.pde_prime, key _ D.host.pde_level.2 D.host.pde'_prime⟩
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have hg := (Good.locGrid_isGood hL ch.G ch.W t hde (hch.guard t)).1 w.1 w.2
  have h00 := hg.square 0 (by change 0 < D.R.m; omega) 0 (by change 0 < D.R.m; omega)
  haveI := (isUnitVol_unitVol w.1).1
  have hT := (locGrid ch.G t w.1).isTensor_pureTensor (unifAt w.1) (depthAt ch.G w.1)
    (GlobalTheory.SplitFlip.oppositePath D.R.m) (exInd φ) (isNatDatum_exInd (isUnif_unifAt w.1) φ hφ)
  obtain ⟨N, hF⟩ := exists_isSBArgs_flat (locGrid ch.G t w.1) one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (unifAt w.1)
    (depthAt ch.G w.1) _ (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) hm h00.unif h00.cond hT
  set Fl := flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1)
    ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (exInd φ))) with hFl
  choose Rp hR1 hR2 hR3 using fun j : Fin D.R.m => GlobalTheory.T.exists_finset_cosetReps_bounded_half_points (ch.S.βp (j + 1)) (ch.S.βp j) {w.1} eL N heL
  have sdT : ∀ j, j ≤ D.R.m → IsSelfDualC (ch.G.V (.top j)) (ch.G.Λ (.top j)) := fun j hj =>
    (ch.G.isV (X := .top j) hj fun _ h => by cases h).sd
  let d : (∀ j : Fin D.R.m, Rp j) → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j) := fun κ j =>
    { FinDatum.ind ch.G t (.top t j) {w.1} (fun w' hw' => by
        rw [Finset.mem_singleton] at hw'
        subst hw'
        exact (Good.locPl_cases w.2).elim (fun h => .inl h.1) fun h => .inr ⟨_, h.2.2, rfl⟩) eL heL with
      fn := cosLoc {w.1} eL (ch.S.βp (j + 1)) (ch.S.βp j) (N : ℤ) (κ j).1
      sb := GlobalTheory.T.indicator_smallCoset_half_isSchwartzBruhat (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) (ch.G.Λ (.top j)) (ch.G.Λ (.top (j + 1))) (ch.S.βp j)
        (ch.S.βp (j + 1)) {w.1} eL N (κ j).1 (isLattice_top ch.G j.2.le) (isLattice_top ch.G j.2) (ch.S.βp_is j j.2.le)
        (ch.S.βp_is (j + 1) j.2) heL (hR1 j _ (κ j).2).1 }
  choose c₁ hc₁ using fun (κ : ∀ j : Fin D.R.m, Rp j) (j : Fin D.R.m) =>
    GlobalTheory.CombsExist.exists_isCombOf ch.W (p := .top t j) (sdT j j.2.le) (sdT (j + 1) j.2) (d κ j)
  refine ⟨∀ j : Fin D.R.m, Rp j, Finset.univ, fun κ => Fl (ch.S.colAt t w.1 fun j => (κ j).1) 0, d,
    fun κ => (fun j => if h : j < D.R.m then c₁ κ ⟨j, h⟩ else 0, fun _ => 0), ?_, ?_⟩
  · intro κ _ j
    refine ⟨rfl, ?_⟩
    dsimp only
    rw [dif_pos j.2]
    exact hc₁ κ j
  · intro y hy
    refine Eq.trans ?_ (flatTensor_exOne_eq_exInd (G := locGrid ch.G t w.1) one_le_sLen _ _ _ _ _ φ _).symm
    have hper : ∀ (x a : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))),
        (∀ j : Fin D.R.m, IsSmall {w.1} (ch.S.βp ((j : ℕ) + 1)) (ch.S.βp j) (N : ℤ) (a j)) →
        Fl (ch.S.colAt t w.1 (x + a)) 0 = Fl (ch.S.colAt t w.1 x) 0 := fun x a ha => by
      rw [colAt_add]
      have := hF.per (ch.S.colAt t w.1 x) 0 (ch.S.colAt t w.1 a) 0 (fun j hj r s => ?_) (fun i _ r s => by simp)
      · rwa [add_zero] at this
      · rw [colAt_eq _ t w.1 _ hj]
        have := ha ⟨j, hj⟩ w.1 (Finset.mem_singleton_self _) (Fin.cast (topRank_eq ch.G t w.1 hj) r)
          (Fin.cast (topRank_eq ch.G t w.1 hj.le) s)
        rw [zpow_natCast] at this
        exact this
    have hsupp : Fl (ch.S.colAt t w.1 y) 0 ≠ 0 → ∀ j : Fin D.R.m,
        IsHalf eL (y j) ∧ IsSmall {w.1} (ch.S.βp ((j : ℕ) + 1)) (ch.S.βp j) (-(N : ℤ)) (y j) := by
      intro hne j
      refine ⟨hy j, fun w' hw' r s => ?_⟩
      rw [Finset.mem_singleton] at hw'
      subst hw'
      have := (hF.supp _ _ hne).1 j j.2 (Fin.cast (topRank_eq ch.G t w.1 j.2).symm r)
        (Fin.cast (topRank_eq ch.G t w.1 j.2.le).symm s)
      rw [colAt_eq _ t w.1 y j.2] at this
      rw [_root_.zpow_neg, zpow_natCast]
      exact this
    have key := sum_reps_mul_indicator_eq_self (ι := Fin D.R.m) (A := fun j : Fin D.R.m => WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))))
      (fun j a => IsSmall {w.1} (ch.S.βp ((j : ℕ) + 1)) (ch.S.βp j) (N : ℤ) a)
      (fun j a => IsHalf eL a ∧ IsSmall {w.1} (ch.S.βp ((j : ℕ) + 1)) (ch.S.βp j) (-(N : ℤ)) a)
      (fun _ _ _ h h' => h.sub h') Rp (fun j x h => hR2 j x h.1 h.2) hR3 (fun x => Fl (ch.S.colAt t w.1 x) 0)
      hper y hsupp
    refine (Finset.sum_congr rfl fun κ _ => ?_).trans key
    exact congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun j _ => cosLoc_eq_ite (hy j))

end GlobalTheory.LocAsm
