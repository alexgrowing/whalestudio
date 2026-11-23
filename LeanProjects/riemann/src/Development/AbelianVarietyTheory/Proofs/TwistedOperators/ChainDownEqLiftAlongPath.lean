import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilDatumAnisotropicKernelPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links Formalism.L2.DIV GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChainDown

open GlobalTheory.FunObj GlobalTheory.RowChain

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (M : GlobalTheory.FunObj.Vol G)

theorem pathLift_comp_split {X Y : Node} (p : Path T X Y) (F : Fn G X) : ∀ {Z : Node} (q : Path T Y Z) (d : PureT G (p.comp q)),
    liftP Wl M (p.comp q) d F = liftP Wl M q (splitFam q d).2 (liftP Wl M p (splitFam q d).1 F)
  | _, .nil, _ => rfl
  | _, .snoc a q, d => congrArg (liftA Wl M a d.2) (pathLift_comp_split p F q d.1)

variable {G} (t : T) (i : ℕ)

noncomputable def lowLift {N : ℕ} (g : ∀ j, j < N → Sch G (.down t i j)) :
    ∀ n, n ≤ N → Fn G (.grid i n) → Fn G (.grid i 0)
  | 0, _, F => F
  | n + 1, h, F => lowLift g n (Nat.le_of_succ_le h) (liftA Wl M (.down t i n) (g n h) F)

theorem lowLift_congr {N N' : ℕ} (g : ∀ j, j < N → Sch G (.down t i j)) (g' : ∀ j, j < N' → Sch G (.down t i j)) :
    ∀ n (h : n ≤ N) (h' : n ≤ N'), (∀ j (hj : j < n), g j (by omega) = g' j (by omega)) →
      ∀ F, lowLift Wl M t i g n h F = lowLift Wl M t i g' n h' F
  | 0, _, _, _, _ => rfl
  | n + 1, h, h', hg, F => by
    show lowLift Wl M t i g n _ (liftA Wl M (.down t i n) (g n h) F) = lowLift Wl M t i g' n _ (liftA Wl M (.down t i n) (g' n h') F)
    rw [hg n (Nat.lt_succ_self n)]
    exact lowLift_congr g g' n _ _ (fun j hj => hg j (by omega)) _

theorem pathLift_downPath : ∀ n (d : PureT G (downPath t i n)) (F : Fn G (.grid i n)),
    liftP Wl M (downPath t i n) d F = lowLift Wl M t i (getD t i n d) n le_rfl F
  | 0, _, _ => rfl
  | n + 1, d, F => by
    have e := pathLift_comp_split G Wl M (Path.one (.down t i n)) F (downPath t i n) d
    refine e.trans ?_
    rw [pathLift_downPath n]
    show _ = lowLift Wl M t i (getD t i (n + 1) d) n _ (liftA Wl M (.down t i n) (getD t i (n + 1) d n (Nat.lt_succ_self n)) F)
    have hx : getD t i (n + 1) d n (Nat.lt_succ_self n) =
        (splitFam (p := Path.one (.down t i n)) (downPath t i n) d).1.2 := by
      rw [getD, dif_neg (lt_irrefl n)]
    rw [hx]
    refine lowLift_congr Wl M t i _ _ n _ _ (fun j hj => ?_) _
    show _ = getD t i (n + 1) d j _
    rw [getD, dif_pos hj]

def castFn {n n' : ℕ} (e : n = n') (F : Fn G (.grid i n)) : Fn G (.grid i n') :=
  Eq.rec (motive := fun k _ => Fn G (.grid i k)) F e

theorem lowLift_two {N : ℕ} (g : ∀ j, j < N → Sch G (.down t i j)) (j n : ℕ) (hn : n ≤ N) (e : j + 1 + 1 = n)
    (F : Fn G (.grid i n)) :
    lowLift Wl M t i g n hn F = lowLift Wl M t i g j (by omega)
      (liftA Wl M (.down t i j) (g j (by omega)) (liftA Wl M (.down t i (j + 1)) (g (j + 1) (by omega)) (castFn i e.symm F))) := by
  subst e
  rfl

theorem castLift (j n : ℕ) (e : j + 1 + 1 = n) (f : Sch G (.down t D.R.m (j + 1))) (F : Fn G (.grid D.R.m n)) :
    GlobalTheory.MixPer.liftS (castOm G e (Wl.om (.mu t D.R.m (j + 1)))) (M.ν (.grid D.R.m n)) (M.fd (.grid D.R.m n)) F (castSch G e f) =
      liftA Wl M (.down t D.R.m (j + 1)) f (castFn D.R.m e.symm F) := by
  subst e
  rfl

variable {t M}

theorem chainFrom_down (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (F : Fn G (.grid D.R.m D.R.m)) :
    ∀ σ j (hj : j + 2 * σ + 2 = D.R.m) (vN : GlobalTheory.Unf.VolN (besDecAt G j σ hj)),
      lowLift Wl M t D.R.m (getD t D.R.m D.R.m d) D.R.m le_rfl F = lowLift Wl M t D.R.m (getD t D.R.m D.R.m d) j (by omega)
        ((chainFrom G Wl t hM σ j hj vN).down (dataFrom G Wl t hM d σ j hj vN) F)
  | 0, j, hj, vN => by
    rw [lowLift_two Wl M t _ _ j D.R.m le_rfl (by omega) F,
      ← castLift Wl M t j D.R.m (by omega) (getD t D.R.m D.R.m d (j + 1) (by omega)) F]
    rfl
  | σ + 1, j, hj, vN =>
    (chainFrom_down hM d F σ (j + 1 + 1) (by omega) _).trans
      ((lowLift_two Wl M t D.R.m (getD t D.R.m D.R.m d) j (j + 1 + 1) (by omega) rfl _).trans rfl)

end GlobalTheory.RowChainDown

namespace GlobalTheory.RowChainDown

open GlobalTheory.FunObj GlobalTheory.RowChain

theorem chain_down_eq_liftP : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) (M : GlobalTheory.FunObj.Vol G)
    (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (F : Fn G (.grid D.R.m D.R.m)),
    (GlobalTheory.RowChain.chain G Wl t hM).down (GlobalTheory.RowChain.chainData G Wl t hM d) F = liftP Wl M (downPath t D.R.m D.R.m) d F := fun G Wl t M hM d F => by
  show (chainFrom G Wl t hM _ 0 top_idx (topVN hM)).down (dataFrom G Wl t hM d _ 0 top_idx (topVN hM)) F = _
  rw [pathLift_downPath]
  exact (chainFrom_down Wl hM d F _ 0 top_idx (topVN hM)).symm

end GlobalTheory.RowChainDown
