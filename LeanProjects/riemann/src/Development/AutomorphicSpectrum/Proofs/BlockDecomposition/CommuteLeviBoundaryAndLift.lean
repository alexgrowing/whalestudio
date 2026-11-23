import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardBlocksLevelSum
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CenterActionCommutesLeviDifference

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.PairMult.CapProdProof

open Formalism.REAL (GlRel qdet)
open CompanionTheory.D.LK (Pos)
open GlobalTheory.CompanionTheory.RgCOBlock (fa fb sz)

variable {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem evalPair_injLeft_eq_eval (E1 E2 : Fin n → Fin n → Module.End ℂ W) (s : Bool) (z : FreeAlgebra ℂ (Fin n × Fin n)) :
    ev2 E1 E2 (injL s z) = CompanionTheory.D.LK.ev (if s then E1 else E2) z := by
  have e : (ev2 E1 E2).comp (injL s) = CompanionTheory.D.LK.ev (if s then E1 else E2) := by
    apply FreeAlgebra.hom_ext
    funext p
    cases s <;> simp [ev2, injL, CompanionTheory.D.LK.ev]
  exact DFunLike.congr_fun e z

theorem evB_injL (lev : Fin n → ℕ) (X1 X2 : Fin n → Fin n → Module.End ℂ W) (s : Bool)
    (z : FreeAlgebra ℂ (Fin n × Fin n)) :
    evB lev X1 X2 (injL s z) = CompanionTheory.RgExh.U.evL lev (if s then X1 else X2) z := by
  have e : (evB lev X1 X2).comp (injL s) = CompanionTheory.RgExh.U.evL lev (if s then X1 else X2) := by
    apply FreeAlgebra.hom_ext
    funext p
    cases s <;> simp [evB, injL, CompanionTheory.RgExh.U.evL]
  exact DFunLike.congr_fun e z

theorem commute_ev (T : Module.End ℂ W) (E : Fin n → Fin n → Module.End ℂ W) (h : ∀ p q, Commute T (E p q))
    (z : FreeAlgebra ℂ (Fin n × Fin n)) : Commute T (CompanionTheory.D.LK.ev E z) := by
  induction z using FreeAlgebra.induction with
  | grade0 r => rw [AlgHom.commutes]; exact (Algebra.commutes r T).symm
  | grade1 p => simpa [CompanionTheory.D.LK.ev] using h p.1 p.2
  | mul a b ha hb => rw [map_mul]; exact ha.mul_right hb
  | add a b ha hb => rw [map_add]; exact ha.add_right hb

def wL {V : Type} [AddCommGroup V] [Module ℂ V] (s : Bool) (w : Pos n → V) (l : Lt n) : V :=
  (1 / 2 : ℂ) • (if l.1 || s then w l.2 else -w l.2)

theorem sum_letters (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ W) (s : Bool) (w : Pos n → W) :
    (∑ l : Lt n, if inUL lev l then Tl E1 E2 l (wL s w l) else 0) =
      ∑ i : Pos n, if CompanionTheory.RgExh.U.inU lev i then (if s then E1 else E2) i.1.1 i.1.2 (w i) else 0 := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : lev i.1.1 < lev i.1.2
  · cases s <;> simp [hi, Tl, Ts, wL, CompanionTheory.RgExh.U.inU] <;> module
  · simp [hi, CompanionTheory.RgExh.U.inU]

theorem isSubL_inUL (lev : Fin n → ℕ) : IsSubL lev (inUL lev) := by
  refine ⟨fun l h => h, fun s t i j k h1 h2 h3 hi hj => ?_⟩
  show lev k.1.1 < lev k.1.2
  have a : lev i.1.1 < lev i.1.2 := hi
  have b : lev j.1.1 < lev j.1.2 := hj
  rw [h2, h3]
  rw [h1] at a
  exact a.trans b

theorem commute_levi_boundary_and_lift (n M : ℕ) (lev : Fin n → ℕ) (h : ∑ i, sz lev M i = n) (hm : Monotone lev)
    (hlev : ∀ (i : Fin M) (p : Fin (sz lev M i)), lev (GlobalTheory.SmGL.stdBlocks (sz lev M) h ⟨i, p⟩) = (i : ℕ))
    (s : Bool) (Y : ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V)
    (hP : PairRel E1 E2) :
    (∀ l, inUL lev l → Commute (Tl E1 E2 l) (ev2 E1 E2 (injL s (fa n Y)))) ∧
      ∀ x : V, ∃ w : Lt n → V, ev2 E1 E2 (injL s (fa n Y)) x - evB lev E1 E2 (injL s (fb (sz lev M) h Y)) x =
        ∑ l : Lt n, if inUL lev l then Tl E1 E2 l (w l) else 0 := by
  have hG : GlRel (if s then E1 else E2) := by
    cases s
    · simpa using hP.2.1
    · simpa using hP.1
  obtain ⟨c1, c2⟩ := GlobalTheory.CompanionTheory.RgCOBlock.co_hyp n M lev (sz lev M) h Y hm hlev V _ hG
  refine ⟨fun l hl => ?_, fun x => ?_⟩
  · rw [evalPair_injLeft_eq_eval]
    have hc := c1 l.2 hl
    have h1 : Commute (E1 l.2.1.1 l.2.1.2) (CompanionTheory.D.LK.ev (if s then E1 else E2) (fa n Y)) := by
      cases s
      · exact commute_ev _ _ (fun p q => hP.2.2 _ _ p q) _
      · simpa using hc
    have h2 : Commute (E2 l.2.1.1 l.2.1.2) (CompanionTheory.D.LK.ev (if s then E1 else E2) (fa n Y)) := by
      cases s
      · simpa using hc
      · exact commute_ev _ _ (fun p q => (hP.2.2 p q _ _).symm) _
    rcases l with ⟨b, i⟩
    cases b
    · simpa [Tl, Ts] using h1.sub_left h2
    · simpa [Tl, Ts] using h1.add_left h2
  · obtain ⟨w, hw⟩ := c2 x
    refine ⟨wL s w, ?_⟩
    rw [sum_letters, evalPair_injLeft_eq_eval, evB_injL]
    exact hw

theorem capProd : GenCOU2 → CapProd := by
  intro hG n M lev h hm hM V _ _ E1 E2 hP s Y r hq j x hS hD hc
  have hlev := (GlobalTheory.CompanionTheory.RgCOBlock.stdBlocks_clusters n M lev h hm hM).1
  obtain ⟨w, w1, w2, w3⟩ := hG n lev (inUL lev) (injL s (fa n Y)) (injL s (fb (sz lev M) h Y)) hm (isSubL_inUL lev)
    (fun V _ _ E1 E2 hP => commute_levi_boundary_and_lift n M lev h hm hlev s Y V E1 E2 hP) V E1 E2 hP j x hS hD hc
  refine ⟨w, w1, w2, ?_⟩
  rw [← w3, evalPair_injLeft_eq_eval, GlobalTheory.CompanionTheory.RgCOBlock.ev_fa, hq]
  congr 1

end GlobalTheory.CompanionTheory.PairMult.CapProdProof
