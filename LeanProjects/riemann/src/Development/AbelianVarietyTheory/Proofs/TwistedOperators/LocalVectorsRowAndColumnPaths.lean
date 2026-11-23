import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilDatumAnisotropicKernelPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalFlipOnVolumesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalListedTopForms
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links Formalism.L2.DIV GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainHyp

open GlobalTheory.FunObj GlobalTheory.RowChain GlobalTheory.FlipRun GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf

variable {T : Type}

theorem splitFam_zip {S S' S'' : Arrow T → Type} (φ : ∀ a, S a → S' a → S'' a) {X Y : Node} {p : Path T X Y} :
    ∀ {Z : Node} (q : Path T Y Z) (d : (p.comp q).Fam S) (e : (p.comp q).Fam S'),
      splitFam q (Path.Fam.zip φ d e) =
        (Path.Fam.zip φ (splitFam q d).1 (splitFam q e).1, Path.Fam.zip φ (splitFam q d).2 (splitFam q e).2)
  | _, .nil, _, _ => rfl
  | _, .snoc _ q, d, e => by
    show ((splitFam q (Path.Fam.zip φ d.1 e.1)).1, ((splitFam q (Path.Fam.zip φ d.1 e.1)).2, φ _ d.2 e.2)) = _
    rw [splitFam_zip φ q d.1 e.1]
    rfl

theorem getD_zip {S S' S'' : Arrow T → Type} (φ : ∀ a, S a → S' a → S'' a) (t : T) (i : ℕ) :
    ∀ (n : ℕ) (d : (downPath t i n).Fam S) (e : (downPath t i n).Fam S') (j : ℕ) (h : j < n),
      getD t i n (Path.Fam.zip φ d e) j h = φ _ (getD t i n d j h) (getD t i n e j h)
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, d, e, j, h => by
    have hs : splitFam (p := Path.one (.down t i n)) (downPath t i n)
        (Path.Fam.zip (p := downPath t i (n + 1)) φ d e) =
        (Path.Fam.zip φ (splitFam (p := Path.one (.down t i n)) (downPath t i n) d).1
          (splitFam (p := Path.one (.down t i n)) (downPath t i n) e).1,
         Path.Fam.zip φ (splitFam (p := Path.one (.down t i n)) (downPath t i n) d).2
          (splitFam (p := Path.one (.down t i n)) (downPath t i n) e).2) :=
      splitFam_zip φ (p := Path.one (.down t i n)) (downPath t i n) d e
    unfold getD
    split_ifs with hj
    · rw [hs]
      exact getD_zip φ t i n _ _ j hj
    · obtain rfl : n = j := by omega
      rw [hs]
      rfl

variable {D : D7} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem vecAll_iff {W : G.Weil} (ρ : RealMatch W) (e : AE D) {X : Node} :
    ∀ {Y : Node} (p : Path T X Y) (φ f : PureT G p), VecAll ρ e p φ f ↔
      Path.Fam.All (fun a (x : Sch G a × Sch G a) => IsLocVec W a.pair e (vacOf ρ a) x.1 x.2)
        (Path.Fam.zip (fun _ u v => (u, v)) φ f)
  | _, .nil, _, _ => Iff.rfl
  | _, .snoc _ p, φ, f => and_congr_left' (vecAll_iff ρ e p φ.1 f.1)

theorem getD_loc {W : G.Weil} (ρ : RealMatch W) (e : AE D) (t : T) (i n : ℕ) (φ f : PureT G (downPath t i n))
    (h : VecAll ρ e (downPath t i n) φ f) (j : ℕ) (hj : j < n) :
    IsLocVec W (Arrow.down t i j).pair e (vacOf ρ (.down t i j)) (getD t i n φ j hj) (getD t i n f j hj) := by
  have := getD_all (fun a (x : Sch G a × Sch G a) => IsLocVec W a.pair e (vacOf ρ a) x.1 x.2) t i n _
    ((vecAll_iff ρ e _ φ f).1 h) j hj
  rwa [getD_zip] at this

theorem row_cusp {W : G.Weil} {M : Vol G} {ρ : RealMatch W} {t : T} (hS : CuspStep W M ρ t) {e : AE D}
    (he : IsIdemSum e (locPl G t)) {F : Fn G (.grid 0 D.R.m)} (hF : IsCuspListed W.θ (.grid 0 D.R.m) F) :
    ∀ n, n ≤ D.R.m → ∀ (φ d : PureT G (rowPath T D.R.m n)) (P : PolT G (rowPath T D.R.m n)),
      VecAll ρ e (rowPath T D.R.m n) φ d →
      IsCuspListed W.θ (.grid n D.R.m)
        (liftP W M (rowPath T D.R.m n) (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P) F)
  | 0, _, _, _, _, _ => hF
  | n + 1, hn, φ, d, P, h =>
    (hS (.right n D.R.m) (Or.inl ⟨n, D.R.m, by omega, le_rfl, rfl⟩) e he φ.2 d.2 h.2 P.2 _
      (row_cusp hS he hF n (by omega) φ.1 d.1 P.1 h.1)).2

theorem step_cusp (G : GridData L sc) (Wl : G.Weil) (t : T) {M : Vol G} (hM : M.Is t) {θ : InfFam D} (j : ℕ)
    (hj : j + 1 ≤ D.R.m) {V₀ W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec (G.V (.grid D.R.m j)) V₀ ρ)
    (dW : HypDec (G.V (.grid D.R.m (j + 1))) W₀ σ) (Φ : Sch G (.down t D.R.m j)) (F : Fn G (.grid D.R.m (j + 1)))
    (h : IsCuspListed θ (.grid D.R.m j) (liftA Wl M (.down t D.R.m j) Φ F)) :
    IsCuspListed θ (.grid D.R.m j) ((stepAt G Wl t hM j hj dV dW).lift F Φ) := h

end GlobalTheory.ChainHyp

namespace GlobalTheory.ChainHyp

open GlobalTheory.FunObj GlobalTheory.RowChain GlobalTheory.RowUnf GlobalTheory.FlipRun GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf

variable {T : Type} {D : D7} {L : LevCh D T} {sc : Consts}

theorem last_cusp (G : GridData L sc) (Wl : G.Weil) (t : T) (M : Vol G) {θ : InfFam D} (j : ℕ)
    (f : Sch G (.down t D.R.m (j + 1)))
    (H : ∀ F' : Fn G (.grid D.R.m (j + 1 + 1)), IsCuspListed θ (.grid D.R.m (j + 1 + 1)) F' →
      IsCuspListed θ (.grid D.R.m (j + 1)) (liftA Wl M (.down t D.R.m (j + 1)) f F')) :
    ∀ (n : ℕ) (h : j + 1 + 1 = n) (F : Fn G (.grid D.R.m n)), IsCuspListed θ (.grid D.R.m n) F →
      IsCuspListed θ (.grid D.R.m (j + 1))
        (liftS (castOm G h (Wl.om (.mu t D.R.m (j + 1)))) (M.ν (.grid D.R.m n)) (M.fd (.grid D.R.m n)) F (castSch G h f)) := by
  intro n h
  subst h
  exact H

theorem chain_props (hP : GlobalTheory.Published.CuspRapidDecay) (G : GridData L sc) (Wl : G.Weil) (hθ : IsInfFam Wl.θ) (t : T)
    {M : Vol G} (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (F : Fn G (.grid D.R.m D.R.m))
    (hF : IsCuspListed Wl.θ (.grid D.R.m D.R.m) F)
    (hst : ∀ k (hk : k < D.R.m) (F' : Fn G (.grid D.R.m (k + 1))), IsCuspListed Wl.θ (.grid D.R.m (k + 1)) F' →
      IsCuspListed Wl.θ (.grid D.R.m k) (liftA Wl M (.down t D.R.m k) (getD t D.R.m D.R.m d k hk) F')) :
    ∀ (σ j : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (vN : VolN (besDecAt G j σ hj)),
      IsCuspListed Wl.θ (.grid D.R.m j) ((chainFrom G Wl t hM σ j hj vN).down (dataFrom G Wl t hM d σ j hj vN) F) ∧
      (chainFrom G Wl t hM σ j hj vN).Rapid (dataFrom G Wl t hM d σ j hj vN) F
  | 0, j, hj, vN => by
    refine ⟨?_, trivial⟩
    exact step_cusp G Wl t hM j (by omega) (besDecAt G j 0 hj) (rowJac G (j + 1) (by omega) 0 (by omega)) _ _ (hst j (by omega) _
      (last_cusp G Wl t M j _ (hst (j + 1) (by omega)) D.R.m (by omega) F hF))
  | σ + 1, j, hj, vN => by
    obtain ⟨h1, h2⟩ := chain_props hP G Wl hθ t hM d F hF hst σ (j + 1 + 1) (by omega)
      (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    have h3 := step_cusp G Wl t hM (j + 1) (by omega)
      (rowJac G (j + 1) (by omega) (σ + 1) (by omega)) (besDecAt G (j + 1 + 1) σ (by omega))
      (getD t D.R.m D.R.m d (j + 1) (by omega)) _ (hst (j + 1) (by omega) _ h1)
    refine ⟨step_cusp G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)) _ _
      (hst j (by omega) _ h3), ?_⟩
    exact ⟨rapidDec_of_cuspForm hP hθ h3.1 h3.2.1, rapidDec_of_cuspForm hP hθ h1.1 h1.2.1, h2⟩

end GlobalTheory.ChainHyp

namespace GlobalTheory.ChainHyp

open GlobalTheory.FunObj GlobalTheory.RowChain GlobalTheory.FlipRun GlobalTheory.Grow

end GlobalTheory.ChainHyp

end
