import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilDatumAnisotropicKernelPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) {M : Vol G}

abbrev pLine (D : D7) : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1

theorem pLine_gram : (pLine D).gram = antiDiagonalSignGramMatrix 1 (1 : D.host.E) := by
  refine Matrix.ext fun i j => ?_
  have e : ∀ a b : Fin 1, (Examples₂.stdSpace (E := D.host.E) Examples₂.star_isIntegral 1 (fun _ => false) 1 0).gram a b = 1 :=
    fun a b => by rw [Examples₂.stdSpace_gram_apply, Subsingleton.elim a b]; simp [Examples₂.sgn]
  exact (e i j).trans (by simp [antiDiagonalSignGramMatrix]; exact ⟨Fin.val_eq_zero i, Fin.val_eq_zero j⟩)

def topOrth : OrthDec (G.V (.top D.R.m)) (G.V (.grid D.R.m D.R.m)) (pLine D) where
  iA := frameMat _ _ G.sp.topDec.ι
  iB := G.sp.topDec.a
  isoA := frameMat_isom G.sp.topDec
  isoB := G.sp.topDec.gram.trans pLine_gram.symm
  orth := perp_sub' G.sp.topDec id
  rank_add := G.sp.topDec.rank

def topOrthAt {n : ℕ} (h : D.R.m = n) : OrthDec (G.V (.top n)) (G.V (.grid D.R.m D.R.m)) (pLine D) :=
  Eq.rec (motive := fun k _ => OrthDec (G.V (.top k)) (G.V (.grid D.R.m D.R.m)) (pLine D)) (topOrth G) h

def topEmb {n : ℕ} (h : D.R.m = n) : GA D (G.V (.grid D.R.m D.R.m)) → GA D (G.V (.top n)) :=
  Eq.rec (motive := fun k _ => GA D (G.V (.grid D.R.m D.R.m)) → GA D (G.V (.top k))) (stabilizerEmbedding G.sp.topDec) h

def lastTau : Matrix (Fin (GlobalTheory.SeeSaw.Model.nLine D).rank) (Fin (pLine D).rank) D.host.E := Matrix.of fun _ _ => -D.host.xi0

variable {G t}

def lastDat (hM : M.Is t) (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) (vN : VolN (besDecAt G j 0 hj)) (g : GA D (G.V (.grid D.R.m j)))
    (Φ₁ : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (Φ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m D.R.m)) → ℂ) :
    WO (G.V (.top j)) (G.V (.top (j + 1))) → WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) → ℂ :=
  GlobalTheory.FinPl.lastBi (besAt G hM j 0 hj vN).o (topOrthAt G (show D.R.m = j + 1 + 1 by omega)) lastTau
    (flatBF (lastAt G Wl t hM j hj vN).s ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁))
    (fun w => Φ₂ ((rowJac G (j + 1) (by omega) 0 (by omega)).ext0 _ w))

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) {M : Vol G}

theorem topOrth_emb (h : GA D (G.V (.grid D.R.m D.R.m))) : (topOrth G).emb (h, 1) = stabilizerEmbedding G.sp.topDec h :=
  (embRel_iff G.sp.topDec h _).1 ((topOrth G).embRel_left G.sp.topDec.ι rfl h)

variable {G t}

noncomputable def colPer (hM : M.Is t) : (σ j : ℕ) → (hj : j + 2 * σ + 2 = D.R.m) → (vN : VolN (besDecAt G j σ hj)) →
    (chainFrom G Wl t hM σ j hj vN).Data → Fn G (.grid D.R.m D.R.m) → (GA D (G.V (.top j)) → ℂ) →
    GA D (G.V (.grid D.R.m j)) → (chainFrom G Wl t hM σ j hj vN).Var → ℂ
  | 0, j, hj, vN, Φ, F, φ, g, _ =>
    ∫ h' in M.fd (.grid D.R.m D.R.m), F h' * GlobalTheory.SeeSaw.biLift (Wl.om (.top t j)) (Wl.om (.top t (j + 1)))
      (volAt hM (.top j) (by show j ≤ D.R.m; omega)) (volAt hM (.top (j + 1)) (by show j + 1 ≤ D.R.m; omega)) φ
      (lastDat Wl hM j hj vN g Φ.1 Φ.2) (topEmb G (show D.R.m = j + 1 + 1 by omega) h') ∂M.ν (.grid D.R.m D.R.m)
  | σ + 1, j, hj, vN, Φ, F, φ, g, h =>
    colPer hM σ (j + 1 + 1) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some Φ.2.2 F
      (GlobalTheory.SeeSaw.biLift (Wl.om (.top t j)) (Wl.om (.top t (j + 1)))
        (volAt hM (.top j) (by show j ≤ D.R.m; omega)) (volAt hM (.top (j + 1)) (by show j + 1 ≤ D.R.m; omega)) φ
        (contr (linkAt hM j σ hj vN (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) (G.V (.top (j + 1)))
          ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some)
          (flatBF (B := besAt G hM j (σ + 1) hj vN) (J := jacAt G hM (j + 1) (σ + 1) (by omega)) (stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)))
            ((stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))).om
              (g, h.1) Φ.1))
          (flatFB (J := jacAt G hM (j + 1) (σ + 1) (by omega))
            (B := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) (stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
              (besDecAt G (j + 1 + 1) σ (by omega)))
            ((stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
              (besDecAt G (j + 1 + 1) σ (by omega))).om (h.1, h.2.1) Φ.2.1))))
      h.2.1 h.2.2

end GlobalTheory.RowChain
