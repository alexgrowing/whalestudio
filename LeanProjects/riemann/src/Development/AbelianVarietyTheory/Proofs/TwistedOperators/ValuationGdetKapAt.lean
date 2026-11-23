import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdPartialEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopLevelInv

section Local

variable {k : Type} [Field k]

def colMove {G : Grid k} (j : ℕ) (κ : GL (Fin (topRank G (j + 1))) k) (x : ColArgs G) : ColArgs G :=
  Function.update (Function.update x j ((κ⁻¹).val * x j)) (j + 1) (x (j + 1) * κ.val)

open Classical in

def stepVol [MeasurableSpace k] (ν : Measure k) (n : Type) [Fintype n] (c : ℕ) (n' : Type) [Fintype n'] :
    Measure (StepVar n c n' → k) := Measure.pi fun _ => ν

theorem varsVol_eq [MeasurableSpace k] (G : Grid k) (ν : Measure k) :
    varsVol G ν = Measure.pi fun j : Fin (G.m - 1) => stepVol ν (Fin (topRank G (j + 1))) (G.m - 2 - j) (Fin (topRank G j)) := rfl

variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem gdet_of_mem_N {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) : gdet g = 1 := by
  refine (show N k n c p ≤ (Matrix.GeneralLinearGroup.det (n := n ⊕ Fin c) (R := k)).ker from
    (Subgroup.closure_le _).2 fun g hg => ?_) hg
  apply Units.ext
  change g.val.det = 1
  rw [(GlobalTheory.RootEx.Model.inN_tri hg).det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : g.val.toSquareBlock (lev p) a = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply]
    rw [hg i j (by rw [hi, hj]), Matrix.one_apply, Matrix.one_apply]
    simp [Subtype.ext_iff]
  rw [this, det_one]

theorem gdet_of_mem_symN {g : GL (n ⊕ Fin c) k} (hg : g ∈ symN k n c) : gdet g = 1 :=
  (show symN k n c ≤ (Matrix.GeneralLinearGroup.det (n := n ⊕ Fin c) (R := k)).ker from
    sup_le (fun _ h => gdet_of_mem_N h) fun _ h => gdet_of_mem_N h) hg

theorem gdet_embX (g : GL n k) : gdet (embX c g) = gdet g :=
  Units.ext (by
    change (fromBlocks g.val 0 0 (1 : Matrix (Fin c) (Fin c) k)).det = g.val.det
    rw [det_fromBlocks_zero₂₁, det_one, mul_one])

theorem gdet_toFrame {G : Grid k} (hs : 1 ≤ G.s) {j : ℕ} (hj : j < G.m) (g : GL (Fin (G.rank (G.m, j))) k) :
    gdet (toFrame hs hj g) = gdet g :=
  Units.ext (det_submatrix_equiv_self _ _)

theorem exists_of_mem_symPr {G : Grid k} (hs : 1 ≤ G.s) {J : G.Level} {g : G.VertexGroup} {j : ℕ} (hj : j < G.m)
    {κ : GL (Fin (topRank G j)) k} (hκ : κ ∈ symPr (conjLevel hs J g hj)) :
    ∃ u ∈ J (G.m, j), ∃ v ∈ symN k (Fin (topRank G j)) (G.m - 1 - j),
      toFrame hs hj (g (G.m, j) * u * (g (G.m, j))⁻¹) = v * embX _ κ ∧ gdet κ = gdet u := by
  obtain ⟨v, hv, _, ⟨u, hu, rfl⟩, h⟩ := hκ
  refine ⟨u, hu, v, hv, h, ?_⟩
  have := congrArg gdet h
  rw [gdet_mul, gdet_of_mem_symN hv, one_mul, gdet_embX] at this
  rw [← this]
  change gdet (toFrame hs hj (g (G.m, j) * u * (g (G.m, j))⁻¹)) = _
  rw [gdet_toFrame, gdet_mul, gdet_mul, mul_right_comm, ← gdet_mul, mul_inv_cancel]
  simp

end Local

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def movedPt (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (g : FinPt G (.top (j + 1)))
    (x : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T))) :
    ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)) :=
  Function.update (Function.update x ⟨j, by omega⟩ (actO _ _ 1⁻¹ (g : GA D (G.V (.top (j + 1))))⁻¹ (x ⟨j, by omega⟩)))
    ⟨j + 1, hj⟩ (actO _ _ (g : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ (x ⟨j + 1, hj⟩))

theorem movedFn_apply (S : GridChoice W U) {t : T} (d : PureDat G t) (j : ℕ) (hj : j + 1 < D.R.m) (g : FinPt G (.top (j + 1)))
    (x : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T))) (j' : Fin D.R.m) :
    movedFn S d j hj g j' (x j') = (d.1 j').fn (movedPt t j hj g x j') := by
  rcases eq_or_ne j' ⟨j + 1, hj⟩ with rfl | h1
  · simp only [movedFn, movedPt, Function.update_self]
  rcases eq_or_ne j' ⟨j, by omega⟩ with rfl | h2
  · simp only [movedFn, movedPt, Function.update_of_ne h1, Function.update_self]
  · simp only [movedFn, movedPt, Function.update_of_ne h1, Function.update_of_ne h2]

def kapAt (S : GridChoice W U) (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))) (w : Pl D.host.E) :
    GL (Fin (topRank (locGrid G t w) (j + 1))) (Kw w) :=
  inBasis (topRank_eq G t w hj.le) (S.βp (j + 1)) w (finG (G.V (.top (j + 1))) k)

theorem kapAt_mem (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {j : ℕ} (hj : j + 1 < D.R.m)
    {k : FinPt G (.top (j + 1))} (hk : finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj) (w : locPl G t) :
    kapAt S t j hj k w ∈ (S.term t Φ β w).pr (j + 1) j.succ_pos hj :=
  Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hk).1 w

theorem givenLevel_col (t : T) (w : Pl D.host.E) (j : ℕ) : givenLevel G t w (D.R.m, j + 1) = KO (Kw w) _ := by
  have key : ∀ i, 0 < i → givenLevel G t w (i, j + 1) = KO (Kw w) _ := by
    rintro (_ | i) h
    · omega
    · rfl
  exact key _ (by have := D.R.two_le_m; omega)

theorem valuation_gdet_kapAt (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {j : ℕ} (hj : j + 1 < D.R.m)
    {k : FinPt G (.top (j + 1))} (hk : finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj) (w : locPl G t) :
    valuation (Kw w.1) (gdet (kapAt S t j hj k w) : Kw w.1) = 1 := by
  obtain ⟨u, hu, -, -, -, h⟩ := exists_of_mem_symPr (G := locGrid G t w) one_le_sLen hj (kapAt_mem S hj hk w)
  rw [h]
  exact valuation_gdet_of_mem_KO (givenLevel_col t w.1 j ▸ hu)

end GlobalTheory.TopLevelInv

end
