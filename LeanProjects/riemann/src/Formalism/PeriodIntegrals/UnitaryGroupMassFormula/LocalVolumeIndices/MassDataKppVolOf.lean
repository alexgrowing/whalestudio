import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst

noncomputable section

namespace PI.MassDataKppVolLemmas

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped ENNReal

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

abbrev lamS : Set (Fin X.B.I.n → X.B.I.E) := (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))

abbrev KfS : Subgroup (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := Kf X.B.I.cm.sig X.B.I.J (lamS X)

def KppS : Subgroup (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := Subgroup.closure (levelUnitary X hb)

def gIdx : ℕ := (KppS X hb).relIndex (KfS X)

def KvS (p : TypX X) : Subgroup (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) :=
  Subgroup.closure (Kv X.B.I.cm.sig X.B.I.J (lamS X) p.1)

def KppvS (p : TypX X) : Subgroup (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) :=
  Subgroup.closure (compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1)

def lIdx (p : TypX X) : ℕ := (KppvS X hb p).relIndex (KvS X p)

def GlobIdx : Prop :=
  gIdx X hb ≠ 0 → X.measG.μGf (KfS X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) =
    (gIdx X hb : ℝ≥0∞) * X.measG.μGf (levelUnitary X hb)

def LocIdx : Prop :=
  ∀ p : TypX X, lIdx X hb p ≠ 0 → X.measG.μGv p.1 (Kv X.B.I.cm.sig X.B.I.J (lamS X) p.1) =
    (lIdx X hb p : ℝ≥0∞) * X.measG.μGv p.1 (compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1)

def LocPos : Prop :=
  ∀ p : TypX X, 0 < X.measG.μGv p.1 (compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1) ∧
    X.measG.μGv p.1 (compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1) < ⊤ ∧ lIdx X hb p ≠ 0

def IdxProd : Prop := gIdx X hb = ∏ p : TypX X, lIdx X hb p

def GlobIdxAll : Prop := ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb →
  X.LevelSubgroupNormalized → GlobIdx X hb
def LocIdxAll : Prop := ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb →
  X.LevelSubgroupNormalized → LocIdx X hb
def LocPosAll : Prop := ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb →
  X.LevelSubgroupNormalized → LocPos X hb
def IdxProdAll : Prop := ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb →
  X.LevelSubgroupNormalized → IdxProd X hb

theorem Steps_bOf_μKpp (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : LocIn (TypX X)) (A : AnIn) :
    (bOf X hb hK FdN FdN' u u' X0 L A).μKpp =
      (X.measG.μGf (KfS X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))).toReal /
        (∏ p : TypX X, (X.measG.μGv p.1 (Kv X.B.I.cm.sig X.B.I.J (lamS X) p.1)).toReal) *
        ∏ p : TypX X, (X.measG.μGv p.1 (compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1)).toReal := rfl

theorem Steps_main (h1 : GlobIdx X hb) (h2 : LocIdx X hb) (h3 : LocPos X hb) (h4 : IdxProd X hb) :
    (X.measG.μGf (KfS X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))).toReal /
        (∏ p : TypX X, (X.measG.μGv p.1 (Kv X.B.I.cm.sig X.B.I.J (lamS X) p.1)).toReal) *
        ∏ p : TypX X, (X.measG.μGv p.1 (compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1)).toReal =
      (X.measG.μGf (levelUnitary X hb)).toReal := by
  have hne : ∀ p : TypX X,
      (X.measG.μGv p.1 (compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1)).toReal ≠ 0 := fun p =>
    (ENNReal.toReal_pos (h3 p).1.ne' (h3 p).2.1.ne).ne'
  have hg : gIdx X hb ≠ 0 := by
    rw [h4]
    exact Finset.prod_ne_zero_iff.mpr fun p _ => (h3 p).2.2
  have hprod : ∏ p : TypX X, (X.measG.μGv p.1 (Kv X.B.I.cm.sig X.B.I.J (lamS X) p.1)).toReal =
      (gIdx X hb : ℝ) *
        ∏ p : TypX X, (X.measG.μGv p.1 (compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1)).toReal := by
    rw [h4, Nat.cast_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [h2 p (h3 p).2.2, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hP : ∏ p : TypX X,
      (X.measG.μGv p.1 (compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1)).toReal ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p _ => hne p
  have hG : (gIdx X hb : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hg
  rw [hprod, h1 hg, ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_div_mul_left _ _ hG,
    div_mul_cancel₀ _ hP]

theorem massDataKppVol_of (h1 : GlobIdxAll) (h2 : LocIdxAll) (h3 : LocPosAll) (h4 : IdxProdAll) :
    ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
      (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : LocIn (TypX X))
      (A : AnIn), KppVolAt X hb hK FdN FdN' u u' X0 L A := by
  intro D X hb hK FdN FdN' u u' X0 L A hyp
  rw [Steps_bOf_μKpp X hb hK FdN FdN' u u' X0 L A]
  exact Steps_main X hb (h1 X hb hK hyp.1 hyp.2.1) (h2 X hb hK hyp.1 hyp.2.1)
    (h3 X hb hK hyp.1 hyp.2.1) (h4 X hb hK hyp.1 hyp.2.1)

end PI.MassDataKppVolLemmas
