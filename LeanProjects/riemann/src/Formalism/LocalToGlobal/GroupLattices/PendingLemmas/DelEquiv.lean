import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.SubstZOfXCoordZA
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.DetYtMatNeZero
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.DetOfColSpanEq
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WeightUpdateAtPlace

noncomputable section

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def glAt : (j : ℕ) → (∀ v : Fin (X.Fl.Pj j).nV, GL (Fin ((X.Fl.Pj j).m + 1)) ((X.Fl.Pj j).Qq v)) →
    ∀ v : X.Pl, GL (Fin ((X.Fl.Pj j).m + 1)) (X.G.P.Qq v)
  | 0, A => A
  | _ + 1, A => A

variable (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc]

def actS (j : ℕ) (B : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) : X.ZA j → MvPowerSeries (X.ZA j) Kc
  | ⟨v, (s, a, b)⟩ => ∑ a' : Fin (NN X.G.P.m X.t j),
      MvPowerSeries.C (if IsOddPos s then mAt X Kc j v s ((B v)⁻¹ : GL _ _) a a' else mAt X Kc j v s (B v) a' a) *
        MvPowerSeries.X ⟨v, (s, a', b)⟩

def SA (j : ℕ) (B : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) (f : MvPowerSeries (X.ZA j) Kc) :
    MvPowerSeries (X.ZA j) Kc :=
  MvPowerSeries.subst (actS X Kc j B) f

def cA (j : ℕ) (B : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) : Kc :=
  ∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v),
    (tw X Kc v s (B v : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det) ^ ((if IsOddPos s then -1 else 1) * X.w v (j + 1) s)

def GoodG (j : ℕ) (G : (X.Pj j).Xsp) : Prop := denD X Kc j ∣ subD X Kc j G * numD X Kc j

def DelEquiv : Prop :=
  ∀ (j : ℕ) (A : ∀ v : Fin (X.Pj j).nV, GL (Fin ((X.Pj j).m + 1)) ((X.Pj j).Qq v)) (G : (X.Pj j).Xsp)
    (f : MvPowerSeries (X.ZA j) Kc), GoodG X Kc j G →
    GoodG X Kc j ((X.Pj j).natAct A G) ∧
    delF X Kc j ((X.Pj j).natAct A G) (SA X Kc j (glAt X j A) f) = cA X Kc j (glAt X j A) • delF X Kc j G f

def gamAt (j : ℕ) (c : X.Lv.comp j) (γ : (X.Lv.lev j c).Γ) : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) :=
  glAt X j fun v => (X.Lv.lev j c).act v γ

def kapG (j : ℕ) (c : X.Lv.comp j) (γ : (X.Lv.lev j c).Γ) : Kc :=
  algebraMap X.G.Kf Kc (algebraMap X.G.O X.G.Kf (((X.Lv.lev j c).χ γ : X.G.Oˣ) : X.G.O)) * cA X Kc j (gamAt X j c γ) *
    ∏ v : X.Pl, (p : Kc) ^ (-(X.vm v (j + 1) * ordP (X.G.P.W v) p (gamAt X j c γ v : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det))

variable (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)

def delt (j : ℕ) (c : X.Lv.comp j) (L : (X.Pj j).Tup) : (X.Lv.lev j c).Γ := by
  classical exact if h : (X.Pj j).IsLatTup L then (Classical.choose_spec (repOf_ex X.Lv hfin j c L h).exists).2.choose else 1

def chiN (j : ℕ) (La : X.Lt j) : Kc := (kapG X Kc j La.1 (delt X hfin j La.1 La.2))⁻¹

def thFN (Th0 : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Kc) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) :
    MvPowerSeries (X.ZA j) Kc :=
  MvPowerSeries.C (chiN X Kc hfin j La) * Th0 j La La'

def GeoLaw (Th0 : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Kc) : Prop :=
  ∀ j (c : X.Lv.comp j) (L : (X.Pj j).Tup) (La' : X.Lt (j + 1)) (γ : (X.Lv.lev j c).Γ), (X.Pj j).IsLatTup L →
    Th0 j (c, (X.Lv.lev j c).smul γ L) La' = SA X Kc j (gamAt X j c γ) (Th0 j (c, L) La')

def KapStab : Prop :=
  ∀ j (c : X.Lv.comp j) (L : (X.Pj j).Tup) (γ : (X.Lv.lev j c).Γ), (X.Pj j).IsLatTup L →
    (X.Lv.lev j c).smul γ L = L → kapG X Kc j c γ = 1

end Formalism.L2.G.Pend
