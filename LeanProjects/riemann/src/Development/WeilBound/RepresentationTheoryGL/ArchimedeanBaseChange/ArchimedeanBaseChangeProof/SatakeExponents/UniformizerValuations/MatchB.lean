import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameL
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchT

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.MB

open PositivityTheory.Rg.BcB.F.U (lpow lone)
open PositivityTheory.Rg.BcN.F2 (mconv)
open PositivityTheory.Rg.BcB.F.MT (MatchLin)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def congK (m : ℕ) (w : Pl E) (k : ℕ) : Set (GLw m w) :=
  {g | g ∈ GlobalTheory.LFun.KGL w m ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤
    WithZero.exp (-(k : ℤ))}

def pairIndicatorMatch (_n a b : ℕ) (w : Pl E) (k : ℕ) (y : GLw a w × GLw b w) : ℂ :=
  ((-((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ^ (k * a * b))⁻¹ *
    (if y.1 ∈ GlobalTheory.LFun.KGL w a ∧ nrmL a w y.1 ∈ congK a w k ∧ y.2 ∈ GlobalTheory.LFun.KGL w b ∧ nrmL b w y.2 ∈ congK b w k then 1
      else 0)

def LponeIdem : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (K' : Subgroup (UL n w)),
    IsLevel (MonoidHom.id _) (KL n w) K' → ∀ m : ℕ, lpow K' (lone K') m = lone K'

def FixIdem : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (L : Subgroup (GLw a w × GLw b w)),
    IsOpen (L : Set (GLw a w × GLw b w)) → L ≤ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) →
    ∀ φ : GLw a w × GLw b w → ℂ, IsHecke L φ → mconv φ (idem L) = φ ∧ mconv (idem L) φ = φ

def MatchBadS : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a : ℕ) (ha : a ≤ n) (w : Pl E), IsSplitAt w →
    ∀ (μ : (w.adicCompletion E)ˣ →* ℂˣ) (K' : Subgroup (UL n w)), IsLevel (MonoidHom.id _) (KL n w) K' → ∀ m : ℕ,
      Match n a (n - a) w μ (lpow K' (lone K') m) (ctMu (Nat.add_sub_cancel' ha) w μ (lone K'))

def MatchBadI : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : Pl E, ¬ IsSplitAt w → ∀ (n a b k : ℕ), a + b = n →
    1 ≤ k → ∀ K' : Subgroup (UL n w), IsLevel (MonoidHom.id _) (KL n w) K' → (∀ γ : UL n w, γ ∈ K' ↔ γ.1 ∈ congK n w k) →
      ∀ m : ℕ, Match n a b w 1 (lpow K' (lone K') m) (fun y => ((K'.relIndex (KL n w) : ℕ) : ℂ) * pairIndicatorMatch n a b w k y)

def MatchUnitI : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : Pl E, ¬ IsSplitAt w → ∀ n a : ℕ, a ≤ n →
    Match n a (n - a) w 1 ((KL n w : Set (UL n w)).indicator 1) (idem (K2 a (n - a) w))

def MatchBadSOf : Prop := M3 → LponeIdem → MatchBadS
def MatchBadIOf : Prop := M2 → LponeIdem → MatchLin → MatchBadI
def MatchUnitIOf : Prop := M1 → MatchUnitI

end PositivityTheory.Rg.BcB.F.MB

end
