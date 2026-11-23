import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IndexCocycleOrbits.VolumeOrbitNonzero

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.IndexCocycleOrbits

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IdxRatio {G : Type} [Group G] (A B : Subgroup G) : ℝ :=
  (B.relIndex A : ℝ) / (A.relIndex B : ℝ)

def IdxCocycle : Prop :=
  ∀ (G : Type) [Group G] (A B C : Subgroup G), B ≤ C → B.relIndex C ≠ 0 →
    IdxRatio A B = (B.relIndex C : ℝ) * IdxRatio A C

def CellUniq : Prop :=
  ∀ (K : Type) [Field K] (N : ℕ) (X : Matrix (Fin N) (Fin N) K) (w₁ w₂ : Point K N),
    IsInCell X w₁ → IsInCell X w₂ → ptMat w₁ = ptMat w₂

abbrev LF (D : D7) (u' : D.what₂.Word) : Type := LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)

abbrev PtR (D : D7) : Type := Point D.host.E (D.R.rS + 1)

section Data

variable {D : D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def NDataG (t : Term D u u' F0 what₂) (w : PtR D) (F' : LF D u') (L U : MatR D) : Prop :=
  t.relevant ∧ t.generic ∧ NormRep t w F' L U ∧ Gval (lf D F0) F' ≠ 0

end Data

variable (D : D7) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def VolIdxRep : Prop :=
  ∀ (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p) → ∀ (t : Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
      (F₁ F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L₁ U₁ L₂ U₂ : MatR D),
      t.relevant → t.generic → NormRep t w F₁ L₁ U₁ → Gval (lf D F0) F₁ ≠ 0 → NormRep t w F₂ L₂ U₂ →
        Gval (lf D F0) F₂ ≠ 0 → volIdx D u u' F0 what₂ δ M t w F₁ L₁ = volIdx D u u' F0 what₂ δ M t w F₂ L₂

def VolIdxFin1 (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) : Prop :=
  (∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p) → ∀ (t : Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : MatR D),
    t.relevant → t.generic → NormRep t w F' L U →
      (stabAut D u u' F0 what₂ t F' L).relIndex (stabInt D u u' δ M w) ≠ 0 ∧
      (stabInt D u u' δ M w).relIndex (stabAut D u u' F0 what₂ t F' L) ≠ 0

def OrbFin : Prop :=
  ∀ (t : Term D u u' F0 what₂) (w : PtR D) (F' : LF D u') (L U : MatR D),
    NDataG t w F' L U → (orbT D u u' F0 what₂ t (ZhatL (lf D F0) F')).Finite

def OrbStab (C : Term D u u' F0 what₂ → LF D u' → MatR D → Subgroup (GLR D)) : Prop :=
  ∀ (t : Term D u u' F0 what₂) (w : PtR D) (F' : LF D u') (L U : MatR D),
    NDataG t w F' L U → stabAut D u u' F0 what₂ t F' L ≤ C t F' L ∧
      (stabAut D u u' F0 what₂ t F' L).relIndex (C t F' L) = (orbT D u u' F0 what₂ t (ZhatL (lf D F0) F')).ncard

def WtIndep (C : Term D u u' F0 what₂ → LF D u' → MatR D → Subgroup (GLR D))
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) : Prop :=
  ∀ (t₁ : Term D u u' F0 what₂) (w₁ : PtR D) (F₁ : LF D u') (L₁ U₁ : MatR D)
    (t₂ : Term D u u' F0 what₂) (w₂ : PtR D) (F₂ : LF D u') (L₂ U₂ : MatR D),
    NDataG t₁ w₁ F₁ L₁ U₁ → NDataG t₂ w₂ F₂ L₂ U₂ → ZhatL (lf D F0) F₁ = ZhatL (lf D F0) F₂ →
      IdxRatio (stabInt D u u' δ M w₁) (C t₁ F₁ L₁) = IdxRatio (stabInt D u u' δ M w₂) (C t₂ F₂ L₂)

def OrbStabZ (C : MatR D → MatR D → Subgroup (GLR D)) : Prop :=
  ∀ (t : Term D u u' F0 what₂) (w : PtR D) (F' : LF D u') (L U : MatR D),
    NDataG t w F' L U → stabAut D u u' F0 what₂ t F' L ≤ C (ZhatL (lf D F0) F') L ∧
      (stabAut D u u' F0 what₂ t F' L).relIndex (C (ZhatL (lf D F0) F') L) =
        (orbT D u u' F0 what₂ t (ZhatL (lf D F0) F')).ncard

end Formalism.L2.SG.Pf.IndexCocycleOrbits
