import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.CntLocal
import Formalism.SharpRestriction.CuspSpanNormBounds.FrameFixingOrbitRelation
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial

noncomputable section

open scoped Classical

namespace PI.PairValDefs

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Phase

variable {E : Type} [Field E] [NumberField E]

def psiInf (g : ℕ) (x : E) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ E x : ℚ) : ℂ) / (g : ℂ)))

def sgUp {N : ℕ} (U : Matrix (Fin N) (Fin N) E) : E :=
  ∑ a : Fin N, if h : a.val + 1 < N then U a ⟨a.val + 1, h⟩ else 0

def sgLo {N : ℕ} (L : Matrix (Fin N) (Fin N) E) : E :=
  ∑ a : Fin N, if h : a.val + 1 < N then L ⟨a.val + 1, h⟩ a else 0

end Phase

section Coef

variable {D : D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

abbrev MatR (D : D7) : Type := Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E

def NormRep (t : Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : MatR D) : Prop :=
  Rep t.lam (lf D F0) (PD D t.lam (lf D F0) u') t.cls F' ∧ AdmWit t.lam (gS D) (lf D F0) F' 1 ∧
    IsLoUni L ∧ IsUpUni U ∧ ZhatOM (ZhatL (lf D F0) F') = L * ptMat w * U

def BigCell {i : ℕ} (w : Point D.host.E i) : Prop := ∀ b ∈ w.1, b.2 = 1

variable (D u u' F0 what₂)

def orbT (t : Term D u u' F0 what₂) (Z : MatR D) : Set (Set (LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))) :=
  {O | ∃ F' ∈ Formalism.L2.SG.CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 t.lam Z,
    Rep t.lam (lf D F0) (PD D t.lam (lf D F0) u') t.cls F' ∧
    O = {F'' | F'' ∈ Formalism.L2.SG.CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 t.lam Z ∧ Formalism.L2.SG.CntLocal.NilradicalFlagMoved F0 t.lam F' F''}}

end Coef

section VolDef

variable {D : D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (D u u' F0 what₂)

abbrev GLR (D : D7) : Type := Matrix.GeneralLinearGroup (Fin (D.R.rS + 1)) D.host.E

def stabIntSet (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (w : Point D.host.E (D.R.rS + 1)) : Set (GLR D) :=
  {a | IsLoUni (a : MatR D) ∧ ∃ b : MatR D, IsUpUni b ∧ (a : MatR D) * ptMat w * b = ptMat w ∧
    ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, ∃ l ρ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep,
      Formalism.MainNotions.S.TieN.IntLow (M p) l ∧ Formalism.MainNotions.S.TieN.IntUp (M p) ρ ∧
      ∀ Z : MatR D, Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatOM ((a : MatR D) * ZhatOM Z * b)) =
        l * Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p Z * ρ}

def stabInt (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (w : Point D.host.E (D.R.rS + 1)) : Subgroup (GLR D) :=
  Subgroup.closure (stabIntSet D u u' δ M w)

def stabAutSet (t : Term D u u' F0 what₂) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L : MatR D) :
    Set (GLR D) :=
  {a | ∃ s ∈ NLam t.lam (lf D F0) ∩ NLam t.lam F', ∃ uu : MatR D,
    (∀ b, s (frame (lf D F0) b) = ∑ c, uu c b • frame (lf D F0) c) ∧ (a : MatR D) = L⁻¹ * uu.conjTranspose * L}

def stabAut (t : Term D u u' F0 what₂) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L : MatR D) :
    Subgroup (GLR D) :=
  Subgroup.closure (stabAutSet D u u' F0 what₂ t F' L)

def volIdx (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (t : Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L : MatR D) : ℝ :=
  ((stabAut D u u' F0 what₂ t F' L).relIndex (stabInt D u u' δ M w) : ℝ) /
    ((stabInt D u u' δ M w).relIndex (stabAut D u u' F0 what₂ t F' L) : ℝ)

def vRdef (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (t : Term D u u' F0 what₂) : ℝ :=
  if h : t.relevant ∧ t.generic ∧
      ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × MatR D × MatR D,
        NormRep t x.1 x.2.1 x.2.2.1 x.2.2.2 then
    volIdx D u u' F0 what₂ δ M t h.2.2.choose.1 h.2.2.choose.2.1 h.2.2.choose.2.2.1
  else 1

end VolDef

end PI.PairValDefs
