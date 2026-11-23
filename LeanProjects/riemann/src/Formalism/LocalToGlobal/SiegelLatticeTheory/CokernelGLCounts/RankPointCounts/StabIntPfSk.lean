import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StabLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.AtNormRep
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfGrp

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.Pf.StabIntSh

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

abbrev FI : Type := FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E

def qq : Ideal (𝓞 D.host.E) := Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)}

def ddPow (k : ℕ) : FI D := ddS D ^ (-(k : ℤ))

def qdPow (k : ℕ) : FI D := (qq D : FI D) * ddPow D k

def bt (b : MatR D) (i j : Fin (D.R.rS + 1)) : D.host.E :=
  (-1) ^ (D.R.rS - i.val) * b i j * (-1) ^ (D.R.rS - j.val)

def EntryShape (a b : MatR D) : Prop :=
  ∀ i j : Fin (D.R.rS + 1), j < i →
    a i j ∈ ddPow D (i.val - j.val) ∧ bt D b j i ∈ ddPow D (i.val - j.val) ∧
      a i j - D.conjF (bt D b j i) ∈ qdPow D (i.val - j.val)

def LocMem (p : PlF D) (I : FI D) (x : D.host.E) : Prop :=
  (D.s.atP p).ιE x ∈ Submodule.span (D.s.atP p).O ((D.s.atP p).ιE '' (I : Set D.host.E))

def LocEntryShape (p : PlF D) (a b : MatR D) : Prop :=
  ∀ i j : Fin (D.R.rS + 1), j < i →
    LocMem D p (ddPow D (i.val - j.val)) (a i j) ∧ LocMem D p (ddPow D (i.val - j.val)) (bt D b j i) ∧
      LocMem D p (qdPow D (i.val - j.val)) (a i j - D.conjF (bt D b j i))

def LocShapeL : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D),
    (∀ q, Agree δ M q) → (M p).split = none → ∀ a b : MatR D, IsLoUni a → IsUpUni b →
      (Formalism.MainNotions.S.TieN.IntLow (M p) (StabShape.lOf δ M p a b) ∧ Formalism.MainNotions.S.TieN.IntUp (M p) (StabShape.ρOf δ M p a b) ↔
        LocEntryShape D p a b)

def LocShapeG : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D),
    (∀ q, Agree δ M q) → (M p).split.isSome → ∀ a b : MatR D, IsLoUni a → IsUpUni b →
      (Formalism.MainNotions.S.TieN.IntLow (M p) (StabShape.lOf δ M p a b) ∧ Formalism.MainNotions.S.TieN.IntUp (M p) (StabShape.ρOf δ M p a b) ↔
        LocEntryShape D p a b)

def LocGlob : Prop :=
  ∀ I : FI D, I ≠ 0 → ∀ x : D.host.E, (∀ p, LocMem D p I x) ↔ x ∈ I

def ShapeNZ : Prop := (∀ k, ddPow D k ≠ 0) ∧ ∀ k, qdPow D k ≠ 0

def StabIntShapeC : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (a : GLR D),
      a ∈ stabInt D u u' δ M w ↔ IsLoUni (a : MatR D) ∧ ∃ b : MatR D, IsUpUni b ∧
        (a : MatR D) * ptMat w * b = ptMat w ∧ EntryShape D a (b)

variable {D}

theorem loc_iff (hL : LocShapeL D) (hG : LocShapeG D) {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {p : PlF D} (hA : ∀ q, Agree δ M q) {a b : MatR D}
    (ha : IsLoUni a) (hb : IsUpUni b) :
    (Formalism.MainNotions.S.TieN.IntLow (M p) (StabShape.lOf δ M p a b) ∧ Formalism.MainNotions.S.TieN.IntUp (M p) (StabShape.ρOf δ M p a b) ↔
      LocEntryShape D p a b) := by
  cases h : (M p).split with
  | none => exact hL δ M p hA h a b ha hb
  | some g => exact hG δ M p hA (by simp [h]) a b ha hb

theorem glob_iff (hLG : LocGlob D) (hNZ : ShapeNZ D) (a b : MatR D) :
    (∀ p, LocEntryShape D p a b) ↔ EntryShape D a b := by
  constructor
  · intro h i j hij
    exact ⟨(hLG _ (hNZ.1 _) _).1 fun p => (h p i j hij).1, (hLG _ (hNZ.1 _) _).1 fun p => (h p i j hij).2.1,
      (hLG _ (hNZ.2 _) _).1 fun p => (h p i j hij).2.2⟩
  · intro h p i j hij
    exact ⟨(hLG _ (hNZ.1 _) _).2 (h i j hij).1 p, (hLG _ (hNZ.1 _) _).2 (h i j hij).2.1 p,
      (hLG _ (hNZ.2 _) _).2 (h i j hij).2.2 p⟩

theorem stabIntShape_of (hL : LocShapeL D) (hG : LocShapeG D) (hLG : LocGlob D) (hNZ : ShapeNZ D) :
    StabIntShapeC D := by
  intro δ M hA u u' w a
  rw [StabIntGrp.mem_stabInt_iff, StabShape.mem_stabIntSet_iff δ M u u' hA w a]
  constructor
  · rintro ⟨ha, b, hb, hW, hp⟩
    exact ⟨ha, b, hb, hW, (glob_iff hLG hNZ a b).1 fun p => (loc_iff hL hG (p := p) hA ha hb).1 (hp p)⟩
  · rintro ⟨ha, b, hb, hW, he⟩
    exact ⟨ha, b, hb, hW, fun p => (loc_iff hL hG (p := p) hA ha hb).2 ((glob_iff hLG hNZ a b).2 he p)⟩

end Formalism.L2.SG.Pf.StabIntSh
