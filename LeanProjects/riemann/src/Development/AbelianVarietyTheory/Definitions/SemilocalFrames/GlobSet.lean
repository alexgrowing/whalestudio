import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.StepsR
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver

namespace GlobalTheory.GenMass

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Z : LocDat D} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {T T' : D.host.E}

def tm (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (G : LFlag (VS D) D.R.rS T) (G' : LFlag (VS D) D.R.rS T')
    (p : PlF D) (Λ : Submodule (Z.M p).L.O (Vp D p)) : Loc.Term (Vp D p) (Z.M p) D.R.rS :=
  ⟨Λ, scaled Z p (frame G), scaled Z p (frame G'), (FP p).A.T, (FP p).B.T⟩

def locSet (G : LFlag (VS D) D.R.rS T) (G' : LFlag (VS D) D.R.rS T') (p : PlF D) (d : LocNG.Datum (FP p)) :
    Set (Submodule (Z.M p).L.O (Vp D p)) :=
  {Λ | LocNG.IsTermOver (FP p) d (tm FP G G' p Λ) ∧ ¬ LocNG.BBne (H := locH Z p) (tm FP G G' p Λ)}

def locSum (G : LFlag (VS D) D.R.rS T) (G' : LFlag (VS D) D.R.rS T') (p : PlF D) (R : LocNG.Reps (FP p))
    (d0 : LocNG.Datum (FP p)) : ℝ≥0∞ :=
  ∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * ((locSet G G' p d.1).encard : ℝ≥0∞)

def globSet (G : LFlag (VS D) D.R.rS T) (G' : LFlag (VS D) D.R.rS T') (y : Dat Z FP) : Set (LV D) :=
  {Λ | Submodule.IsLattice D.host.E Λ ∧ ∀ p, lattice₂ D Z.M p Λ ∈ locSet G G' p (y p)}

def StdOff (Z : LocDat D) (P : Finset (PlF D)) (F G : LFlag (VS D) D.R.rS T) (F' G' : LFlag (VS D) D.R.rS T') : Prop :=
  Tri D.host.E (frame F) (frame G) ∧ Tri D.host.E (frame F') (frame G') ∧ G.zt = G.fl.z ∧ G'.zt = G'.fl.z ∧
  ∀ p, p ∉ P → ∃ A A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep, Uni A ∧ Uni A' ∧
    (∀ a b, A a b ∈ (Z.M p).L.O ∧ A' a b ∈ (Z.M p).L.O) ∧
    Chg (scaled Z p (frame F)) A (scaled Z p (frame G)) ∧ Chg (scaled Z p (frame F')) A' (scaled Z p (frame G'))

def BaseOK (Tn T'n : ℕ) (F : LFlag (VS D) D.R.rS (Tn : D.host.E)) (F' : LFlag (VS D) D.R.rS (T'n : D.host.E))
    (P : Finset (PlF D)) (d0 : Dat Z FP) : Prop :=
  Based Z FP Tn T'n F F' ∧ (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) ∧ (∀ p, p ∉ P → (FP p).PrimeTo) ∧
  (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ) ∧
  ∃ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ ∧ ∀ p, p ∉ P → LocNG.IsTermOver (FP p) (d0 p) (tm FP F F' p (lattice₂ D Z.M p Λ₀))

def MassLaw (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (P : Finset (PlF D)) (d0 : Dat Z FP) (V : ℝ) : Prop :=
  ∀ d : Dat Z FP, (∀ p, p ∉ P → d p = d0 p) → (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d p) τ) →
    massA F F' d = ENNReal.ofReal (V * ∏ p ∈ P, LocNG.Datum.wt (d0 p) (d p))

def glueSum (G : LFlag (VS D) D.R.rS T) (G' : LFlag (VS D) D.R.rS T') (s : Finset (LV D)) : ℝ :=
  ∑ Λ ∈ s, ((Nat.card (Formalism.L2.SG.Pf.Cnt.stabFix (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') Λ) : ℕ) : ℝ)⁻¹

def Glue (G : LFlag (VS D) D.R.rS T) (G' : LFlag (VS D) D.R.rS T') (s : Finset (LV D)) : Prop :=
  Formalism.L2.SG.Pf.Cnt.IsGlueReps (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') (Formalism.L2.SG.Pf.Cnt.MMof D G.fl G') s

end GlobalTheory.GenMass
