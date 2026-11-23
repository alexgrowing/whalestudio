import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc

namespace GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev GV (D : D7) : Type := (VS D).V ≃ₗ[D.host.E] (VS D).V

abbrev LV (D : D7) : Type := Submodule (𝓞 D.host.E) (VS D).V

def Adapt {T : D.host.E} (g : GV D) (F G : LFlag (VS D) D.R.rS T) : Prop :=
  g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ ∀ a : Fin (D.R.rS + 1), g (frame F a) - frame G a ∈ Xflag G a.val

def Aut0 {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (Λ : LV D) : Set (GV D) :=
  {a | Adapt a F F ∧ Formalism.HermitianLatticesTheory.gmap a Λ = Λ}

section Base

variable {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')

def H0 : Set (GV D) :=
  {h | h ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ (∀ a, h (frame F a) = frame F a) ∧ ∀ a, h (frame F' a) = frame F' a}

def gdat (Λ : LV D) : LV D × LV D × Set ((VS D).V × (VS D).V) :=
  (Lsub Λ F, Lsub Λ F',
    {p | ∃ l' ∈ Lrep Λ F', ∃ l ∈ Lrep Λ F, p.1 - l' ∈ Xsp F' ∧ p.2 - l ∈ Xsp F ∧ l - l' ∈ NgX Λ (gS D) F F'})

def LRel (Λ₁ Λ₂ : LV D) : Prop := ∃ h ∈ H0 F F', gdat F F' (Formalism.HermitianLatticesTheory.gmap h Λ₁) = gdat F F' Λ₂

def stabL (Λ : LV D) : Set (GV D) := {h | h ∈ H0 F F' ∧ gdat F F' (Formalism.HermitianLatticesTheory.gmap h Λ) = gdat F F' Λ}

end Base

def KeyEq {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (Λ : LV D) (γ₁ γ₂ : GV D) : Prop :=
  (∃ n ∈ NRat F, ∃ n' ∈ NRat F', γ₂ = n * γ₁ * n') ∧
    IotaCompat Λ F (mapLF γ₁ F') (mapLF γ₂ F') (γ₂ * γ₁⁻¹) (gS D)

section Local

variable (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS)

def Ext (p : PlF D) (g : GV D) (g' : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) : Prop := ∀ x, g' (baseChange₂ D p x) = baseChange₂ D p (g x)

def Based (Tn T'n : ℕ) (F : LFlag (VS D) D.R.rS (Tn : D.host.E)) (F' : LFlag (VS D) D.R.rS (T'n : D.host.E)) : Prop :=
  ∀ p, (FP p).A.f = (fun a => frFac Z.δ p a • baseChange₂ D p (frame F a)) ∧
    (FP p).B.f = (fun a => frFac Z.δ p a • baseChange₂ D p (frame F' a)) ∧
    (FP p).A.T = (Tn : (D.s.atP p).Fp) ∧ (FP p).B.T = (T'n : (D.s.atP p).Fp)

abbrev Dat : Type := ∀ p : PlF D, LocNG.Datum (FP p)

variable {Z FP}

def LocOver (Λ : LV D) (y : Dat Z FP) : Prop :=
  Submodule.IsLattice D.host.E Λ ∧
    ∀ p, ∃ τ : Loc.Term (Vp D p) (Z.M p) D.R.rS, LocNG.IsTermOver (FP p) (y p) τ ∧ τ.abelian₂ = lattice₂ D Z.M p Λ

def RMoves (h : GV D) (y y' : Dat Z FP) : Prop :=
  ∀ p, ∃ g', Ext p h g' ∧ LocNG.Datum.Moves g' (y p) (y' p)

def InGen (d y : Dat Z FP) : Prop :=
  (∀ p, LocNG.Datum.Rel (d p) (y p)) ∧ {p | y p ≠ d p}.Finite

variable {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')

def GRel (y y' : Dat Z FP) : Prop := ∃ h ∈ H0 F F', RMoves h y y'

def stabY (y : Dat Z FP) : Set (GV D) := {h | h ∈ H0 F F' ∧ RMoves h y y}

def massA (d : Dat Z FP) : ℝ≥0∞ :=
  ∑' o : Quot (GRel (Z := Z) (FP := FP) F F'), if InGen d o.out then (((stabY F F' o.out).encard : ℝ≥0∞))⁻¹ else 0

end Local

section Terms

variable {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}
  (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))

def TG (t : TauC Y u u') (Λ : LV D) : Prop :=
  ∃ g, Adapt g (lf D (X.Fu u)) F ∧ Adapt g t.frame F' ∧ Λ = Formalism.HermitianLatticesTheory.gmap g t.lam

def key (t : TauC Y u u') := ((Y.tO u u').rowOf t, nmlOf Y u u' t)

def ClsRow {Cl : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl) : Prop :=
  ∀ t ∈ TS, ∀ t' ∈ TS, nmlOf Y u u' t = nmlOf Y u u' t' →
    (cls t = cls t' ↔ (Y.tO u u').rowOf t = (Y.tO u u').rowOf t')

def LocClosed (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (TS : Set (TauC Y u u')) : Prop :=
  ∀ t t' Λ Λ', TG F F' t Λ → TG F F' t' Λ' →
    (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ) = lattice₂ D Z.M p Λ') → t ∈ TS → t' ∈ TS

end Terms

end GlobalTheory.Unfold
