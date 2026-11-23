import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.TrDual
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementAB

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual beMean)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog lgN)

namespace GlobalTheory.KerStd

def BeData (l d : ℕ) [Fact l.Prime] [NeZero d] (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l))
    (om oms : Fin (d / 2) → MaximalUnramifiedExtension l) (ζ : MaximalUnramifiedExtension l) : Prop :=
  UnrOK (MaximalUnramifiedExtension l) l σ ∧ IsLawOfLog l F ∧ F1 F be0 ∧ F2 l σ be0 ∧ OwOK d σ om oms ∧ TrDual d σ om oms ∧
    IsPrimitiveRoot ζ (l ^ d - 1)

def beOf (l d : ℕ) [Fact l.Prime] [NeZero d] (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l))
    (om oms : Fin (d / 2) → MaximalUnramifiedExtension l) (ζ : MaximalUnramifiedExtension l) : MvPowerSeries (ZMod d) ℂ_[l] :=
  MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (beMean (d := d) l σ be0 om oms ζ)

def BeStd (l d : ℕ) [Fact l.Prime] [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  ∃ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) (om oms : Fin (d / 2) → MaximalUnramifiedExtension l) (ζ : MaximalUnramifiedExtension l),
    BeData l d σ F be0 om oms ζ ∧ be = beOf l d σ be0 om oms ζ

def BeFam (D : D7) (ep : ∀ w : D.what₂.places.Pl, ℂ_[D.what₂.places.resChar w])
    (be : ∀ w : D.what₂.places.Pl, OrbitPlaces.Pl D →
      MvPowerSeries (ZMod (nP D (D.what₂.places.resChar w))) ℂ_[D.what₂.places.resChar w]) : Prop :=
  ∀ w : D.what₂.places.Pl,
    ((IsResidueClassZero D (D.what₂.places.resChar w) ∧ HEv D (D.what₂.places.resChar w)) ∨ IsSg D (D.what₂.places.resChar w)) →
    ‖ep w‖ = 1 ∧ ∀ r, BeStd (D.what₂.places.resChar w) (nP D (D.what₂.places.resChar w)) (be w r)

def linEv (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (c : MaximalUnramifiedExtension p) (r : OrbitPlaces.Pl D) (a : Fin N0) (b : Fin N1) :
    MvPowerSeries (OrbitPlaces.Pl D × Fin N0 × Fin N1) ℂ_[p] :=
  ∑ s : ZMod (nP D p), if s.val % 2 = 0 then
    MvPowerSeries.C ((σ^[s.val] c : MaximalUnramifiedExtension p) : ℂ_[p]) * MvPowerSeries.X (OrbitPlaces.orbMap D p r s, a, b) else 0

def linOd (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (c : MaximalUnramifiedExtension p) (r : OrbitPlaces.Pl D) (a : Fin N0) (b : Fin N1) :
    MvPowerSeries (OrbitPlaces.Pl D × Fin N0 × Fin N1) ℂ_[p] :=
  ∑ s : ZMod (nP D p), if s.val % 2 = 0 then 0 else
    MvPowerSeries.C ((σ^[s.val] c : MaximalUnramifiedExtension p) : ℂ_[p]) * MvPowerSeries.X (OrbitPlaces.orbMap D p r s, a, b)

def hypZ (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {n : Type} (f f' : (R × Fin (nP D p / 2)) × Fin N0 × Fin N1 → n → MaximalUnramifiedExtension p) (i : n) :
    MvPowerSeries (OrbitPlaces.Pl D × Fin N0 × Fin N1) ℂ_[p] :=
  ∑ e : (R × Fin (nP D p / 2)) × Fin N0 × Fin N1,
    (MvPowerSeries.C (f e i : ℂ_[p]) * linEv D p σ (oms e.1.2) e.1.1 e.2.1 e.2.2 +
      MvPowerSeries.C (f' e i : ℂ_[p]) * linOd D p σ (om e.1.2) e.1.1 e.2.1 e.2.2)

def alLoc (Lc : product_zeroth_first_parts.Loc) (s : ZMod Lc.d) : ℕ := if s ∈ Lc.TT then (Lc.nu s).rowLen 0 - (Lc.nu s).rowLen 1 else 0

def gainA (Lc : product_zeroth_first_parts.Loc) : ℝ :=
  (∑ s ∈ Lc.TT, ∑' e : ℕ,
    if Odd e ∧ ¬ (e < Lc.d ∧ s + (e : ZMod Lc.d) ∈ Lc.TT) then
      max ((alLoc Lc s : ℝ) / (Lc.l : ℝ) ^ e - (Lc.cap (s + (e : ZMod Lc.d)) : ℝ)) 0 else 0) -
  ((∑ s : ZMod Lc.d, ((Lc.N1 : ℝ) * lgN Lc.l (alLoc Lc s) + (Lc.N0 : ℝ) * Lc.N1 * lgN Lc.l (Lc.size s - alLoc Lc s))) +
    ∑ s ∈ Lc.TT, ((lgN Lc.l (alLoc Lc s) : ℝ)) ^ 2)

end GlobalTheory.KerStd
