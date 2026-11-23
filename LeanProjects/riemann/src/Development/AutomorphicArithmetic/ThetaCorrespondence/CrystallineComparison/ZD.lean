import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.LocTied6

noncomputable section

namespace Formalism.BasicNotions.CmpTie

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

variable (l : ℕ) [Fact l.Prime]

def Compat (eB : Per.Bcris l ≃+* Per6.Bcris l) (eD : Per.BdR l ≃+* Per6.BdR l) (eP : Per.BdRp l ≃+* Per6.BdRp l) :
    Prop :=
    (∀ z : ℤ_[l], eB (Per.zB l z) = Per6.zB l z) ∧
    (∀ z : ℤ_[l], eD (Per.zD l z) = Per6.zD l z) ∧
    (∀ y : Per.BdRp l, eD (algebraMap (Per.BdRp l) (Per.BdR l) y) = algebraMap (Per6.BdRp l) (Per6.BdR l) (eP y)) ∧
    (∀ y : Per.BdRp l, Per6.θD l (eP y) = Per.θD l y) ∧
    (∀ (g : GQ l) (b : Per.Bcris l), eB (Per.σB g b) = Per6.σB g (eB b)) ∧
    (∀ (g : GQ l) (x : Per.BdR l), eD (Per.σD g x) = Per6.σD g (eD x)) ∧
    (∀ b : Per.Bcris l, eB (Per.φB l b) = Per6.φB l (eB b)) ∧
    (∀ f : Per.Bcris l →+* Per.BdR l, Per.IsCrisDR l f ↔ Per6.IsCrisDR l ((eD.toRingHom.comp f).comp eB.symm.toRingHom)) ∧
    (∀ (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a ↔ eD x ∈ Per6.FilD l a) ∧
    (∀ {P : LocPrime l} (AI : LocAinf l P) (y : Per.BdRp l), Per.IsLog l AI.ε y ↔ Per6.IsLog l AI.ε (eP y)) ∧
    (∀ a : Ainf l, eB (Per.aB l a) = Per6.aB l a)

def Cmp : Prop :=
  ∃ (eB : Per.Bcris l ≃+* Per6.Bcris l) (eD : Per.BdR l ≃+* Per6.BdR l) (eP : Per.BdRp l ≃+* Per6.BdRp l),
    Compat l eB eD eP

variable {l} {eB : Per.Bcris l ≃+* Per6.Bcris l} {eD : Per.BdR l ≃+* Per6.BdR l} {eP : Per.BdRp l ≃+* Per6.BdRp l}

theorem Compat.zB (h : Compat l eB eD eP) :
    ∀ z : ℤ_[l], eB (Per.zB l z) = Per6.zB l z :=
  h.1

theorem Compat.zD (h : Compat l eB eD eP) :
    ∀ z : ℤ_[l], eD (Per.zD l z) = Per6.zD l z :=
  h.2.1

theorem Compat.alg (h : Compat l eB eD eP) :
    ∀ y : Per.BdRp l, eD (algebraMap (Per.BdRp l) (Per.BdR l) y) = algebraMap (Per6.BdRp l) (Per6.BdR l) (eP y) :=
  h.2.2.1

theorem Compat.θ (h : Compat l eB eD eP) :
    ∀ y : Per.BdRp l, Per6.θD l (eP y) = Per.θD l y :=
  h.2.2.2.1

theorem Compat.σB (h : Compat l eB eD eP) :
    ∀ (g : GQ l) (b : Per.Bcris l), eB (Per.σB g b) = Per6.σB g (eB b) :=
  h.2.2.2.2.1

theorem Compat.σD (h : Compat l eB eD eP) :
    ∀ (g : GQ l) (x : Per.BdR l), eD (Per.σD g x) = Per6.σD g (eD x) :=
  h.2.2.2.2.2.1

theorem Compat.φB (h : Compat l eB eD eP) :
    ∀ b : Per.Bcris l, eB (Per.φB l b) = Per6.φB l (eB b) :=
  h.2.2.2.2.2.2.1

theorem Compat.incl (h : Compat l eB eD eP) :
    ∀ f : Per.Bcris l →+* Per.BdR l, Per.IsCrisDR l f ↔ Per6.IsCrisDR l ((eD.toRingHom.comp f).comp eB.symm.toRingHom) :=
  h.2.2.2.2.2.2.2.1

theorem Compat.fil (h : Compat l eB eD eP) :
    ∀ (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a ↔ eD x ∈ Per6.FilD l a :=
  h.2.2.2.2.2.2.2.2.1

theorem Compat.log (h : Compat l eB eD eP) :
    ∀ {P : LocPrime l} (AI : LocAinf l P) (y : Per.BdRp l), Per.IsLog l AI.ε y ↔ Per6.IsLog l AI.ε (eP y) :=
  h.2.2.2.2.2.2.2.2.2.1

theorem Compat.aB (h : Compat l eB eD eP) :
    ∀ a : Ainf l, eB (Per.aB l a) = Per6.aB l a :=
  h.2.2.2.2.2.2.2.2.2.2

end Formalism.BasicNotions.CmpTie
