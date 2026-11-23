import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.AdelicNormWeight
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNatMulInt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsValueBelow
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ClassSumCompare

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def flip {X K : Type} [Neg X] (φ : X → K) : X → K := fun x => φ (-x)

section Reps

variable {n : ℕ}

def ords {ι : Type} (J : Subgroup (UA E n)) (h : ι → UA E n) : ι → ℕ := fun i => Nat.card (stab J (h i))

def lats {ι : Type} (h : ι → UA E n) : ι → GenLat E n := fun i => latOf (h i)

end Reps

section Sums

variable {n : ℕ} {ι : Type} [Fintype ι] {T : Type} [AddCommGroup T] [Module c.F T]

variable {Xo c}

def coverCoeff (d : DeltaDat Xo c n) (φ : (Fin n → ConjQ Dw l) → c.F) (φδ : (Fin n → LaJ Xo c d) → c.F) :
    (Fin n → LevQ Dw d.l₂) → c.F :=
  fun q => d.eF.symm (phiHat d.c₂ (flip (coverDatum d φ φδ)) q)

def twist (d : DeltaDat Xo c n) (g : Rul d.Xo₂ d.c₂) : DeltaDat Xo c n := { d with cδ := d.cδ * g }

abbrev Tested {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : Prop :=
  FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y

variable (Xo c)

end Sums

end GlobalTheory.ClassSumCompare
