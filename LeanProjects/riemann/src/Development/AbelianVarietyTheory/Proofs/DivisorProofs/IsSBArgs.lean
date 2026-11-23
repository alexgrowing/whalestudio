import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnfSupportOfNeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLatSmulBlockLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGlLatCongOfSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilOver

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

structure IsSBArgs (G : Grid k) (ϖ : kˣ) (n : ℕ) (F : ColArgs G → RowArgs G → ℂ) : Prop where
  dep : ∀ x x' y y', (∀ j, j < G.m → x j = x' j) → (∀ i, i < G.m → y i = y' i) → F x y = F x' y'
  per : ∀ x y a b, (∀ j, j < G.m → ∀ r s, valuation k (a j r s) ≤ valuation k ((ϖ ^ n : kˣ) : k)) →
    (∀ i, i < G.m → ∀ r s, valuation k (b i r s) ≤ valuation k ((ϖ ^ n : kˣ) : k)) → F (x + a) (y + b) = F x y
  supp : ∀ x y, F x y ≠ 0 → (∀ j, j < G.m → ∀ r s, valuation k (x j r s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k)) ∧
    ∀ i, i < G.m → ∀ r s, valuation k (y i r s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k)

end Local

section Half

variable {D : D7} {a b : ℕ}

def frAt (w : Pl D.host.E) (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D)) (x : Mx D b a) :
    Matrix (Fin b) (Fin a) (Kw w) :=
  (Comparison₂.fr β' β (x.map (toEAf D))).map (cpt (D := D) w)

def IsSmall (P : Finset (Pl D.host.E)) (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D)) (n : ℤ) (t : Mx D b a) : Prop :=
  ∀ w ∈ P, ∀ r s, valuation (Kw w) (frAt w β' β t r s) ≤ valuation (Kw w) ((unifAt w ^ n : (Kw w)ˣ) : Kw w)

open Classical in

def cosLoc (P : Finset (Pl D.host.E)) (e : AE D) (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D)) (n : ℤ)
    (r t : Mx D b a) : ℂ :=
  if IsHalf e t ∧ IsSmall P β' β n (t - r) then 1 else 0

end Half

end GlobalTheory.FunObj

end
