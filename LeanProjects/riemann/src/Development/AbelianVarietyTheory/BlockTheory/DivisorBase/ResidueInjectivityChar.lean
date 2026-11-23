import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links

namespace GlobalTheory.IndefiniteRowSideFullHecke.ResidueInjectivityChar

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def VanishesOnLowest {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (U : MMap M) : Prop :=
  ∀ v : ∀ ρ, lowT M ρ, U (fun ρ => (v ρ : M.sm ρ)) = 0

def ResInjAt (R : RealDat D A Ks) : Prop :=
  ∀ i : Fin D.R.m, ∀ U ∈ R.Wall i (sg0 D A), VanishesOnLowest (R.MW i (sg0 D A)) U → U = 0

end

def ResInj : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → R.models_inf → R.models_order → ResInjAt R

section Basic₂

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem ResInj.of_char (h : ResInj) (R : RealDat D A Ks) (F : Face D A) (hR : R.Char F) : ResInjAt R :=
  h D G Pl0 T A Ks R hR.lev hR.models.inf hR.models.order

theorem ResInjAt.ext {R : RealDat D A Ks} (h : ResInjAt R) (i : Fin D.R.m) {U U' : MMap (R.MW i (sg0 D A))}
    (hU : U ∈ R.Wall i (sg0 D A)) (hU' : U' ∈ R.Wall i (sg0 D A))
    (e : ∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, U (fun ρ => v ρ) = U' (fun ρ => v ρ)) : U = U' := by
  refine sub_eq_zero.1 (h i _ (Submodule.sub_mem _ hU hU') fun v => ?_)
  rw [MultilinearMap.sub_apply, e v, sub_self]

theorem ResInjAt.good {R : RealDat D A Ks} (h : ResInjAt R) (i : Fin D.R.m) {U : MMap (R.MW i (sg0 D A))}
    (hU : U ∈ R.Wat i (sg0 D A) R.triv) (e : VanishesOnLowest (R.MW i (sg0 D A)) U) : U = 0 :=
  h i U (goodPart_le _ _ _ _ _ hU) e

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.ResidueInjectivityChar

end
