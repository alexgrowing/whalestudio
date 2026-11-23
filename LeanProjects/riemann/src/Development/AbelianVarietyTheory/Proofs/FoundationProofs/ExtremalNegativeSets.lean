import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.WeightFlagWeyl

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeightFlagWeyl

namespace GlobalTheory.Cmp.ExtremalNegativeSets

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Idx

variable {n : ℕ} {ε : Fin n → Bool}

theorem mem_negS {a : Fin n} : a ∈ negS ε ↔ ε a = false := by simp [negS]

theorem revNeg_anti {a b : Fin n} (hab : a < b) (ha : ε a = false) (hb : ε b = false) :
    revNeg ε b < revNeg ε a := by
  have ha' : a ∈ negS ε := mem_negS.2 ha
  have hb' : b ∈ negS ε := mem_negS.2 hb
  rw [show revNeg ε a = (revOn ε ⟨a, ha'⟩ : Fin n) from Equiv.Perm.ofSubtype_apply_of_mem _ ha',
    show revNeg ε b = (revOn ε ⟨b, hb'⟩ : Fin n) from Equiv.Perm.ofSubtype_apply_of_mem _ hb']
  have h1 : ((negS ε).orderIsoOfFin rfl).symm ⟨a, ha'⟩ < ((negS ε).orderIsoOfFin rfl).symm ⟨b, hb'⟩ :=
    (OrderIso.lt_iff_lt _).2 (Subtype.mk_lt_mk.2 hab)
  exact ((negS ε).orderIsoOfFin rfl).strictMono (Fin.rev_lt_rev.2 h1)

end Idx

variable {D : D7}

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end GlobalTheory.Cmp.ExtremalNegativeSets

end
