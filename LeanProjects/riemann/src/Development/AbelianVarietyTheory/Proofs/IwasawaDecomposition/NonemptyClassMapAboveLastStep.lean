import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

noncomputable def clDown {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ) (hi : B.R.m < i)
    (c : (I.stp u a i).Cl) : (I.stp u I.mu0 i).Cl :=
  (I.stp u I.mu0 i).cl (Idx.top I.sel (I.tup I.mu0) (I.idx I.mu0) (le_of_lt hi))
    ⟨(extTo (I.Q I.mu0) ((I.stp u a i).rep c).1.1, ∅), by
      rw [ysAt_ys_of_ne I.sel (I.tup I.mu0) (I.cst I.mu0) (by omega)]
      rfl⟩

theorem nonempty_clDown : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), B.R.m < i →
    Nonempty ((I.stp u a i).Cl → (I.stp u I.mu0 i).Cl) :=
  fun I _ u a i hi => ⟨I.clDown u a i hi⟩

end GlobalTheory.Mem.Col2.TC
