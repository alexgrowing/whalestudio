import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabilizerFormValueStep
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_form_value_step : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → I.IsTw → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (i : ℕ), i < B.R.m →
    ∀ (c : (I.stp u I.mu0 i).Cl) (c' : (I.stp u I.mu0 (i + 1)).Cl) (g : (I.stp u I.mu0 (i + 1)).Stab c')
      (f : Fr B.fields.emb B.embLL (B.R.N i) → ℂ),
      f ∈ Formalism.L2.Forms.ValC (Gr B.fields.emb B.embLL (B.R.N i)) (lamT (B.hcW u) i) →
      (I.stp u I.mu0 (i + 1)).tr B.fields.emb B.embLL c'.1 g.1 ((I.chain l u I.mu0).Kmap i c c' f) = (I.chain l u I.mu0).Kmap i c c' f := by
  first | exact @GlobalTheory.KerStab.Kmap_stab | exact GlobalTheory.KerStab.Kmap_stab | (intros; apply GlobalTheory.KerStab.Kmap_stab <;> assumption)
