import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.BlkOneMem

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

private theorem isHecke_add {G : Type} [Group G] [TopologicalSpace G] {K : Subgroup G} {f g : G → ℂ}
    (hf : IsHecke K f) (hg : IsHecke K g) : IsHecke K fun y => f y + g y := by
  refine ⟨hf.1.add hg.1, fun k hk x => ?_⟩
  simp only [(hf.2 k hk x).1, (hf.2 k hk x).2, (hg.2 k hk x).1, (hg.2 k hk x).2, and_self]

private theorem isHecke_const_mul {G : Type} [Group G] [TopologicalSpace G] {K : Subgroup G} {f : G → ℂ}
    (c : ℂ) (hf : IsHecke K f) : IsHecke K fun y => c * f y := by
  refine ⟨hf.1.mul_left (f := fun _ => c), fun k hk x => ?_⟩
  simp only [(hf.2 k hk x).1, (hf.2 k hk x).2, and_self]

theorem ctLin : CtLin := by
  intro E _ _ _ w n a b h f g c hf hg
  refine ⟨funext fun m => ?_, funext fun m => ?_⟩
  · obtain ⟨e, -⟩ := ctSph E w n a b h _ (isHecke_add hf hg) m
    obtain ⟨e₁, s₁⟩ := ctSph E w n a b h f hf m
    obtain ⟨e₂, s₂⟩ := ctSph E w n a b h g hg m
    rw [e, e₁, e₂, finsum_add_distrib s₁ s₂, mul_add]
  · obtain ⟨e, -⟩ := ctSph E w n a b h _ (isHecke_const_mul c hf) m
    obtain ⟨e₁, s₁⟩ := ctSph E w n a b h f hf m
    rw [e, e₁, mul_left_comm c, mul_finsum _ c]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
