import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

theorem trSph : TrSph := by
  intro hEx hSL E _ _ _ n w τ B hB e
  have hne : fixed τ.ρ (KGL w n) ≠ ⊥ := hB.1
  have hfr : Module.finrank ℂ (fixed τ.ρ (KGL w n)) = 1 := (hSL E n w τ hne).1
  have hact : ∀ x ∈ fixed τ.ρ (KGL w n),
      levOp τ.ρ (KGL w n) (KGL w n) (fn1 n w e) LinearMap.id x = ev1 n w e B • x := by
    intro x hx
    by_cases h0 : x = 0
    · simp [h0]
    · exact (hEx E n w e).2 _ τ.ρ x B (hB.2 x hx h0)
  have hmaps : ∀ v ∈ fixed τ.ρ (KGL w n),
      levOp τ.ρ (KGL w n) (KGL w n) (fn1 n w e) LinearMap.id v ∈ fixed τ.ρ (KGL w n) := fun v hv => by
    rw [hact v hv]
    exact Submodule.smul_mem _ _ hv
  have hres : (levOp τ.ρ (KGL w n) (KGL w n) (fn1 n w e) LinearMap.id).restrict hmaps =
      ev1 n w e B • LinearMap.id := by
    ext ⟨x, hx⟩
    simp [LinearMap.restrict_apply, hact x hx]
  haveI : Module.Finite ℂ (fixed τ.ρ (KGL w n)) := Module.finite_of_finrank_pos (by omega)
  unfold twTr
  rw [dif_pos hmaps, hres, map_smul, LinearMap.trace_id, hfr]
  simp

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
