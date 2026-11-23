import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFlipGL

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open GlobalTheory.CompanionTheory.ConjSat

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.uConj :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.UConj := by
  intro E _ _ _ n σ w hw τ B ⟨_, f, f0, hf, hfx⟩ hB
  have hu : locU n (UpperTheory.V.Af.Bc.cPl w) = locU n w :=
    locU_eq_of_under (GlobalTheory.SplitPts.over_split hw).2.1
  refine ⟨flipIrr τ, ⟨(flipIrr τ).irred, f, f0, hf, fun x v => ?_⟩, hasSatGL_flipIrr τ hB⟩
  have hx : (x : UA E n) ∈ locU n w := hu ▸ x.2
  have key := hfx ⟨x, hx⟩ v
  rw [MonoidHom.comp_apply] at key
  change f (τ.ρ (flipGL w (cLoc _ x.1)) v) = _
  rw [← cLoc_eq_flipGL]
  exact key
