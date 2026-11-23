import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.StrongMultOneC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CmBridge

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.carrier :
    UpperTheory.V.Af.StrongMultiplicityOne.Carrier := by
  intro E _ _ _ n π
  refine ⟨Cm.carrier π, Cm.stab_carrier π, (Cm.stab_carrier π).isIrreducible_iff.1 (Cm.isIrreducible_toModule π),
    fun f => ⟨fun ⟨ψ, hψ, e⟩ => ⟨_, hψ, e⟩, fun ⟨φ, hφ, e⟩ => ?_⟩⟩
  rw [← Cm.map_carrier] at hφ
  obtain ⟨ψ, hψ, rfl⟩ := hφ
  exact ⟨ψ, hψ, e⟩
