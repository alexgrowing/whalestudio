import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.StrongMultOneC

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.niceOf :
    UpperTheory.V.Af.StrongMultiplicityOne.NiceOf := by
  intro E _ _ n φ
  have hl : ∃ V : OpenSubgroup (GL (Fin n) (Af E)), ∀ g, ∀ v ∈ V, φ.1 (g * finGL E n v) = φ.1 g := by
    obtain ⟨W, -, hW⟩ := exists_openSubgroup_rightInvariant φ.2.1.isSmooth φ.2.1.isKFinite
    refine ⟨W, fun g v hv => ?_⟩
    rw [← Fb.finEmb_eq]
    exact hW g v hv
  exact ⟨hl, fun h => ⟨φ.2.1.continuous, exists_norm_le_of_mem_centralCuspForms h, φ.2.1.isLeftInvariant, φ.2.2, hl⟩⟩
