import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.OrthZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TwtrContOfMem

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.Zero.ConvolutionTheory.EB
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open scoped Classical

attribute [local instance] borelG borelF borelA borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.TS

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private lemma trace_range_eq (A : V →ₗ[ℂ] V) (W : Submodule ℂ V) [FiniteDimensional ℂ W]
    (hA : LinearMap.range A ≤ W) (hW : ∀ x ∈ W, A x ∈ W) :
    LinearMap.trace ℂ (LinearMap.range A) (A.restrict fun x _ => LinearMap.mem_range_self A x) =
      LinearMap.trace ℂ W (A.restrict hW) := by
  have hfd : FiniteDimensional ℂ (LinearMap.range A) :=
    Submodule.finiteDimensional_of_le hA
  let f : W →ₗ[ℂ] LinearMap.range A :=
    (A.comp W.subtype).codRestrict _ fun x => LinearMap.mem_range_self A _
  let g : LinearMap.range A →ₗ[ℂ] W := Submodule.inclusion hA
  have e1 : A.restrict (fun x _ => LinearMap.mem_range_self A x) = f ∘ₗ g := by
    ext x; rfl
  have e2 : A.restrict hW = g ∘ₗ f := by
    ext x; rfl
  rw [e1, e2, LinearMap.trace_comp_comm' f g]

private lemma trace_sum {J : Type*} (s : Finset J) (c : J → ℂ) (L : J → V →ₗ[ℂ] V)
    (h : ∀ j ∈ s, FiniteDimensional ℂ (LinearMap.range (L j))) :
    FiniteDimensional ℂ (LinearMap.range (∑ j ∈ s, c j • L j)) ∧
    LinearMap.trace ℂ (LinearMap.range (∑ j ∈ s, c j • L j))
        ((∑ j ∈ s, c j • L j).restrict fun x _ => LinearMap.mem_range_self _ x) =
      ∑ j ∈ s, c j * LinearMap.trace ℂ (LinearMap.range (L j))
        ((L j).restrict fun x _ => LinearMap.mem_range_self _ x) := by
  classical
  let W : Submodule ℂ V := s.sup fun j => LinearMap.range (L j)
  have hfd : FiniteDimensional ℂ W := by
    refine Finset.sup_induction (p := fun U : Submodule ℂ V => FiniteDimensional ℂ U) ?_ ?_ h
    · exact inferInstanceAs (FiniteDimensional ℂ (⊥ : Submodule ℂ V))
    · intro a ha b hb
      exact Submodule.finiteDimensional_sup a b
  have hle : ∀ j ∈ s, LinearMap.range (L j) ≤ W := fun j hj =>
    Finset.le_sup (f := fun j => LinearMap.range (L j)) hj
  have hS : LinearMap.range (∑ j ∈ s, c j • L j) ≤ W := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.sum_apply]
    exact W.sum_mem fun j hj => W.smul_mem _ (hle j hj (LinearMap.mem_range_self _ x))
  have hj' : ∀ j ∈ s, ∀ x ∈ W, L j x ∈ W := fun j hj x _ => hle j hj (LinearMap.mem_range_self _ x)
  have hSW : ∀ x ∈ W, (∑ j ∈ s, c j • L j) x ∈ W := fun x _ => hS (LinearMap.mem_range_self _ x)
  refine ⟨Submodule.finiteDimensional_of_le hS, ?_⟩
  rw [trace_range_eq _ W hS hSW]
  have e : (∑ j ∈ s, c j • L j).restrict hSW =
      ∑ j ∈ s.attach, c j.1 • (L j.1).restrict (hj' j.1 j.2) := by
    ext x
    simp only [LinearMap.restrict_coe_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.coe_sum, Submodule.coe_smul]
    rw [← Finset.sum_attach s]
  rw [e, map_sum, ← Finset.sum_attach s]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, trace_range_eq (L j.1) W (hle j.1 j.2) (hj' j.1 j.2)]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.TS

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.TS in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.twTrSum_pf :
    TwTrSum := by
  intro E _ _ _ n D π J s c φ t h
  have hL := fun j (hj : j ∈ s) => (h j hj).2
  choose! L e f ht using hL
  have hT := trace_sum s c L f
  haveI : IsLocallyFiniteMeasure D.μ := D.haar.2.2.2
  refine ⟨∑ j ∈ s, c j • L j, fun ψ x => ?_, hT.1, ?_⟩
  · have hc : Continuous fun g : GA E n => ψ.1.1 (thetaA E n g) :=
      (DiscreteGroups.T1.G.twtr_cont_of_mem π ψ.2).comp (PositivityTheory.Rg.BcB.E1.thetaBasic_holds E n).1
    have hi : ∀ j ∈ s, Integrable (fun y => φ j y * ψ.1.1 (thetaA E n (x * y.1))) D.μ := fun j hj =>
      DiscreteGroups.T1.G.twtr_integrable D.μ (h j hj).1 hc x
    have hv : ((∑ j ∈ s, c j • L j) ψ).1.1 x = ∑ j ∈ s, c j * (L j ψ).1.1 x := by
      simp [LinearMap.sum_apply]
    rw [hv, Finset.sum_congr rfl fun j hj => by rw [e j hj ψ x]]
    simp_rw [← integral_const_mul]
    rw [← integral_finset_sum _ fun j hj => (hi j hj).const_mul _]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [Finset.sum_apply, Finset.sum_mul, mul_assoc]
  · rw [hT.2]
    exact Finset.sum_congr rfl fun j hj => by rw [ht j hj]
