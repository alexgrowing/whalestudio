import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import GroundTheory.GlobalFields.TateThesis.SchwartzBruhatDual
import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.perpCpt :
    ∀ (F : Type) [Field F] [NumberField F] (Λ : OpenAddSubgroup (FiniteAdeleRing (𝓞 F) F)), ∃ K : Set (FiniteAdeleRing (𝓞 F) F), IsCompact K ∧
    ∀ x : A F, (∀ a : A F, a.1 = 0 → a.2 ∈ Λ → ψ (a * x) = 1) → x.2 ∈ K := by
  intro F _ _ Λ
  obtain ⟨J, hJ⟩ := exists_idealFiniteAdeles_subset (K := F) (W := (Λ : Set (FiniteAdeleRing (𝓞 F) F)))
    (Λ.isOpen.mem_nhds Λ.zero_mem)
  refine ⟨(idealFiniteAdeles (traceDualIdeal F J) : Set (FiniteAdeleRing (𝓞 F) F)),
    isCompact_idealFiniteAdeles _, fun x hx => ?_⟩
  refine (forall_finiteAdelicChar_mul_eq_one_iff J x.2).1 fun y hy => ?_
  have h := hx (finiteAdeleInr y) rfl (hJ hy)
  have e : finiteAdeleInr y * x = finiteAdeleInr (y * x.2) := by
    refine Prod.ext ?_ rfl
    change (0 : _) * x.1 = 0
    exact zero_mul _
  rw [e] at h
  rw [finiteAdelicChar_apply]
  exact Circle.ext h
