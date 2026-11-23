import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GlobFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SatOfFixed

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

private theorem aeInt {K : Type} [Field K] [NumberField K] (x : A K) :
    ∀ᶠ v : P K in cofinite, cp v x ∈ v.adicCompletionIntegers K :=
  x.2.2

private theorem aeKAt {K : Type} [Field K] [NumberField K] (g : GL (Fin 2) (A K)) :
    ∀ᶠ v in cofinite, KAt v g := by
  have h1 : ∀ᶠ v : P K in cofinite, ∀ i j, cp v (g.val i j) ∈ v.adicCompletionIntegers K :=
    eventually_all.2 fun i => eventually_all.2 fun j => aeInt _
  have h2 : ∀ᶠ v : P K in cofinite, ∀ i j, cp v ((g⁻¹).val i j) ∈ v.adicCompletionIntegers K :=
    eventually_all.2 fun i => eventually_all.2 fun j => aeInt _
  filter_upwards [h1, h2] with v a b
  rw [KAt, GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff]
  refine ⟨a, fun i j => ?_⟩
  rw [← map_inv]
  exact b i j

private theorem aeFix {K : Type} [Field K] [NumberField K] (f : GL (Fin 2) (A K) → ℂ)
    (hf : IsOpen {k : GL (Fin 2) (Af K) | ∀ g, f (g * finGL K 2 k) = f g}) :
    ∀ᶠ v in cofinite, Fix v f := by
  obtain ⟨S, hU⟩ := GlobalFixedVectors.exists_KAway_subset (M := 1)
    (hf.mem_nhds (show (1 : GL (Fin 2) (Af K)) ∈ _ from fun g => by simp))
  filter_upwards [S.eventually_cofinite_notMem] with w hw g k hk
  have h0 : ((1 : ℕ) : 𝓞 K) ∉ w.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top
  exact hU (GlobalFixedVectors.mem_KAway.2 ⟨locGL_mem_KLev 2 w h0 hk, fun x hx =>
    pLoc_locGL_of_ne (show x ≠ w from fun e => hw (e ▸ hx)) _⟩) g

theorem UpperTheory.ConvolutionTheory.R2.H.aeK :
    ∀ (K : Type) [Field K] [NumberField K], (∀ g : GL (Fin 2) (A K), ∀ᶠ v in cofinite, KAt v g) ∧ (∀ a : (A K)ˣ, ∀ᶠ v in cofinite, KAt v (dM a)) ∧
      ∀ f : GL (Fin 2) (A K) → ℂ, IsOpen {k : GL (Fin 2) (Af K) | ∀ g, f (g * finGL K 2 k) = f g} → ∀ᶠ v in cofinite, Fix v f := by
  intro K _ _
  exact ⟨aeKAt, fun a => aeKAt _, aeFix⟩
