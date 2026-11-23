import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.SplitA
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.LamGen
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.LamReal

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.lamOne :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (g : FiniteAdeleRing (𝓞 F) F → ℂ), ∃ C : FiniteAdeleRing (𝓞 F) F → ℂ, ∀ b : (A F)ˣ, Lam1 (b : A F) (g1 g) = C (b : A F).2 * ∏ w, lamR (TR.pInf F (b : A F) w) := by
  intro F _ _ _ g
  obtain ⟨⟨e, c, he, hmap⟩, hψ⟩ := splitA F
  refine ⟨fun β => ((c.toReal : ℝ) : ℂ) ^ 2 * abelian₂ (finiteAdeleMeasure F)
    (fun x => ((finiteAdelicChar F (β * x ^ 2) : Circle) : ℂ)) g, fun b => ?_⟩
  have hne : ∀ w, TR.pInf F (b : A F) w ≠ 0 := by
    intro w h0
    have h1 : TR.pInf F (b : A F) * TR.pInf F ((b⁻¹ : (A F)ˣ) : A F) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have h2 := congrFun h1 w
    rw [Pi.mul_apply, h0, zero_mul] at h2
    exact zero_ne_one h2
  let γi : InfinitePlace F → ℝ → ℂ := fun w x =>
    Complex.exp (-(2 * Real.pi * Complex.I) * ((TR.pInf F (b : A F) w : ℝ) : ℂ) * (x : ℂ) ^ 2)
  let φi : InfinitePlace F → ℝ → ℂ := fun _ x => Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2)
  let γf : FiniteAdeleRing (𝓞 F) F → ℂ := fun x => ((finiteAdelicChar F ((b : A F).2 * x ^ 2) : Circle) : ℂ)
  have hadd : ∀ x y, e (x + y) = e x + e y := by
    intro x y
    simp only [he, map_add]
    rfl
  have h3 := (lamGen.2.2 (A F) ((InfinitePlace F → ℝ) × FiniteAdeleRing (𝓞 F) F) (adeleMeasure F) _ e c hadd hmap
    (fun p => (∏ w, γi w (p.1 w)) * γf p.2) (fun p => (∏ w, φi w (p.1 w)) * g p.2)).1
  have h1 := lamGen.1 (InfinitePlace F → ℝ) (FiniteAdeleRing (𝓞 F) F) volume (finiteAdeleMeasure F)
    (fun v => ∏ w, γi w (v w)) (fun v => ∏ w, φi w (v w)) γf g
  have h2 := lamGen.2.1 (InfinitePlace F) ℝ volume γi φi
  have h4 : ∀ w, abelian₂ (volume : Measure ℝ) (γi w) (φi w) = lamR (TR.pInf F (b : A F) w) :=
    fun w => lamReal _ (hne w)
  have hγ : (fun x : A F => ψ ((b : A F) * x ^ 2)) =
      fun x => (∏ w, γi w ((e x).1 w)) * γf (e x).2 := by
    funext x
    rw [hψ, he]
    congr 1
    · refine Finset.prod_congr rfl fun w _ => ?_
      have : TR.pInf F ((b : A F) * x ^ 2) w = TR.pInf F (b : A F) w * (TR.pInf F x w) ^ 2 := by
        rw [map_mul, map_pow]
        rfl
      simp only [γi]
      rw [this]
      push_cast
      ring_nf
  have hφ : g1 g = fun x : A F => (∏ w, φi w ((e x).1 w)) * g (e x).2 := by
    funext x
    rw [he]
    rfl
  have hL : Lam1 (b : A F) (g1 g) = abelian₂ (adeleMeasure F) (fun x : A F => ψ ((b : A F) * x ^ 2)) (g1 g) := rfl
  have hv : (volume : Measure (InfinitePlace F → ℝ)) = Measure.pi fun _ => volume := volume_pi
  rw [hL, hγ, hφ, h3, h1, hv, h2]
  simp only [h4]
  ring
