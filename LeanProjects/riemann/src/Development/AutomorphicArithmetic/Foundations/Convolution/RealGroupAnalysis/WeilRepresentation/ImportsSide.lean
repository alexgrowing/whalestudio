import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsBis
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.ContMkE
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SpanCont
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Splt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.KeyFock
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GmapCont

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H

theorem UpperTheory.ConvolutionTheory.R2.split :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Split W M π := by
  intro F E _ _ _ _ _ _ _ D W M π h0 Q hQ v w i hi hc σ σ' hσ hσ'
  obtain ⟨θ, hθ⟩ := UpperTheory.ConvolutionTheory.R2.I.splt F E D v w i hi hc
  obtain ⟨ι, hι, he⟩ := hσ'
  obtain ⟨y, hy⟩ : ∃ y, ι y ≠ 0 := by
    by_contra hn
    exact hι (LinearMap.ext fun y => by_contra fun h => hn ⟨y, h⟩)
  obtain ⟨h, hh⟩ : ∃ h, WE D (ι y).1.1 h ≠ 0 := by
    by_contra hn
    exact hy (Subtype.ext ((UpperTheory.ConvolutionTheory.R2.cusp F E D W M π h0 _ (hQ (ι y).2)).2 fun h => by_contra fun e => hn ⟨h, e⟩))
  have hcont : ∀ u, Continuous (ι u).1.1 := fun u => (H.spanCont F E D W M π _ (hQ (ι u).2)).1
  have hz : ∀ k, WE D (0 : GL (Fin 2) (A E) → ℂ) k = 0 := fun k => by simp [WE]
  let J := (lc w).comp (Matrix.GeneralLinearGroup.map i.toRingHom)
  let T : σ'.V →ₗ[ℂ] (I.GLv v → ℂ) :=
    { toFun := fun u x => WE D (ι u).1.1 (h * J x)
      map_add' := fun u u' => funext fun x => by
        have := (H.weEig F E D _ (hcont u)).2.2 _ 1 (hcont u') (h * J x)
        rw [one_smul, one_mul] at this
        rw [map_add]; exact this
      map_smul' := fun c u => funext fun x => by
        have := (H.weEig F E D 0 continuous_const).2.2 _ c (hcont u) (h * J x)
        rw [zero_add, hz, zero_add] at this
        rw [map_smul]; exact this }
  refine UpperTheory.ConvolutionTheory.R2.I.fin F E π v w i hi σ σ' hσ T (fun e => hh ?_) (fun g u x => ?_) fun u =>
    UpperTheory.ConvolutionTheory.R2.I.key F E D W M π v θ J hθ _ (hQ (ι u).2) h
  · have := congrFun (LinearMap.congr_fun e y) 1
    simpa [T] using this
  · change WE D (ι _).1.1 _ = WE D (ι u).1.1 (h * J (x * g))
    rw [he, map_mul, ← mul_assoc]
    unfold WE
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    beta_reduce
    rw [← mul_assoc _ _ (J g)]
    rfl
