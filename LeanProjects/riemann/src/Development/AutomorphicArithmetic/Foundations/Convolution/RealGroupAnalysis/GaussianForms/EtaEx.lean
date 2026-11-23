import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.EtaQuad
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NormForm

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.etaEx :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E), ∃ η : HChar F, IsQuadCharOf E η ∧ (∀ a, η.1 a ^ 2 = 1) ∧ (∀ z : (A E)ˣ, η.1 (ideleNorm F E z) = 1) ∧
    ∀ a, η.1 a = 1 → ∃ (t : F) (z : (A E)ˣ), t ≠ 0 ∧ (a : A F) = rt t * (ideleNorm F E z : (A F)ˣ) := by
  intro F E _ _ _ _ _ D
  haveI : Algebra.IsQuadraticExtension F E :=
    ⟨by rw [Module.finrank_eq_card_basis D.b]; simp⟩
  have h0 : D.b 0 = 1 := D.b0
  have h1 : D.b 1 * D.b 1 = algebraMap F E D.δ := by
    rw [D.b1, ← pow_two, D.sq]
  obtain ⟨η, hq, hη⟩ := UpperTheory.ConvolutionTheory.R2.C.etaQuad F E
  have hone : ∀ a, GlobalTheory.IdeleNormChar.normSign E a = 1 → η.1 a = 1 := by
    intro a ha
    refine Units.ext ?_
    rw [hη a, ha]
    simp
  have hsign : ∀ a, η.1 a = 1 → GlobalTheory.IdeleNormChar.normSign E a = 1 := by
    intro a ha
    have h := hη a
    rw [ha] at h
    rcases Int.units_eq_one_or (GlobalTheory.IdeleNormChar.normSign E a) with e | e
    · exact e
    · rw [e] at h
      norm_num at h
  have hmem : ∀ z : (A E)ˣ, ideleNorm F E z ∈ GlobalTheory.QuadSymbol.normGroup F E (A F) := by
    intro z
    obtain ⟨s, t, hst⟩ := (UpperTheory.ConvolutionTheory.R2.C.normForm F E D (ideleNorm F E z)).2 ⟨z, rfl⟩
    exact (GlobalTheory.QuadSymbol.mem_normGroup_iff_form D.b h0 h1).2 ⟨s, t, hst⟩
  refine ⟨η, hq, ?_, ?_, ?_⟩
  · intro a
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, hη a]
    rcases Int.units_eq_one_or (GlobalTheory.IdeleNormChar.normSign E a) with e | e <;> rw [e] <;> simp
  · intro z
    exact hone _ (GlobalTheory.IdeleNormChar.normSign_of_mem E (hmem z))
  · intro a ha
    obtain ⟨t, ht⟩ := (GlobalTheory.IdeleNormChar.normSign_eq_one_iff E a).1 (hsign a ha)
    obtain ⟨s, u, hsu⟩ := (GlobalTheory.QuadSymbol.mem_normGroup_iff_form D.b h0 h1).1 ht
    obtain ⟨z, hz⟩ := (UpperTheory.ConvolutionTheory.R2.C.normForm F E D _).1 ⟨s, u, hsu⟩
    refine ⟨(t : F), z, t.ne_zero, ?_⟩
    rw [hz]
    have : a = GlobalTheory.QuadSymbol.toUnits F (A F) t * (a / GlobalTheory.QuadSymbol.toUnits F (A F) t) := by
      rw [mul_div_cancel]
    exact congrArg Units.val this
