import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.MixApply

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.omFinite :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (φ : S4 F) (C : Set (G1 F)), IsCompact C → ∃ s : Set (G1 F), s.Finite ∧ (∀ g ∈ s, InfOne g) ∧
    ∀ k ∈ C, ∃ g ∈ s, ∃ k', FinOne k' ∧ (InfOrth k → InfOrth k') ∧ W.Om k φ = W.Om k' (W.Om g φ) := by
  intro F E _ _ _ _ _ _ _ D W φ C hC
  obtain ⟨pi, pf, hpf, hp⟩ := UpperTheory.ConvolutionTheory.R2.Fo.proj F
  have hU : ∀ k₀ ∈ C, {k | W.Om (pf k) φ = W.Om (pf k₀) φ} ∈ 𝓝 k₀ := by
    intro k₀ _
    have hc : Continuous fun k : G1 F => pf (k₀⁻¹ * k) :=
      hpf.comp (continuous_const.mul continuous_id)
    have h1 : Tendsto (fun k : G1 F => pf (k₀⁻¹ * k)) (𝓝 k₀) (𝓝 1) := by
      have h := hc.tendsto k₀
      simpa using h
    filter_upwards [h1.eventually (W.level φ)] with k hk
    have h2 := hk (hp _).2.1
    have h3 : pf k = pf k₀ * pf (k₀⁻¹ * k) := by rw [← map_mul, mul_inv_cancel_left]
    change W.Om (pf k) φ = W.Om (pf k₀) φ
    rw [h3, map_mul, Module.End.mul_apply, h2]
  obtain ⟨t, -, hcov⟩ := hC.elim_nhds_subcover _ hU
  refine ⟨pf '' (t : Set (G1 F)), t.finite_toSet.image _, ?_, ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    exact (hp k).2.1
  · intro k hk
    obtain ⟨k₀, hk₀, hkk⟩ := Set.mem_iUnion₂.1 (hcov hk)
    refine ⟨pf k₀, ⟨k₀, hk₀, rfl⟩, pi k, (hp k).1, ?_, ?_⟩
    · intro ho i j
      have e : ∀ a b, ((pi k).1 a b).1 = (k.1 a b).1 := (hp k).2.2.2.1
      have key : (((pi k).1 * (pi k).1ᵀ) i j).1 = ((k.1 * k.1ᵀ) i j).1 := by
        have hadd : ∀ a b c d : A F, (a * b + c * d).1 = a.1 * b.1 + c.1 * d.1 := fun _ _ _ _ => rfl
        simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
        rw [hadd, hadd, e i 0, e j 0, e i 1, e j 1]
      exact key.trans (ho i j)
    · have h4 : W.Om k = W.Om (pi k) * W.Om (pf k) := by rw [← map_mul, (hp k).2.2.1]
      rw [h4, Module.End.mul_apply]
      exact congrArg _ hkk
