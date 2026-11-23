import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.PsiLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem indicator_mem_SB {X : Type} [TopologicalSpace X] {f : X → ℂ} (hf : f ∈ SB X)
    {U : Set X} (hU : IsClopen U) : U.indicator f ∈ SB X := by
  refine ⟨?_, ?_⟩
  · have h1 : IsLocallyConstant (U.indicator fun _ : X => (1 : ℂ)) := by
      rw [IsLocallyConstant.iff_isOpen_fiber]
      intro c
      by_cases h1 : (1 : ℂ) = c <;> by_cases h0 : (0 : ℂ) = c
      · exact absurd (h1.trans h0.symm) one_ne_zero
      · have : (U.indicator fun _ : X => (1 : ℂ)) ⁻¹' {c} = U := by
          ext x
          by_cases hx : x ∈ U <;> simp [hx, h1, Ne.symm h0, h0]
        rw [this]; exact hU.isOpen
      · have : (U.indicator fun _ : X => (1 : ℂ)) ⁻¹' {c} = Uᶜ := by
          ext x
          by_cases hx : x ∈ U <;> simp [hx, Ne.symm h1, h1, h0]
        rw [this]; exact hU.compl.isOpen
      · have : (U.indicator fun _ : X => (1 : ℂ)) ⁻¹' {c} = ∅ := by
          ext x
          by_cases hx : x ∈ U <;> simp [hx, Ne.symm h1, Ne.symm h0, h1, h0]
        rw [this]; exact isOpen_empty
    have h2 : U.indicator f = (U.indicator fun _ : X => (1 : ℂ)) * f := by
      ext x
      by_cases hx : x ∈ U <;> simp [hx]
    rw [h2]
    exact h1.mul hf.1
  · exact HasCompactSupport.mono hf.2 (fun x hx => by
      by_contra h0
      apply hx
      have h0' : f x = 0 := by simpa using h0
      by_cases hxU : x ∈ U <;> simp [hxU, h0'])

theorem UpperTheory.ConvolutionTheory.R2.I.loc :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (ℓ : SB (M2 v) →ₗ[ℂ] ℂ),
      (∀ (s : Kv v) (a a' : SB (M2 v)), (∀ m, a'.1 m = ψl v (-(s * m.det)) * a.1 m) → ℓ a' = ψl v (-s) * ℓ a) →
      ∀ a : SB (M2 v), (∀ m : M2 v, m.det = 1 → a.1 m = 0) → ℓ a = 0 := by
  intro F _ _ v ℓ h a ha
  obtain ⟨-, -, hadd, hlc, hnt, -⟩ := psiLaws F v
  have hψ0 : ∀ x, ψl v x ≠ 0 := fun x => Circle.coe_ne_zero _

  have key : ∀ m0 : M2 v, m0.det ≠ 1 → ∃ N : Set (M2 v), IsClopen N ∧ m0 ∈ N ∧
      ∀ b : SB (M2 v), Function.support b.1 ⊆ N → ℓ b = 0 := by
    intro m0 hm
    obtain ⟨t, ht⟩ := hnt (m0.det - 1) (sub_ne_zero.mpr hm)
    have hz : ψl v (-(-t * m0.det)) ≠ ψl v (- -t) := by
      intro hzz
      apply ht
      have e : -(-t * m0.det) = t * (m0.det - 1) + - -t := by ring
      rw [e, hadd] at hzz
      exact mul_right_cancel₀ (hψ0 _) (hzz.trans (one_mul _).symm)
    have hf : IsLocallyConstant (fun m : M2 v => ψl v (-(-t * m.det))) :=
      hlc.comp_continuous (by
        have : Continuous fun m : M2 v => m.det := continuous_id.matrix_det
        exact (continuous_const.mul this).neg)
    refine ⟨(fun m : M2 v => ψl v (-(-t * m.det))) ⁻¹' {ψl v (-(-t * m0.det))},
      hf.isClopen_fiber _, rfl, fun b hb => ?_⟩
    have h1 := h (-t) b (ψl v (-(-t * m0.det)) • b) (fun m => by
      by_cases hm' : b.1 m = 0
      · simp [hm']
      · have : ψl v (-(-t * m.det)) = ψl v (-(-t * m0.det)) := hb hm'
        rw [this]; rfl)
    rw [map_smul, smul_eq_mul] at h1
    by_contra hne
    exact hz (mul_right_cancel₀ hne h1)
  have hsupp : tsupport a.1 = Function.support a.1 := by
    refine IsClosed.closure_eq ?_
    have : Function.support a.1 = (a.1 ⁻¹' {0})ᶜ := by
      ext x; simp
    rw [this]
    exact (a.2.1.isClopen_fiber 0).compl.isClosed
  have main : ∃ C : Set (M2 v), IsClopen C ∧ tsupport a.1 ⊆ C ∧
      ∀ b : SB (M2 v), Function.support b.1 ⊆ C → ℓ b = 0 := by
    refine IsCompact.induction_on (p := fun T : Set (M2 v) => ∃ C : Set (M2 v), IsClopen C ∧ T ⊆ C ∧
      ∀ b : SB (M2 v), Function.support b.1 ⊆ C → ℓ b = 0) a.2.2 ?_ ?_ ?_ ?_
    · refine ⟨∅, isClopen_empty, subset_rfl, fun b hb => ?_⟩
      have : b = 0 := by
        apply Subtype.ext
        funext x
        by_contra hx
        exact hb hx
      rw [this, map_zero]
    · rintro S T hST ⟨C, hC, hTC, hb⟩
      exact ⟨C, hC, hST.trans hTC, hb⟩
    · rintro S T ⟨C, hC, hSC, hb⟩ ⟨C', hC', hTC', hb'⟩
      refine ⟨C ∪ C', hC.union hC', Set.union_subset_union hSC hTC', fun b hbs => ?_⟩
      have e : b = ⟨C.indicator b.1, indicator_mem_SB b.2 hC⟩ + ⟨Cᶜ.indicator b.1, indicator_mem_SB b.2 hC.compl⟩ := by
        apply Subtype.ext
        funext x
        by_cases hx : x ∈ C <;> simp [hx]
      rw [e, map_add, hb _ (fun x hx => by by_contra hc; exact hx (by simp [hc])), hb', add_zero]
      intro x hx
      have hxC : x ∉ C := by
        intro hc
        exact hx (by simp [hc])
      have hxb : b.1 x ≠ 0 := by
        intro h0
        apply hx
        simp [h0]
      exact (hbs hxb).resolve_left hxC
    · intro x hx
      rw [hsupp] at hx
      have hdet : x.det ≠ 1 := fun h1 => hx (ha x h1)
      obtain ⟨N, hN, hxN, hb⟩ := key x hdet
      exact ⟨N, mem_nhdsWithin_of_mem_nhds (hN.isOpen.mem_nhds hxN), N, hN, subset_rfl, hb⟩
  obtain ⟨C, -, hC, hb⟩ := main
  exact hb a (subset_tsupport _ |>.trans hC)
