import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.StepFin
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

private theorem out_mem_iff {G : Type*} [Group G] (J : Subgroup G) (y : G) (c : G ⧸ J) :
    c.out ∈ {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b} ↔ c ∈ {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * y)} := by
  constructor
  · rintro ⟨a, ha, b, hb, e⟩
    refine ⟨a, ha, ?_⟩
    rw [← QuotientGroup.out_eq' c, e]
    exact QuotientGroup.eq.2 (by simpa [mul_assoc] using J.inv_mem hb)
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul J (k * y)
    exact ⟨k, hk, j, j.2, hj⟩

private theorem dc_support {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G) (y : G)
    (hc : IsCompact (J : Set G)) :
    HasCompactSupport ({g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b}.indicator (1 : G → ℂ)) := by
  have hDc : IsCompact {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b} := by
    have : {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b} = (fun p : G × G => p.1 * y * p.2) ''
        ((J : Set G) ×ˢ (J : Set G)) := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_prod, SetLike.mem_coe, Prod.exists]
      exact ⟨fun ⟨a, ha, b, hb, e⟩ => ⟨a, b, ⟨ha, hb⟩, e.symm⟩, fun ⟨a, b, ⟨ha, hb⟩, e⟩ => ⟨a, ha, b, hb, e.symm⟩⟩
    rw [this]
    exact (hc.prod hc).image (by fun_prop)
  exact HasCompactSupport.intro hDc fun x hx => Set.indicator_of_notMem hx _

private theorem dc_inv {G : Type*} [Group G] (J : Subgroup G) (y : G) :
    ∀ k ∈ J, ∀ x, {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b}.indicator (1 : G → ℂ) (x * k) =
      {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b}.indicator 1 x := by
  have hmem : ∀ k ∈ J, ∀ x, x * k ∈ {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b} ↔
      x ∈ {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b} := by
    intro k hk x
    constructor
    · rintro ⟨a, ha, b, hb, e⟩
      exact ⟨a, ha, b * k⁻¹, J.mul_mem hb (J.inv_mem hk), by rw [← mul_assoc, ← e]; simp⟩
    · rintro ⟨a, ha, b, hb, e⟩
      exact ⟨a, ha, b * k, J.mul_mem hb hk, by rw [e]; simp [mul_assoc]⟩
  intro k hk x
  by_cases hx : x ∈ {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b}
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hmem k hk x).2 hx)]; rfl
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem fun q => hx ((hmem k hk x).1 q)]

private theorem dc_sum {G E : Type*} [Group G] [AddCommMonoid E] [Module ℂ E] (J : Subgroup G) (y : G) (ρ : G → E) :
    (∑ᶠ c : G ⧸ J, {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b}.indicator (1 : G → ℂ) c.out • ρ c.out) =
      ∑ᶠ c ∈ {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * y)}, ρ c.out := by
  rw [finsum_mem_def]
  refine finsum_congr fun c => ?_
  by_cases hcC : c ∈ {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * y)}
  · rw [Set.indicator_of_mem hcC, Set.indicator_of_mem ((out_mem_iff J y c).2 hcC)]
    simp
  · rw [Set.indicator_of_notMem hcC, Set.indicator_of_notMem fun q => hcC ((out_mem_iff J y c).1 q)]
    simp

theorem UpperTheory.Ofin_doubleCoset_indicator_eq_Hop :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure]
      (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))) (y : GL (Fin n) (w.adicCompletion K)),
      IsOpen (J : Set (GL (Fin n) (w.adicCompletion K))) → IsCompact (J : Set (GL (Fin n) (w.adicCompletion K))) →
      ∀ (r : AdelicGLn.FiniteAdelicGL K n → ℂ), Free w r → ∀ e₀ e₁ : TF K n,
        (∀ x, e₀ x = r x * (J : Set (GL (Fin n) (w.adicCompletion K))).indicator 1 (cf w x)) →
        (∀ x, e₁ x = r x * {g : GL (Fin n) (w.adicCompletion K) | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b}.indicator 1 (cf w x)) →
        Ofin μ m e₁ = Hop μ w J y ∘L Ofin μ m e₀ := by
  intro K _ _ n hn μ _ m _ w J y ho hc r hr e₀ e₁ h0 h1
  obtain ⟨hfix, heq⟩ := UpperTheory.ConvolutionTheory.GM.stepFin K n hn μ m w J ho _ (dc_support J y hc) (dc_inv J y) r hr e₀ e₁ h0 h1
  refine ContinuousLinearMap.ext fun u => ?_
  rw [heq, dc_sum J y (rhoL μ w)]
  have hp : prj (fixL μ w J) (Ofin μ m e₀ u) = Ofin μ m e₀ u :=
    (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ (J.map (AdelicGLn.localEmbedding w))).2.2.2.1 _ (hfix u)
  simp only [Hop, ContinuousLinearMap.comp_apply, hp]
