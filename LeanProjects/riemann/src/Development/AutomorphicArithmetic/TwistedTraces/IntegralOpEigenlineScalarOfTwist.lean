import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TvDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.TraceLine
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

theorem UpperTheory.integralOp_eigenline_scalar_of_twist :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (m : Measure G)
        [m.IsHaarMeasure] (τ : SmIrr G) (I : τ.V ≃ₗ[ℂ] τ.V) (s : G →* G) (J : Subgroup G) (χ : G → ℂ) (A : τ.V →ₗ[ℂ] τ.V) (e : τ.V),
        CO J → IsChr J χ → m J = 1 → IsIntegralOp m τ.ρ ((J : Set G).indicator fun x => conj (χ x)) A →
        e ≠ 0 → (∀ g ∈ J, τ.ρ g e = χ g • e) → (∀ x : τ.V, (∀ g ∈ J, τ.ρ g x = χ g • x) → ∃ c : ℂ, x = c • e) →
        (∀ x ∈ J, s x ∈ J ∧ χ (s x) = χ x) → (∀ g x, I (τ.ρ g x) = τ.ρ (s g) (I x)) →
        ∃ t : ℂ, t ≠ 0 ∧ HasTwTrace m τ I ((J : Set G).indicator fun x => conj (χ x)) t := by
  intro G _ _ _ _ _ m _ τ I s J χ A e hCO hχ hm hA he hty hone hs hI
  have hJo : IsOpen (J : Set G) := hCO.2
  have hcc : ∀ g ∈ J, conj (χ g) * χ g = 1 := by
    intro g hg
    rw [Complex.conj_mul', hχ.2.1 g hg]
    simp

  have hAe : A e = e := by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, sub_eq_zero, (hA e l).2]
    have h1 : (fun g => ((J : Set G).indicator (fun x => conj (χ x)) g) * l (τ.ρ g e)) =
        (J : Set G).indicator fun _ => l e := by
      funext g
      by_cases hg : g ∈ (J : Set G)
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, hty g hg, map_smul, smul_eq_mul,
          ← mul_assoc, hcc g hg, one_mul]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, zero_mul]
    rw [h1, integral_indicator_const _ hJo.measurableSet]
    simp [Measure.real, hm]

  have hAty : ∀ x, ∀ u ∈ J, τ.ρ u (A x) = χ u • A x := by
    intro x u hu
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    have h1 := (hA x (l ∘ₗ τ.ρ u)).2
    have h2 := (hA x l).2
    rw [map_sub, map_smul, sub_eq_zero, h2, smul_eq_mul, ← integral_const_mul,
      ← integral_mul_left_eq_self (fun g => χ u * (((J : Set G).indicator (fun x => conj (χ x)) g) * l (τ.ρ g x))) u]
    refine h1.trans (integral_congr_ae (Filter.Eventually.of_forall fun g => ?_))
    have h3 : χ u * (J : Set G).indicator (fun x => conj (χ x)) (u * g) =
        (J : Set G).indicator (fun x => conj (χ x)) g := by
      by_cases hg : g ∈ J
      · have hug : u * g ∈ (J : Set G) := J.mul_mem hu hg
        have hg' : g ∈ (J : Set G) := hg
        rw [Set.indicator_of_mem hug, Set.indicator_of_mem hg', hχ.2.2 u hu g hg, map_mul, ← mul_assoc,
          mul_comm (χ u), hcc u hu, one_mul]
      · have hug : u * g ∉ (J : Set G) := fun h => hg ((J.mul_mem_cancel_left hu).1 h)
        have hg' : g ∉ (J : Set G) := hg
        rw [Set.indicator_of_notMem hug, Set.indicator_of_notMem hg', mul_zero]
    simp only [← mul_assoc, h3, map_mul, LinearMap.comp_apply, Module.End.mul_apply]

  obtain ⟨a, ha⟩ := hone (I.symm e) (by
    intro g hg
    apply I.injective
    rw [hI, map_smul, LinearEquiv.apply_symm_apply, hty _ (hs g hg).1, (hs g hg).2])
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact he (by simpa using ha)
  have hIe : I e = a⁻¹ • e := by
    have h1 : e = a • I e := by
      have := congrArg I ha
      rwa [LinearEquiv.apply_symm_apply, map_smul] at this
    rw [eq_inv_smul_iff₀ ha0]
    exact h1.symm
  obtain ⟨t, ht, htr⟩ := UpperTheory.V.Z.Tf.L4.traceLine τ.V (Submodule.span ℂ {e}) (finrank_span_singleton he) A 1 one_ne_zero
    (fun v => by
      obtain ⟨c, hc⟩ := hone (A v) (hAty v)
      rw [hc]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e))
    (fun v hv => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
      rw [map_smul, hAe, one_smul])
    I
    (fun v hv => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
      rw [map_smul, hIe]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)))
  exact ⟨t, ht, A, hA, htr⟩
