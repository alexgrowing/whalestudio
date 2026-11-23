import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OccursBasics
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactorAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OlocEx
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocFlath
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.LocUApply
import Development.AutomorphicArithmetic.TwistedTraces.SummandLeClosureSpanLocalTypeImages

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf
open scoped InnerProductSpace

section Abs

variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X]

private theorem fixed_of_inner {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep G H) (τ : Representation ℂ G X) (hτ : ∀ x, IsOpen {g | τ g x = x})
    (J : Subgroup G) (hJ : IsCompact (J : Set G)) (f : X →ₗ[ℂ] H) (hf : ∀ g x, f (τ g x) = π g (f x))
    (v : H) (hv : ∀ u ∈ J, π u v = v) (x : X) (h0 : ⟪v, f x⟫_ℂ ≠ 0) :
    fixedVectors τ J ≠ ⊥ := by
  have hfin : ((fun g => τ g x) '' (J : Set G)).Finite := by
    obtain ⟨t, -, ht⟩ := hJ.elim_nhds_subcover (fun g => {h | τ h x = τ g x}) fun g _ => by
      have h1 : IsOpen ((fun h => g⁻¹ * h) ⁻¹' {g | τ g x = x}) := (hτ x).preimage (by fun_prop)
      refine Filter.mem_of_superset (h1.mem_nhds (by simp)) fun h hh => ?_
      have h2 : τ (g⁻¹ * h) x = x := hh
      show τ h x = τ g x
      conv_rhs => rw [← h2]
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    refine (t.finite_toSet.image fun g => τ g x).subset ?_
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨i, hi, h⟩ := Set.mem_iUnion₂.1 (ht hg)
    exact ⟨i, hi, (h : τ g x = τ i x).symm⟩
  classical
  set S := hfin.toFinset with hS
  have hm : ∀ y, y ∈ S ↔ ∃ g ∈ J, τ g x = y := fun y => by simp [hS]
  have hpos : 0 < S.card := Finset.card_pos.2 ⟨x, (hm x).2 ⟨1, J.one_mem, by simp⟩⟩
  have hc' : (S.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hpos.ne'
  have hst : ∀ u ∈ J, ∀ y ∈ S, τ u y ∈ S := fun u hu y hy => by
    obtain ⟨g, hg, rfl⟩ := (hm y).1 hy
    exact (hm _).2 ⟨u * g, J.mul_mem hu hg, by rw [map_mul]; rfl⟩
  have hy : ∀ y ∈ S, ⟪v, f y⟫_ℂ = ⟪v, f x⟫_ℂ := fun y hy => by
    obtain ⟨g, hg, rfl⟩ := (hm y).1 hy
    rw [hf]
    have h1 := UnitaryRep.inner_map_map π g v (f x)
    rwa [hv g hg] at h1
  have hmem : (S.card : ℂ)⁻¹ • ∑ y ∈ S, y ∈ fixedVectors τ J := fun u hu => by
    rw [map_smul, map_sum]
    congr 1
    refine Finset.sum_nbij' (τ u) (τ u⁻¹) (hst u hu) (hst _ (J.inv_mem hu)) (fun y _ => ?_) (fun y _ => ?_) fun _ _ => rfl
    · rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
    · rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  intro hb
  rw [hb, Submodule.mem_bot] at hmem
  have h1 : ⟪v, f ((S.card : ℂ)⁻¹ • ∑ y ∈ S, y)⟫_ℂ = ⟪v, f x⟫_ℂ := by
    rw [map_smul, inner_smul_right, map_sum, inner_sum, Finset.sum_congr rfl hy, Finset.sum_const,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc', one_mul]
  rw [hmem, map_zero, inner_zero_right] at h1
  exact h0 h1.symm

private theorem trace_ne [MeasurableSpace G] [BorelSpace G] (m : Measure G) [m.IsHaarMeasure]
    (τ : Representation ℂ G X) (J : Subgroup G) (hJ : CO J) (hx : fixedVectors τ J ≠ ⊥) {s : ℂ}
    (hs : HasTrace m τ ((J : Set G).indicator 1) s) : s ≠ 0 := by
  obtain ⟨A, hA, hfd, rfl⟩ := hs
  have hmeas : MeasurableSet (J : Set G) := hJ.2.measurableSet
  set c : ℂ := (m.real (J : Set G) : ℂ) with hcdef
  have hc : c ≠ 0 := by
    have h1 : 0 < m (J : Set G) := hJ.2.measure_pos m ⟨1, J.one_mem⟩
    have h2 : m (J : Set G) < ⊤ := hJ.1.measure_lt_top
    exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_pos h1.ne' h2.ne).ne'
  have hfix : ∀ y ∈ fixedVectors τ J, A y = c • y := fun y hy => by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, (hA y l).2, map_smul, smul_eq_mul, sub_eq_zero]
    have e : (fun g => (J : Set G).indicator (1 : G → ℂ) g * l (τ g y)) = (J : Set G).indicator (fun _ => l y) := by
      funext g
      by_cases hg : g ∈ (J : Set G)
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, Pi.one_apply, one_mul, hy g hg]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, zero_mul]
    rw [e, integral_indicator hmeas, setIntegral_const]
    simp [hcdef]
  have hran : ∀ v, A v ∈ fixedVectors τ J := fun v h hh => by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, sub_eq_zero]
    change (l ∘ₗ τ h) (A v) = _
    rw [(hA v (l ∘ₗ τ h)).2, (hA v l).2]
    refine Eq.trans ?_ (integral_mul_left_eq_self (μ := m) (fun g => (J : Set G).indicator (1 : G → ℂ) g * l (τ g v)) h)
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have hi : (J : Set G).indicator (1 : G → ℂ) (h * g) = (J : Set G).indicator (1 : G → ℂ) g := by
      by_cases hg : g ∈ J
      · rw [Set.indicator_of_mem (show h * g ∈ (J : Set G) from J.mul_mem hh hg),
          Set.indicator_of_mem (show g ∈ (J : Set G) from hg)]
        rfl
      · rw [Set.indicator_of_notMem (show h * g ∉ (J : Set G) from fun e => hg ((Subgroup.mul_mem_cancel_left J hh).1 e)),
          Set.indicator_of_notMem (show g ∉ (J : Set G) from hg)]
    show (J : Set G).indicator (1 : G → ℂ) g * l (τ h (τ g v)) = (J : Set G).indicator (1 : G → ℂ) (h * g) * l (τ (h * g) v)
    rw [hi, map_mul, Module.End.mul_apply]
  obtain ⟨x, hxf, hx0⟩ := (Submodule.ne_bot_iff _).1 hx
  have hxr : x ∈ LinearMap.range A :=
    ⟨c⁻¹ • x, by rw [map_smul, hfix x hxf, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩
  have hres : A.restrict (p := LinearMap.range A) (q := LinearMap.range A) (fun v _ => LinearMap.mem_range_self A v) =
      c • LinearMap.id := by
    refine LinearMap.ext fun y => Subtype.ext ?_
    obtain ⟨z, hz⟩ := y.2
    exact hfix y.1 (hz ▸ hran z)
  haveI : FiniteDimensional ℂ (LinearMap.range A) := hfd
  haveI : Nontrivial (LinearMap.range A) :=
    ⟨⟨⟨x, hxr⟩, 0, fun e => hx0 (congrArg Subtype.val e)⟩⟩
  rw [hres, map_smul, LinearMap.trace_id, smul_eq_mul]
  exact mul_ne_zero hc (Nat.cast_ne_zero.2 Module.finrank_pos.ne')

end Abs

theorem UpperTheory.ConvolutionTheory.T.unitTrace :
    UpperTheory.ConvolutionTheory.T.UnitTrace := by
  intro K _ _ n μ _ V hV w _ _ m hm τ J hocc hJ hne
  haveI := hm
  have hcl : IsClosed (J : Set (Gw n w)) := J.isClosed_of_isOpen hJ.2
  have hind : ∀ u ∈ J, ∀ g, (J : Set (Gw n w)).indicator (1 : Gw n w → ℂ) (u * g) = (J : Set (Gw n w)).indicator 1 g ∧
      (J : Set (Gw n w)).indicator (1 : Gw n w → ℂ) (g * u) = (J : Set (Gw n w)).indicator 1 g := by
    intro u hu g
    have h1 : u * g ∈ J ↔ g ∈ J := Subgroup.mul_mem_cancel_left J hu
    have h2 : g * u ∈ J ↔ g ∈ J := Subgroup.mul_mem_cancel_right J hu
    by_cases hg : g ∈ J
    · rw [Set.indicator_of_mem (show u * g ∈ (J : Set (Gw n w)) from h1.2 hg),
        Set.indicator_of_mem (show g * u ∈ (J : Set (Gw n w)) from h2.2 hg),
        Set.indicator_of_mem (show g ∈ (J : Set (Gw n w)) from hg)]
      exact ⟨rfl, rfl⟩
    · rw [Set.indicator_of_notMem (show u * g ∉ (J : Set (Gw n w)) from fun e => hg (h1.1 e)),
        Set.indicator_of_notMem (show g * u ∉ (J : Set (Gw n w)) from fun e => hg (h2.1 e)),
        Set.indicator_of_notMem (show g ∉ (J : Set (Gw n w)) from hg)]
      exact ⟨rfl, rfl⟩
  have htest : Test ((J : Set (Gw n w)).indicator (1 : Gw n w → ℂ)) := by
    refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, HasCompactSupport.intro hJ.1 fun x hx => Set.indicator_of_notMem hx _⟩
    by_cases hx : x ∈ (J : Set (Gw n w))
    · exact ⟨_, hJ.2, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl⟩
    · exact ⟨_, hcl.isOpen_compl, hx, fun y hy => by rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
  have hfix : fixedVectors τ.ρ J ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
    have hvJ : ∀ u ∈ J, locU μ w u v = v := by
      have h1 : v ∈ fixU (locU μ w) J := by
        rw [fixU_locU]
        exact hv.2
      exact h1
    by_contra hbot
    have hle : spanAll τ.ρ (locU μ w) V ≤ (ℂ ∙ v)ᗮ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨f, hf, x, rfl⟩
      refine Submodule.mem_orthogonal_singleton_iff_inner_right.2 ?_
      by_contra h
      exact fixed_of_inner (locU μ w) τ.ρ (fun x => τ.smooth x) J hJ.1 f hf.map v hvJ x h hbot
    have h2 := Submodule.topologicalClosure_minimal _ hle (Submodule.isClosed_orthogonal _)
      (UpperTheory.summand_le_closure_span_local_type_images K n μ V w τ hV hocc hv.1)
    exact hv0 (inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_right.1 h2))
  obtain ⟨-, -, h3⟩ := UpperTheory.ConvolutionTheory.C.occursBasics K n μ V w m hV
  obtain ⟨s, hs⟩ := h3 τ hocc _ htest
  exact ⟨hfix, htest, hind, s, trace_ne m τ.ρ J hJ hfix hs, hs⟩
