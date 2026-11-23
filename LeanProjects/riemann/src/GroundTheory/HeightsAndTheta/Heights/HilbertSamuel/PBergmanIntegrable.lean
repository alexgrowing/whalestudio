import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergmanIntegrable
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanSectionPairing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M SectionPairing
open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace BergmanIntegrable

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}

def SectionInnerProductSpace (V : Submodule ℂ (Fin A.n → X → ℂ)) : Type := V

variable (V : Submodule ℂ (Fin A.n → X → ℂ))

instance : AddCommGroup (SectionInnerProductSpace V) := inferInstanceAs (AddCommGroup V)

instance : Module ℂ (SectionInnerProductSpace V) := inferInstanceAs (Module ℂ V)

instance [FiniteDimensional ℂ V] : FiniteDimensional ℂ (SectionInnerProductSpace V) :=
  inferInstanceAs (FiniteDimensional ℂ V)

def val : SectionInnerProductSpace V →ₗ[ℂ] (Fin A.n → X → ℂ) := V.subtype

theorem val_mem (v : SectionInnerProductSpace V) : val V v ∈ V := (show V from v).2

variable [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  (W : Weight L) (dV : SmoothVolume A) (n : ℕ)

omit [CompactSpace X] [T2Space X] [BorelSpace X] in

theorem integral_pairing_self (s : Fin A.n → X → ℂ) :
    ∫ x, pairing W n s s x ∂dV.μ = ((sectionL2NormSq W dV n s : ℝ) : ℂ) := by
  simp_rw [pairing_self]
  exact integral_ofReal

theorem pairing_integrable {s t : Fin A.n → X → ℂ} (hs : s ∈ L.sections n)
    (ht : t ∈ L.sections n) : Integrable (pairing W n s t) dV.μ := by
  have := dV.isProb
  exact integrableOn_univ.1
    ((pairing_continuous W n hs ht).continuousOn.integrableOn_compact isCompact_univ)

@[instance_reducible]
def core (hV : V ≤ L.sections n) : InnerProductSpace.Core ℂ (SectionInnerProductSpace V) where
  inner v w := ∫ x, pairing W n (val V v) (val V w) x ∂dV.μ
  conj_inner_symm v w := by
    show conj (∫ x, pairing W n (val V w) (val V v) x ∂dV.μ) =
      ∫ x, pairing W n (val V v) (val V w) x ∂dV.μ
    rw [← integral_conj]
    congr 1
    funext x
    simp only [pairing, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  re_inner_nonneg v := by
    show 0 ≤ RCLike.re (∫ x, pairing W n (val V v) (val V v) x ∂dV.μ)
    rw [integral_pairing_self, RCLike.re_to_complex, Complex.ofReal_re]
    exact integral_nonneg fun x ↦ ptNormSq_nonneg W n _ x
  add_left u v w := by
    show ∫ x, pairing W n (val V (u + v)) (val V w) x ∂dV.μ =
      ∫ x, pairing W n (val V u) (val V w) x ∂dV.μ + ∫ x, pairing W n (val V v) (val V w) x ∂dV.μ
    rw [← integral_add (pairing_integrable W dV n (hV (val_mem V u)) (hV (val_mem V w)))
      (pairing_integrable W dV n (hV (val_mem V v)) (hV (val_mem V w))), map_add]
    congr 1
    funext x
    simp only [pairing, Pi.add_apply, map_add]
    ring
  smul_left u w r := by
    show ∫ x, pairing W n (val V (r • u)) (val V w) x ∂dV.μ =
      conj r * ∫ x, pairing W n (val V u) (val V w) x ∂dV.μ
    rw [← integral_const_mul, map_smul]
    congr 1
    funext x
    simp only [pairing, Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  definite v h := by
    have hs : val V v ∈ L.sections n := hV (val_mem V v)
    have hl : sectionL2NormSq W dV n (val V v) = 0 := by
      have h' : ((sectionL2NormSq W dV n (val V v) : ℝ) : ℂ) = 0 := by
        rw [← integral_pairing_self]
        exact h
      exact_mod_cast h'
    have hpt : ∀ x, ptNormSq W n (val V v) x = 0 := by
      intro x
      by_contra hx
      have := dV.isProb
      have := isOpenPosMeasure dV
      have hpos := (ptNormSq_continuous W n hs).integral_pos_of_hasCompactSupport_nonneg_nonzero
        (μ := dV.μ) (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))
        (fun y ↦ ptNormSq_nonneg W n _ y) hx
      rw [sectionL2NormSq] at hl
      linarith
    have hzero : val V v = 0 := by
      funext j x
      by_cases hx : x ∈ (A.chart j).source
      · have h1 := pairing_eq W n hs hs j hx
        rw [pairing_self, hpt x, Complex.conj_mul'] at h1
        have h2 : ‖val V v j x‖ ^ 2 * Real.exp (-(n : ℝ) * W.φ j x) = 0 := by
          exact_mod_cast h1.symm
        have h3 := (mul_eq_zero.1 h2).resolve_right (Real.exp_pos _).ne'
        simpa using h3
      · exact hs.2.2 j x hx
    exact (Subtype.ext hzero : (show V from v) = 0)

theorem bergman_eq_sum (hV : V ≤ L.sections n) [FiniteDimensional ℂ V] :
    ∃ (m : ℕ) (u : Fin m → Fin A.n → X → ℂ), (∀ i, u i ∈ V) ∧
      ∀ x, bergman W dV V n x = ∑ i, ptNormSq W n (u i) x := by
  let cd : InnerProductSpace.Core ℂ (SectionInnerProductSpace V) := core V W dV n hV
  let : NormedAddCommGroup (SectionInnerProductSpace V) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : InnerProductSpace ℂ (SectionInnerProductSpace V) := InnerProductSpace.ofCore cd.toCore
  have hinner : ∀ v w : SectionInnerProductSpace V,
      ⟪v, w⟫_ℂ = ∫ x, pairing W n (val V v) (val V w) x ∂dV.μ := fun _ _ ↦ rfl
  have hnorm : ∀ v : SectionInnerProductSpace V, sectionL2NormSq W dV n (val V v) = ‖v‖ ^ 2 := fun v ↦ by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) v]
    show _ = RCLike.re (∫ x, pairing W n (val V v) (val V v) x ∂dV.μ)
    rw [integral_pairing_self, RCLike.re_to_complex, Complex.ofReal_re]
  let b := stdOrthonormalBasis ℂ (SectionInnerProductSpace V)
  refine ⟨_, fun i ↦ val V (b i), fun i ↦ val_mem V (b i), fun x ↦ ?_⟩
  let ev : SectionInnerProductSpace V →ₗ[ℂ] ℂ :=
    (LinearMap.proj (R := ℂ) x).comp ((LinearMap.proj (R := ℂ) (chartIdx A x)).comp (val V))
  set w := Real.exp (-(n : ℝ) * W.φ (chartIdx A x) x) with hw
  have hw0 : 0 ≤ w := (Real.exp_pos _).le
  have hpt : ∀ v : SectionInnerProductSpace V, ptNormSq W n (val V v) x = ‖ev v‖ ^ 2 * w := fun _ ↦ rfl
  let r : SectionInnerProductSpace V := ∑ i, conj (ev (b i)) • b i
  have hr : ∀ v, ev v = ⟪r, v⟫_ℂ := fun v ↦ by
    calc ev v = ev (∑ i, ⟪b i, v⟫_ℂ • b i) := by rw [b.sum_repr']
      _ = ∑ i, ev (b i) * ⟪b i, v⟫_ℂ := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, smul_eq_mul, mul_comm]
      _ = ⟪r, v⟫_ℂ := by
          rw [sum_inner]
          exact Finset.sum_congr rfl fun i _ ↦ by rw [inner_smul_left, Complex.conj_conj]
  have hrn : ‖r‖ ^ 2 = ∑ i, ‖ev (b i)‖ ^ 2 := by
    rw [← b.sum_sq_norm_inner_right r]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← inner_conj_symm, ← hr, Complex.norm_conj]
  have hsum : ∑ i, ptNormSq W n (val V (b i)) x = ‖r‖ ^ 2 * w := by
    rw [hrn, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ hpt _
  have hle : ∀ s : V, ptNormSq W n (s : Fin A.n → X → ℂ) x / sectionL2NormSq W dV n s ≤ ‖r‖ ^ 2 * w := by
    intro s
    let v : SectionInnerProductSpace V := s
    change ptNormSq W n (val V v) x / sectionL2NormSq W dV n (val V v) ≤ ‖r‖ ^ 2 * w
    rw [hpt, hnorm]
    have hcs : ‖ev v‖ ≤ ‖r‖ * ‖v‖ := by rw [hr]; exact norm_inner_le_norm r v
    rcases eq_or_ne ‖v‖ 0 with h0 | h0
    · rw [h0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero]
      positivity
    · rw [div_le_iff₀ (by positivity)]
      have h2 : ‖ev v‖ ^ 2 ≤ (‖r‖ * ‖v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hcs 2
      nlinarith [mul_le_mul_of_nonneg_right h2 hw0]
  have hattain : ptNormSq W n (val V r) x / sectionL2NormSq W dV n (val V r) = ‖r‖ ^ 2 * w := by
    have hn : ‖⟪r, r⟫_ℂ‖ = ‖r‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      simp
    rw [hpt, hnorm, hr, hn]
    rcases eq_or_ne ‖r‖ 0 with h0 | h0
    · simp [h0]
    · field_simp
  rw [hsum]
  refine le_antisymm (ciSup_le hle) ?_
  exact le_ciSup_of_le ⟨_, forall_mem_range.2 hle⟩ (show V from r) hattain.ge

theorem proof : BergmanIntegrable.Statement := by
  intro D X _ _ _ _ _ A L W dV n V _ hV
  obtain ⟨m, u, hu, h⟩ := bergman_eq_sum V W dV n hV
  have := dV.isProb
  have hc : Continuous (bergman W dV V n) := by
    rw [show bergman W dV V n = fun x ↦ ∑ i, ptNormSq W n (u i) x from funext h]
    exact continuous_finsetSum _ fun i _ ↦ ptNormSq_continuous W n (hV (hu i))
  exact integrableOn_univ.1 (hc.continuousOn.integrableOn_compact isCompact_univ)

end BergmanIntegrable

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
