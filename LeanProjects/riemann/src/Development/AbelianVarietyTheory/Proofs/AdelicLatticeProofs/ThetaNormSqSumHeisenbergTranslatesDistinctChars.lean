import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeisOrtho

open GlobalTheory.SplitScalar

theorem setIntegral_add_right {G E : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup E] [NormedSpace ℝ E] (Γ : AddSubgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsAddHaarMeasure] (𝓕 : Set G) (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (h : G → E)
    (hp : ∀ γ ∈ Γ, ∀ w, h (γ + w) = h w) (u : G) : ∫ w in 𝓕, h (w + u) ∂μ = ∫ w in 𝓕, h w ∂μ := by
  have h1 : IsAddFundamentalDomain Γ (u +ᵥ 𝓕) μ := h𝓕.vadd_of_comm u
  rw [h𝓕.setIntegral_eq h1 (f := h) fun γ w => hp γ γ.2 w]
  have h2 := (measurePreserving_add_left μ u).setIntegral_image_emb (measurableEmbedding_addLeft u) h 𝓕
  simp only [add_comm _ u]
  exact h2.symm

theorem integral_norm_sq_sum {X ι : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] (s : Finset ι)
    (g : ι → X → ℂ) (c : ι → ℂ) (C : ℝ) (hm : ∀ i, Measurable (g i)) (hC : ∀ i x, ‖g i x‖ ≤ C)
    (hc : ∀ i ∈ s, ‖c i‖ = 1) (h1 : ∀ i ∈ s, ∫ x, ‖g i x‖ ^ 2 ∂ν = 1)
    (h0 : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∫ x, g i x * (starRingEnd ℂ) (g j x) ∂ν = 0) :
    ∫ x, ‖(∑ i ∈ s, c i • g i) x‖ ^ 2 ∂ν = (s.card : ℝ) := by
  classical
  have hi : ∀ i j, Integrable (fun x => g i x * (starRingEnd ℂ) (g j x)) ν := fun i j => by
    refine Integrable.of_bound (((hm i).mul (Complex.continuous_conj.measurable.comp (hm j))).aestronglyMeasurable)
      (C * C) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hC i x) (hC j x) (norm_nonneg _) ((norm_nonneg _).trans (hC i x))
  have e : ∀ x, ((‖(∑ i ∈ s, c i • g i) x‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, (c i * (starRingEnd ℂ) (c j)) * (g i x * (starRingEnd ℂ) (g j x)) := fun x => by
    rw [Complex.ofReal_pow, ← Complex.mul_conj', Finset.sum_apply, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [e]
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => (hi i j).const_mul _,
    Finset.card_eq_sum_ones]
  push_cast
  refine Finset.sum_congr rfl fun i hi' => ?_
  rw [integral_finset_sum _ fun j _ => (hi i j).const_mul _, Finset.sum_eq_single i]
  · rw [integral_const_mul, Complex.mul_conj', hc i hi']
    simp_rw [Complex.mul_conj', ← Complex.ofReal_pow]
    rw [integral_complex_ofReal, h1 i hi']
    simp
  · intro j hj hji
    rw [integral_const_mul, h0 i hi' j hj hji.symm, mul_zero]
  · exact fun h => absurd hi' h

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem heisO_quasi {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (u : WO S T) (γ : WO S T) (hγ : γ ∈ ratL T S)
    (w : WO S T) : heisO ψ S T u f (γ + w) = ψ (-(symplOH S T γ w)) * heisO ψ S T u f w := by
  obtain ⟨γ, rfl⟩ := hγ
  have h := hf.quasi γ (w + u)
  show ψ (symplOH S T (ratW T S γ + w) u) * f (ratW T S γ + w + u) =
    ψ (-(symplOH S T (ratW T S γ) w)) * (ψ (symplOH S T w u) * f (w + u))
  rw [add_assoc, h, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul,
    symplOH_add_left, symplOH_add_right]
  congr 2
  abel

theorem continuous_heisO (hψ : IsCharAF D.host.F ψ) {f : WO S T → ℂ} (hf : Continuous f) (u : WO S T) :
    Continuous (heisO ψ S T u f) :=
  (hψ.1.comp (continuous_const.mul (continuous_symplO S T continuous_id continuous_const))).mul
    (hf.comp (continuous_id.add continuous_const))

theorem norm_heisO (hψ : IsCharAF D.host.F ψ) (f : WO S T → ℂ) (u w : WO S T) :
    ‖heisO ψ S T u f w‖ = ‖f (w + u)‖ := by
  rw [heisO, norm_mul, hψ.2.1, one_mul]

theorem mul_conj_of_norm_one {z : ℂ} (h : ‖z‖ = 1) : z * (starRingEnd ℂ) z = 1 := by
  rw [Complex.mul_conj', h]; simp

theorem thetaNormSq_sum_heisenbergTranslates_distinctChars (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (hψ : IsCharAF D.host.F ψ)
    (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (hμ : IsCovolOne (ratL T S) μ 𝓕) (f : WO S T → ℂ)
    (hf : IsThetaFunO ψ S T f) (hn : nrm2 μ 𝓕 f = 1) (ι : Type) (s : Finset ι) (a : ι → WO S T) (c : ι → ℂ)
    (hc : ∀ i ∈ s, ‖c i‖ = 1)
    (hl : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∃ (l : WO S T) (ε : ℂ), ‖ε‖ = 1 ∧ heisO ψ S T l f = ε • f ∧
      ψ (symplO S T (a i - a j) l) ≠ 1) :
    nrm2 μ 𝓕 (∑ i ∈ s, c i • heisO ψ S T (a i) f) = (s.card : ℝ) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  obtain ⟨hμ, h𝓕, h1⟩ := hμ
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hp : ∀ γ ∈ ratL T S, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
    rintro _ ⟨γ, rfl⟩ w
    exact (congrArg norm (hf.quasi γ w)).trans (by rw [norm_mul, hψ.2.1, one_mul])
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.cont.continuousOn
  have hC' : ∀ w, ‖f w‖ ≤ C := fun w => by
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← hp γ hγ w]
    exact hC _ h
  refine integral_norm_sq_sum (μ.restrict 𝓕) s (fun i => heisO ψ S T (a i) f) c C
    (fun i => (continuous_heisO hψ hf.cont _).measurable) (fun i x => by rw [norm_heisO hψ]; exact hC' _) hc
    (fun i _ => ?_) fun i hi j hj hij => ?_
  · simp_rw [norm_heisO hψ]
    exact (setIntegral_add_right (G := WO S T) (ratL T S) μ 𝓕 h𝓕 (fun w => ‖f w‖ ^ 2)
      (fun γ hγ w => by simp only [hp γ hγ w]) (a i)).trans hn
  · obtain ⟨l, ε, hε, he, hne⟩ := hl i hi j hj hij
    have ev : ∀ b w, ψ (symplOH S T w l) * heisO ψ S T b f (w + l) =
        ψ (symplO S T l b) * (ε * heisO ψ S T b f w) := fun b w => by
      have := congrFun (heisO_comm ψ S T l b f) w
      rw [he, heisO_smul] at this
      exact this
    have key := setIntegral_add_right (G := WO S T) (ratL T S) μ 𝓕 h𝓕
      (fun w => heisO ψ S T (a i) f w * (starRingEnd ℂ) (heisO ψ S T (a j) f w)) (fun γ hγ w => by
        have := mul_conj_of_norm_one (hψ.2.1 (-(symplOH S T γ w)))
        simp only [heisO_quasi hf _ γ hγ, map_mul]
        linear_combination (heisO ψ S T (a i) f w * (starRingEnd ℂ) (heisO ψ S T (a j) f w)) * this) l
    have hκ : ψ (symplO S T (a i - a j) l) * (ψ (symplO S T l (a i)) * (starRingEnd ℂ) (ψ (symplO S T l (a j)))) = 1 := by
      rw [← mul_assoc, ← AddChar.map_add_eq_mul, symplO_sub_left, symplO_skew S T l (a i), symplO_skew S T l (a j),
        show -symplO S T l (a i) - -symplO S T l (a j) + symplO S T l (a i) = symplO S T l (a j) by abel]
      exact mul_conj_of_norm_one (hψ.2.1 _)
    have e : ∀ w, heisO ψ S T (a i) f w * (starRingEnd ℂ) (heisO ψ S T (a j) f w) =
        ψ (symplO S T (a i - a j) l) *
          (heisO ψ S T (a i) f (w + l) * (starRingEnd ℂ) (heisO ψ S T (a j) f (w + l))) := fun w => by
      have e1 := mul_conj_of_norm_one (hψ.2.1 (symplOH S T w l))
      have e2 := mul_conj_of_norm_one hε
      have e3 := ev (a i) w
      have e4 := congrArg (starRingEnd ℂ) (ev (a j) w)
      rw [map_mul, map_mul, map_mul] at e4
      have e5 := congrArg₂ (· * ·) e3 e4
      rw [mul_mul_mul_comm, e1, one_mul] at e5
      rw [e5, mul_mul_mul_comm (ψ _), ← mul_assoc, hκ, one_mul, mul_mul_mul_comm, e2, one_mul]
    have k2 : ∫ w in 𝓕, heisO ψ S T (a i) f w * (starRingEnd ℂ) (heisO ψ S T (a j) f w) ∂μ =
        ψ (symplO S T (a i - a j) l) *
          ∫ w in 𝓕, heisO ψ S T (a i) f w * (starRingEnd ℂ) (heisO ψ S T (a j) f w) ∂μ := by
      conv_rhs => rw [← key, ← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall e)
    have k3 : (ψ (symplO S T (a i - a j) l) - 1) *
        ∫ w in 𝓕, heisO ψ S T (a i) f w * (starRingEnd ℂ) (heisO ψ S T (a j) f w) ∂μ = 0 := by
      rw [sub_mul, one_mul, ← k2, sub_self]
    exact (mul_eq_zero.1 k3).resolve_left (sub_ne_zero.2 hne)

end GlobalTheory.HeisOrtho

end
