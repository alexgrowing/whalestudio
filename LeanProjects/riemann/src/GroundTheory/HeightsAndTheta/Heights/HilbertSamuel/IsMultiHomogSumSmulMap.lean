import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsBoundedAtOfIsBoundedH
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNmSectionsRankBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionSupBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionPointValue
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRealFormsOnPoints
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IntConst
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

namespace SectionL2Lattice

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem measurableSet_mcPts (P : Ideal (MRing ι)) : MeasurableSet (mcPts P) := by
  have h1 : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have h2 : IsClosed {z : (Σ k, ι k) → ℂ | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun f => isClosed_iInter fun _ =>
      isClosed_eq (MvPolynomial.continuous_eval _) continuous_const
  exact h1.measurableSet.inter h2.measurableSet

omit [Fintype K] in

theorem isMultiHomog_sum_smul_map {r : ℕ} {e : K → ℕ} {g : Fin r → MRing ι} (hg : ∀ i, IsMultiHomog (g i) e)
    (c : Fin r → ℂ) : IsMultiHomog (∑ i, c i • map (Int.castRingHom ℂ) (g i)) e := by
  classical
  intro m hm k
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hm)
  exact hg i m (MvPolynomial.support_map_subset _ _ (MvPolynomial.support_smul hi)) k

variable {Ω : Type} [Field Ω]

omit [∀ k, Fintype (ι k)] in

theorem chartLat_le_chartLatNm (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) : chartLat y a τ ≤ chartLatNm y a τ :=
  fun _ hs c hc => isIntegral_algebraMap (R := chartRingZ y c) (A := Ω) (x := ⟨_, hs c hc⟩)

omit [∀ k, Fintype (ι k)] in

theorem finite_chartLat (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) (hfin : Module.Finite ℤ (chartLatNm y a τ)) :
    Module.Finite ℤ (chartLat y a τ) ∧
      Module.finrank ℤ (chartLat y a τ) ≤ Module.finrank ℤ (chartLatNm y a τ) := by
  let f : chartLat y a τ →ₗ[ℤ] chartLatNm y a τ :=
    (AddSubgroup.inclusion (chartLat_le_chartLatNm y a τ)).toIntLinearMap
  have hf : Function.Injective f := AddSubgroup.inclusion_injective (chartLat_le_chartLatNm y a τ)
  have : Module.Finite ℤ (chartLat y a τ) := Module.Finite.of_injective f hf
  exact ⟨inferInstance, LinearMap.finrank_le_finrank_of_injective hf⟩

end SectionL2Lattice

open SectionL2Lattice in

theorem SectionL2Lattice.proof (hV : SectionPointValue.Statement) (hF : RealFormsOnPoints.Statement)
    (hG : L2GramLattice.Statement) (hN : NmSectionsRankBound.Statement) (hB : SectionSupBound.Statement) :
    SectionL2Lattice.Statement := by
  intro K _ ι _ Ω _ _ y D A har hbir hcont μ _ hμ hZ
  obtain ⟨w, hwc, hwrep, hwnorm, hwmul, hwden⟩ := hV K ι Ω y A har.2.1.2.2 hcont
  obtain ⟨hfin, C, -, hC⟩ := hN K ι Ω y D A.a har hbir
  have hae : ∀ᵐ z ∂μ, z ∈ mcPts (mCoordIdeal y) := hμ
  have hrest : μ.restrict (mcPts (mCoordIdeal y)) = μ := Measure.restrict_eq_self_of_ae_mem hae
  have hmeas : ∀ (n : ℕ) (s : chartLat y A.a n), AEStronglyMeasurable (w n s) μ := fun n s => by
    rw [← hrest]; exact (hwc n s).aestronglyMeasurable (measurableSet_mcPts _)
  have hbdd : ∀ (n : ℕ) (s : chartLat y A.a n), ∃ c : ℝ, ∀ᵐ z ∂μ, ‖w n s z‖ ≤ c := fun n s => by
    obtain ⟨c, -, hc⟩ := hB K ι Ω y A n s hcont s.2
    refine ⟨Real.exp c, hae.mono fun z hz => ?_⟩
    rw [← hwnorm n s z hz]
    exact secNormAt_le (Real.exp_pos c).le (isBoundedAt_of_isBoundedH hc hz)
  have hint : ∀ (n : ℕ) (s : chartLat y A.a n), Integrable (fun z => ‖w n s z‖ ^ 2) μ := fun n s => by
    obtain ⟨c, hc⟩ := hbdd n s
    refine (integrable_const (c ^ 2)).mono' ((hmeas n s).norm.pow 2) (hc.mono fun z hz => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) hz 2
  have key : ∀ n : ℕ, ∃ φ : chartLat y A.a n →+ EuclideanSpace ℝ (Fin (Module.finrank ℤ (chartLat y A.a n))),
      Function.Injective φ ∧ DiscreteTopology (imageLattice φ) ∧
      (∀ [DiscreteTopology (imageLattice φ)], IsZLattice ℝ (imageLattice φ)) ∧
      ∀ s, ‖φ s‖ = Real.sqrt (∫ z, ‖w n s z‖ ^ 2 ∂μ) := by
    intro n
    have : Module.Finite ℤ (chartLat y A.a n) := (finite_chartLat y A.a n (hfin n)).1
    have : Module.Free ℤ (chartLat y A.a n) := Module.free_of_finite_type_torsion_free'
    refine hG _ _ μ (w n) (hmeas n) (hbdd n) ?_
    intro r x hx c hc
    obtain ⟨e, e', h, g, hh, hg, he, hy, hgy⟩ := hwden n r x
    refine hF K ι Ω y (D + 1) e r g har hg ?_ c ?_
    · have h1 : LinearIndependent ℤ (fun i => (x i : Ω)) :=
        hx.map' (chartLat y A.a n).subtype.toIntLinearMap (LinearMap.ker_eq_bot.2 Subtype.val_injective)
      have h2 := h1.map' (LinearMap.mulRight ℤ (aeval y h))
        (LinearMap.ker_eq_bot.2 (mul_left_injective₀ hy))
      convert h2 using 1 <;> first | rfl | (funext i; simp [hgy i])
    · intro z hz
      have hF' := hZ e (∑ i, (c i : ℂ) • map (Int.castRingHom ℂ) (g i)) (isMultiHomog_sum_smul_map hg _) ?_ z hz
      · simpa only [map_sum, smul_eval] using hF'
      · filter_upwards [hc, hae] with z hz0 hzP
        rw [map_sum]
        simp only [smul_eval]
        calc ∑ i, (c i : ℂ) * eval z (map (Int.castRingHom ℂ) (g i))
            = ∑ i, (c i : ℂ) * (w n (x i) z * eval z (map (Int.castRingHom ℂ) h) * (A.h z : ℂ) ^ n) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [hwrep n (x i) e e' (g i) h z (hg i) hh he (hgy i) hzP]
          _ = (∑ i, (c i : ℂ) * w n (x i) z) * (eval z (map (Int.castRingHom ℂ) h) * (A.h z : ℂ) ^ n) := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun i _ => ?_
              ring
          _ = 0 := by rw [hz0, zero_mul]
  choose φ hinj hdisc hlat hnorm using key
  refine ⟨fun n => Module.finrank ℤ (chartLat y A.a n), φ, hinj, hdisc, fun n _ => hlat n, ?_, ?_, ?_, ?_⟩
  · intro n c s hc hs
    rw [hnorm, ← Real.sqrt_sq hc]
    refine Real.sqrt_le_sqrt ?_
    calc ∫ z, ‖w n s z‖ ^ 2 ∂μ ≤ ∫ _, c ^ 2 ∂μ :=
          integral_mono_of_nonneg (ae_of_all _ fun z => by positivity) (integrable_const _)
            (hae.mono fun z hz => by
              show ‖w n s z‖ ^ 2 ≤ c ^ 2
              rw [← hwnorm n s z hz]
              exact pow_le_pow_left₀ (secNormAt_nonneg _ _ _ _ _)
                (secNormAt_le hc (isBoundedAt_of_isBoundedH hs hz)) 2)
      _ = c ^ 2 := by simp
  · intro n k s t st ht hst
    rw [hnorm, hnorm]
    refine Real.sqrt_le_sqrt (integral_mono_of_nonneg (ae_of_all _ fun z => by positivity) (hint n s)
      (hae.mono fun z hz => ?_))
    have h1 : ‖w k t z‖ ≤ 1 := by
      rw [← hwnorm k t z hz]
      refine secNormAt_le zero_le_one fun dg dh g h hg hh hd he => ?_
      rw [one_mul]
      exact ht dg dh g h z hg hh hd he hz
    show ‖w (n + k) st z‖ ^ 2 ≤ ‖w n s z‖ ^ 2
    rw [hwmul n k s t st hst z hz, norm_mul, mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) h1)
  · exact ⟨C, fun n => le_trans (by exact_mod_cast (finite_chartLat y A.a n (hfin n)).2) (hC n)⟩
  · intro n s
    rw [hnorm, sectionL2Norm]
    congr 1
    refine integral_congr_ae (hae.mono fun z hz => ?_)
    simp only [hwnorm n s z hz]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
