import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZeroSetOpenMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteMapOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Filter Topology

noncomputable section

theorem exists_eval_ne_zero_of_isOpen {d : ℕ} {P : MvPolynomial (Fin d) ℂ} (hP : P ≠ 0)
    {S : Set (Fin d → ℂ)} (hS : IsOpen S) (hne : S.Nonempty) : ∃ y ∈ S, eval y P ≠ 0 := by
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hS y₀ hy₀
  by_contra h
  push Not at h
  apply hP
  have hinf : ∀ i, (Metric.ball (y₀ i) r).Infinite := fun i =>
    infinite_of_mem_nhds (y₀ i) (Metric.ball_mem_nhds _ hr)
  refine (funext_set_iff (p := P) (q := 0) _ hinf).mpr fun y hy => ?_
  rw [map_zero]
  exact h y (hball (by rwa [ball_pi _ hr]))

theorem eval_linPoly {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (z : Fin n → ℂ) :
    (fun i => eval z (GroundTheory.Heights₂.Heights.ComplexSets.linPoly A i)) = A.mulVec z := by
  ext i
  simp [GroundTheory.Heights₂.Heights.ComplexSets.linPoly, Matrix.mulVec, dotProduct]

theorem finrank_real_fin_complex (d : ℕ) : Module.finrank ℝ (Fin d → ℂ) = 2 * d := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Complex.finrank_real_complex, smul_eq_mul, mul_comm]

theorem ZeroSetOpenMass.proof
    (hG : GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.Statement)
    (hD : GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.Statement)
    (hF : FiniteMapOpen.Statement) : ZeroSetOpenMass.Statement := by
  intro n d W hW hdim x O hO hxO hxZ
  obtain ⟨A, hA⟩ := (hG n d W hW hdim).2.1
  obtain ⟨P, hP0, hPcov⟩ := hD n d W A hW hdim hA
  have hopen := hF n d W (GroundTheory.Heights₂.Heights.ComplexSets.linPoly A) hW hA.injective hA.finite x hxZ O
    (hO.mem_nhds hxO)
  have hfun : (fun z : Fin n → ℂ => fun i => eval z (GroundTheory.Heights₂.Heights.ComplexSets.linPoly A i)) =
      fun z => A.mulVec z := funext (eval_linPoly A)
  rw [hfun, eval_linPoly A x] at hopen
  obtain ⟨y, hyS, hPy⟩ := exists_eval_ne_zero_of_isOpen hP0 isOpen_interior
    ⟨_, mem_interior_iff_mem_nhds.mpr hopen⟩
  obtain ⟨z, ⟨hzW, hzO⟩, hzy⟩ := interior_subset hyS
  subst hzy
  obtain ⟨-, -, hloc⟩ := hPcov _ hPy
  obtain ⟨U, V, g, hU, hzU, hV, hzV, hg, hgz, hAg, hZV⟩ := hloc z ⟨hzW, rfl⟩
  set U' := U ∩ g ⁻¹' (O ∩ V) with hU'def
  have hU' : IsOpen U' := hg.continuousOn.isOpen_inter_preimage hU (hO.inter hV)
  have hzU' : A.mulVec z ∈ U' := ⟨hzU, by simp only [Set.mem_preimage, hgz]; exact ⟨hzO, hzV⟩⟩
  have hsub : g '' U' ⊆ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ O := by
    rintro _ ⟨w, ⟨hwU, hwO, -⟩, rfl⟩
    have hw : g w ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ V := by
      rw [hZV]; exact Set.mem_image_of_mem g hwU
    exact ⟨hw.1, hwO⟩
  have himg : (fun z => A.mulVec z) '' (g '' U') = U' := by
    rw [Set.image_image]
    exact (Set.image_congr fun w hw => hAg w hw.1).trans (Set.image_id' _)
  obtain ⟨K, hK⟩ : ∃ K, LipschitzWith K (fun z : Fin n → ℂ => A.mulVec z) :=
    ⟨_, (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).lipschitz⟩
  have hpos : 0 < μH[((2 * d : ℕ) : ℝ)] U' := by
    rw [← finrank_real_fin_complex d]
    exact hU'.measure_pos _ ⟨_, hzU'⟩
  have hle := hK.hausdorffMeasure_image_le (by positivity : (0 : ℝ) ≤ ((2 * d : ℕ) : ℝ)) (g '' U')
  rw [himg] at hle
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  refine pos_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, mul_zero] at hle
  exact hpos.ne' (nonpos_iff_eq_zero.mp hle)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
