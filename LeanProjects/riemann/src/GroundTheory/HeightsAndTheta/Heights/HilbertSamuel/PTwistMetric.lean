import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwistMetric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingWeight
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwistIntersectionAnyDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory NumberField Filter Topology

theorem isOpen_multiconePts {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z; simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem leviForm_eq_of_eventuallyEq_add_const {κ : Type*} [Fintype κ] (φ ψ : (κ → ℂ) → ℝ) (c : ℝ)
    (z w : κ → ℂ) (h : ψ =ᶠ[𝓝 z] fun x => φ x + c) : leviForm ψ z w = leviForm φ z w := by
  have h1 : fderiv ℝ ψ =ᶠ[𝓝 z] fderiv ℝ φ := by
    filter_upwards [h.eventuallyEq_nhds] with x hx
    rw [hx.fderiv_eq, fderiv_add_const]
  unfold leviForm
  rw [h1.fderiv_eq]

theorem TwistMetric.proof (hEW : EmbeddingWeight.Statement)
    (hTI : TwistIntersectionAnyDegree.Statement) : TwistMetric.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y D A P0 II u hD hII hY hbir _ hsemi hconj hlies hu hsum
  refine ⟨((D + 1 : ℕ) : ℝ) * genDeg (mCoordIdeal y) D A.a, fun δ hδ => ?_⟩
  obtain ⟨B, hBa, hBs, hBc, hBloc⟩ := hEW K ι Ω F y (fun sg => Real.exp (u sg + δ))
    (fun _ => Real.exp_pos _) (fun sg => by simp only [hu]) hlies
  have hcard : (Fintype.card (F →+* ℂ) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (F →+* ℂ) :=
      Fintype.card_pos_iff.mpr ⟨(IsAlgClosed.lift (R := ℚ) (S := F) (M := ℂ)).toRingHom⟩
    exact_mod_cast this.ne'
  refine ⟨A.tensor B, ?_, ?_, ?_, fun z hz sg hsg => ?_, ?_⟩
  · change A.a + B.a = A.a
    rw [hBa, add_zero]
  · unfold IsSemipositiveRel
    refine ⟨ContDiffOn.mul hsemi.1 hBs, fun z hz w hw => ?_⟩
    obtain ⟨sg, hsg, -⟩ := hlies z hz
    have hzA : ∀ᶠ x in 𝓝 z, A.h x ≠ 0 := by
      filter_upwards [isOpen_multiconePts.mem_nhds hz.1] with x hx using (A.pos x hx).ne'
    have heq : (fun x => Real.log ((A.tensor B).h x)) =ᶠ[𝓝 z]
        fun x => Real.log (A.h x) + Real.log (Real.exp (u sg + δ)) := by
      filter_upwards [hzA, hBloc z hz sg hsg] with x hx hB
      change Real.log (A.h x * B.h x) = _
      rw [hB, Real.log_mul hx (Real.exp_pos _).ne']
    rw [leviForm_eq_of_eventuallyEq_add_const _ _ _ z w heq]
    exact hsemi.2 z hz w hw
  · intro z
    change A.h _ * B.h _ = A.h z * B.h z
    rw [hconj z, hBc z]
  · change A.h z * B.h z = _
    rw [(hBloc z hz sg hsg).self_of_nhds, mul_comm]
  · rw [hTI K ι Ω F y D A B II (fun sg => Real.exp (u sg + δ)) hD hII hY hbir hsemi.1 hBa hBs
      (fun _ => Real.exp_pos _) hlies hBloc]
    have hs : (∑ sg, Real.log ((fun sg => Real.exp (u sg + δ)) sg)) / Fintype.card (F →+* ℂ) = δ := by
      simp only [Real.log_exp, Finset.sum_add_distrib, hsum, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, zero_add]
      field_simp
    rw [hs]

end GroundTheory.Heights₂.Heights.HilbertSamuel
