import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeFiniteFibreDim
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeFibreDegree
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeMassOfFibre
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionsContainOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjHomInjective
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsExists
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLeadIdealDim
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLinearFormCut
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHomogDimZeroPow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped Matrix

noncomputable section

theorem exists_mem_zeroSet_mulVec_eq {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {B : Matrix (Fin d) (Fin n) ℂ} (hB : ComplexSets.IsFiniteProjection J B) (x : Fin d → ℂ) :
    ∃ z ∈ ComplexSets.zeroSet J, B *ᵥ z = x := by
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (ComplexSets.projHom J B).toRingHom.toAlgebra
  have _ : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    ⟨fun y => hB.finite.to_isIntegral y⟩
  have _ : (RingHom.ker (eval x)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun c => ⟨C c, eval_C c⟩
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := MvPolynomial (Fin n) ℂ ⧸ J) (RingHom.ker (eval x)) (by
      intro q hq
      have hq0 : q = 0 := hB.injective (by rw [RingHom.mem_ker] at hq; exact hq.trans (map_zero _).symm)
      rw [hq0]; exact Ideal.zero_mem _)
  have hQ' : (Q.comap (Ideal.Quotient.mk J)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨z, hz⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.1 hQ'
  have hmem : ∀ q, Ideal.Quotient.mk J q ∈ Q ↔ eval z q = 0 := fun q => by
    rw [← Ideal.mem_comap, hz, mem_vanishingIdeal_singleton_iff]; rfl
  refine ⟨z, fun q hq => (hmem q).1 ?_, funext fun i => ?_⟩
  · rw [Ideal.Quotient.eq_zero_iff_mem.2 hq]; exact Q.zero_mem
  · have hi : X i - C (x i) ∈ RingHom.ker (eval x) := by simp [RingHom.mem_ker]
    rw [← hQP, Ideal.mem_comap] at hi
    change ComplexSets.projHom J B (X i - C (x i)) ∈ Q at hi
    have h1 : ComplexSets.projHom J B (X i - C (x i)) =
        Ideal.Quotient.mk J (ComplexSets.linPoly B i - C (x i)) := by
      simp [ComplexSets.projHom, ComplexSets.pullback]
    rw [h1, hmem, map_sub, eval_C, sub_eq_zero] at hi
    rw [← hi]
    simp [ComplexSets.linPoly, Matrix.mulVec, dotProduct]

theorem ConeFiniteFibreDim.proof : ConeFiniteFibreDim.Statement := by
  intro n m h J hJ _ _ hae
  have _ := hJ.isPrime

  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ n := by
    have := ringKrullDim_le_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    rwa [ComplexSets.ringKrullDim_mvPolynomial_complex] at this
  have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ J)
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d := by
    generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = D at h0 hle
    induction D using WithBot.recBotCoe with
    | bot => exact absurd h0 (by simp)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top => exact absurd hle (not_le.2 (WithBot.coe_lt_coe.2 (ENat.coe_lt_top n)))
      | coe d => exact ⟨d, rfl⟩
  rw [hd]
  by_contra hlt
  have hmd : m < d := by push_neg at hlt; exact_mod_cast hlt
  obtain ⟨k, rfl⟩ : ∃ k, d = m + k := ⟨d - m, by omega⟩
  have hk : 0 < k := by omega

  obtain ⟨W, ⟨S, rfl⟩, ⟨A₀, p, hpS, hp⟩, hW⟩ :=
    ComplexSets.FiniteProjectionsContainOpen.proof ComplexSets.ConeAvoidsFinite.proof
      ComplexSets.FiniteProjHomInjective.proof ComplexSets.ConeAvoidsOpen.proof
      (ComplexSets.ConeAvoidsExists.proof ComplexSets.LeadIdealDim.proof
        ComplexSets.LinearFormCut.proof ComplexSets.HomogDimZeroPow.proof) n (m + k) J inferInstance hd

  set N : Matrix (Fin n) (Fin n) ℂ := (h.mat)ᵀ⁻¹
  have hdet : IsUnit (h.mat)ᵀ.det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  have hMN : (h.mat)ᵀ * N = 1 := Matrix.mul_nonsing_inv _ hdet

  let blk : ((Fin m × Fin n) ⊕ (Fin k × Fin n) → ℂ) → Matrix (Fin (m + k)) (Fin n) ℂ :=
    fun v i j => Fin.addCases (motive := fun _ => ℂ) (fun a => v (.inl (a, j))) (fun b => v (.inr (b, j))) i
  let g : Fin (m + k) × Fin n → MvPolynomial ((Fin m × Fin n) ⊕ (Fin k × Fin n)) ℂ := fun ij =>
    ∑ l, Fin.addCases (motive := fun _ => MvPolynomial ((Fin m × Fin n) ⊕ (Fin k × Fin n)) ℂ)
      (fun a => X (.inl (a, l))) (fun b => X (.inr (b, l))) ij.1 * C (N l ij.2)
  have heval : ∀ v, eval v (bind₁ g p) = eval (fun ij => (blk v * N) ij.1 ij.2) p := by
    intro v
    change eval₂Hom (RingHom.id ℂ) v (bind₁ g p) = eval₂Hom (RingHom.id ℂ) _ p
    rw [eval₂Hom_bind₁]
    refine congrArg (fun f => eval₂Hom (RingHom.id ℂ) f p) (funext fun ij => ?_)
    obtain ⟨i, j⟩ := ij
    change eval v (g (i, j)) = (blk v * N) i j
    simp only [g, blk, Matrix.mul_apply, map_sum, map_mul, eval_C]
    refine Finset.sum_congr rfl fun l _ => ?_
    induction i using Fin.addCases <;> simp
  have hP0 : bind₁ g p ≠ 0 := by
    intro h0'
    let v₀ : (Fin m × Fin n) ⊕ (Fin k × Fin n) → ℂ :=
      Sum.elim (fun aj => (A₀ * (h.mat)ᵀ) (Fin.castAdd k aj.1) aj.2)
        (fun bj => (A₀ * (h.mat)ᵀ) (Fin.natAdd m bj.1) bj.2)
    have hv₀ : blk v₀ = A₀ * (h.mat)ᵀ := by
      ext i j
      induction i using Fin.addCases <;> simp [blk, v₀]
    have := heval v₀
    rw [h0', map_zero, hv₀, Matrix.mul_assoc, hMN, Matrix.mul_one] at this
    exact hp this.symm

  have h1 := ConeFibreDegree.ae_eval_ne_zero_univ _ hP0
  have h2 := (volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : (Fin m × Fin n) ⊕ (Fin k × Fin n) => ℂ)).quasiMeasurePreserving.ae h1
  have h3 := Measure.ae_ae_of_ae_prod h2
  have h4 : ∀ᵐ a : Fin m × Fin n → ℂ, ∃ b : Fin k × Fin n → ℂ,
      eval ((MeasurableEquiv.sumPiEquivProdPi _).symm (a, b)) (bind₁ g p) ≠ 0 :=
    h3.mono fun a ha => ha.exists
  have h5 := (measurePreserving_curry_matrix m n).symm.quasiMeasurePreserving.ae h4
  have _ : (ae (volume : Measure (Fin m → Fin n → ℂ))).NeBot := by
    refine ae_neBot.2 (Measure.measure_univ_ne_zero.1 ?_)
    rw [volume_pi, Measure.pi_univ]
    exact Finset.prod_ne_zero_iff.2 fun i _ => Measure.measure_univ_ne_zero.2 (NeZero.ne _)
  obtain ⟨π, hπ, b, hb⟩ := (hae.and h5).exists
  set v := (MeasurableEquiv.sumPiEquivProdPi fun _ : (Fin m × Fin n) ⊕ (Fin k × Fin n) => ℂ).symm
    ((MeasurableEquiv.curry (Fin m) (Fin n) ℂ).symm π, b)
  have hrow : ∀ (u : Fin n → ℂ) (i : Fin m), (blk v *ᵥ u) (Fin.castAdd k i) = ∑ j, π i j * u j := by
    intro u i
    simp [blk, v, Matrix.mulVec, dotProduct, MeasurableEquiv.coe_curry_symm]
    rfl
  have hfin : ComplexSets.IsFiniteProjection J (blk v * N) := hW ⟨p, hpS, by rw [← heval]; exact hb⟩

  obtain ⟨w, hw⟩ := hπ.exists
  apply hw
  have key : ∀ c : ℂ, ∃ y : EuclideanSpace ℂ (Fin n), (y ∈ coneSet h J ∧ linProj π y = w) ∧
      (blk v *ᵥ fun j => y j) (Fin.natAdd m ⟨0, hk⟩) = c := by
    intro c
    obtain ⟨z, hz, hBz⟩ := exists_mem_zeroSet_mulVec_eq hfin
      (Fin.addCases (motive := fun _ => ℂ) (fun a => w a) (fun _ => c))
    rw [← Matrix.mulVec_mulVec] at hBz
    have hpt : h.pointOf (WithLp.toLp 2 (N *ᵥ z)) = z := by
      simp [HermNorm.pointOf, Matrix.mulVec_mulVec, hMN]
    refine ⟨WithLp.toLp 2 (N *ᵥ z), ⟨fun q hq => ?_, ?_⟩, ?_⟩
    · rw [hpt]; exact hz q hq
    · ext i
      have := congrFun hBz (Fin.castAdd k i)
      rw [hrow] at this
      simpa [linProj] using this
    · have := congrFun hBz (Fin.natAdd m ⟨0, hk⟩)
      rw [Fin.addCases_right] at this
      exact this
  choose y hy hyc using key
  have hinj : Function.Injective y := fun c₁ c₂ he => by
    rw [← hyc c₁, ← hyc c₂, he]
  exact (Set.infinite_of_injective_forall_mem hinj hy).encard_eq

end

end GroundTheory.Heights₂.Heights
