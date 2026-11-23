import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GroupFactorizationHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IntegrableOnIoiTruncatedPowerMoment

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.TensLen

open Formalism.HermitianLatticeCounting.ExpansionTerms (majorantDistance)

section general

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem infDist_add_mem (S : Submodule ℂ V) (x w : V) (hw : w ∈ S) :
    Metric.infDist (x + w) (S : Set V) = Metric.infDist x (S : Set V) := by
  have h := Metric.infDist_image (isometry_add_right w) (x := x) (t := (S : Set V))
  have h2 : (fun y => y + w) '' (S : Set V) = S := by
    ext v
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact S.add_mem hy hw
    · intro hv
      exact ⟨v - w, S.sub_mem hv hw, by simp⟩
  rwa [h2] at h

theorem len_eq_of_unitriangular {n : ℕ} (y y' : Fin n → V) (U : Matrix (Fin n) (Fin n) ℂ)
    (h0 : ∀ c a, a < c → U c a = 0) (h1 : ∀ c, U c c = 1) (h : ∀ a, y a = ∑ c, U c a • y' c) (a : Fin n) :
    majorantDistance y a = majorantDistance y' a := by
  have hrest : ∀ (S : Submodule ℂ V) (b : Fin n), (∀ c, c < b → y' c ∈ S) →
      ∑ c ∈ univ.erase b, U c b • y' c ∈ S := by
    intro S b hS
    refine S.sum_mem fun c hc => ?_
    rcases lt_trichotomy c b with hcb | hcb | hcb
    · exact S.smul_mem _ (hS c hcb)
    · exact absurd hcb (Finset.ne_of_mem_erase hc)
    · rw [h0 c b hcb, zero_smul]; exact S.zero_mem
  have hy : ∀ b, y b = y' b + ∑ c ∈ univ.erase b, U c b • y' c := by
    intro b
    rw [h b, ← Finset.add_sum_erase _ _ (Finset.mem_univ b), h1, one_smul]
  have hspan : Submodule.span ℂ (y '' {b | b < a}) = Submodule.span ℂ (y' '' {b | b < a}) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨b, hb, rfl⟩
      rw [hy b]
      exact Submodule.add_mem _ (Submodule.subset_span ⟨b, hb, rfl⟩)
        (hrest _ b fun c hc => Submodule.subset_span ⟨c, lt_trans hc hb, rfl⟩)
    · rw [Submodule.span_le]
      have key : ∀ b, b < a → y' b ∈ Submodule.span ℂ (y '' {b | b < a}) := by
        intro b
        induction b using WellFoundedLT.induction with
        | ind b ih =>
          intro hb
          rw [eq_sub_of_add_eq (hy b).symm]
          exact Submodule.sub_mem _ (Submodule.subset_span ⟨b, hb, rfl⟩)
            (hrest _ b fun c hc => ih c hc (lt_trans hc hb))
      rintro _ ⟨b, hb, rfl⟩
      exact key b hb
  unfold majorantDistance
  rw [hspan, hy a]
  exact infDist_add_mem _ _ _ (hrest _ a fun c hc => Submodule.subset_span ⟨c, hc, rfl⟩)

theorem len_pos {n : ℕ} (y : Fin n → V) (hy : LinearIndependent ℂ y) (a : Fin n) : 0 < majorantDistance y a := by
  unfold majorantDistance
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (y '' {b | b < a})) :=
    FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
  refine ((Submodule.closed_of_finiteDimensional _).notMem_iff_infDist_pos ⟨0, Submodule.zero_mem _⟩).1 ?_
  exact hy.notMem_span_image (by simp)

theorem len_zero {n : ℕ} (y : Fin (n + 1) → V) : majorantDistance y 0 = ‖y 0‖ := by
  unfold majorantDistance
  have : y '' {b | b < 0} = ∅ := by simp
  rw [this, Submodule.span_empty, Submodule.bot_coe, Metric.infDist_singleton, dist_zero_right]

end general

theorem cmp_mulVec_wedge {n l : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin l → Fin n → ℂ) :
    BranchingSupport.cmp l g *ᵥ wedge f = wedge (fun b => g *ᵥ f b) := by
  funext I
  have h := Formalism.HermitianLatticeCounting.P.ge_cauchyBinet (g.submatrix (I.1.orderEmbOfFin I.2) id)
    (Matrix.of fun (i : Fin n) (b : Fin l) => f b i)
  refine Eq.trans ?_ (h.symm.trans ?_)
  · simp only [mulVec, dotProduct]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [mul_comm]
    rfl
  · rfl

theorem sum_norm_wedge {n l : ℕ} (f : Fin l → Fin n → ℂ) :
    ∑ J, ‖wedge f J‖ ^ 2 =
      ∏ a, majorantDistance (fun b => (WithLp.toLp 2 (f b) : EuclideanSpace ℂ (Fin n))) a ^ 2 := by
  have h := Formalism.HermitianLatticeCounting.P.gram_matrix_product_formula (EuclideanSpace ℂ (Fin n)) l (fun b => WithLp.toLp 2 (f b))
  have h2 := Formalism.HermitianLatticeCounting.P.ge_cauchyBinet (Matrix.of fun (i : Fin n) (b : Fin l) => f b i)ᴴ
    (Matrix.of fun (i : Fin n) (b : Fin l) => f b i)
  have h3 : (Matrix.of fun (i : Fin n) (b : Fin l) => f b i)ᴴ *
      (Matrix.of fun (i : Fin n) (b : Fin l) => f b i) =
      Matrix.of fun a b => inner ℂ (WithLp.toLp 2 (f a) : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 (f b)) := by
    ext a b
    simp [Matrix.mul_apply, PiLp.inner_apply, mul_comm]
  rw [h3, h] at h2
  apply Complex.ofReal_injective
  rw [h2]
  push_cast
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [← conjTranspose_submatrix, det_conjTranspose, RCLike.star_def, Complex.mul_conj']
  rfl

theorem sum_norm_sq_eq {n : ℕ} (v : Fin n → ℂ) : ((∑ c, ‖v c‖ ^ 2 : ℝ) : ℂ) = v ⬝ᵥ star v := by
  push_cast
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Pi.star_apply, RCLike.star_def, Complex.mul_conj']

theorem sum_norm_dual {n : ℕ} (H g : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1)
    (hg : gᴴ * H * g = H) (hu : IsUnit g.det) (f : Fin n → ℂ) :
    ∑ c, ‖(dualM g⁻¹ *ᵥ (fun c => Formalism.QuantumDeterminants.herm H (Pi.single c 1) f)) c‖ ^ 2 = ∑ c, ‖(g⁻¹ *ᵥ f) c‖ ^ 2 := by
  have h1 : (fun c => Formalism.QuantumDeterminants.herm H (Pi.single c 1) f) = star f ᵥ* H := by
    funext c
    simp [Formalism.QuantumDeterminants.herm, vecMul, dotProduct]
  have h2 : H * g = (g⁻¹)ᴴ * H := by
    conv_rhs => rw [← hg]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, mul_nonsing_inv _ hu,
      conjTranspose_one, Matrix.one_mul]
  have h3 : dualM g⁻¹ *ᵥ (star f ᵥ* H) = star (H *ᵥ (g⁻¹ *ᵥ f)) := by
    rw [dualM, nonsing_inv_nonsing_inv _ hu, mulVec_transpose, vecMul_vecMul, h2, star_mulVec, star_mulVec,
      vecMul_vecMul, hH]
  rw [h1, h3]
  apply Complex.ofReal_injective
  rw [sum_norm_sq_eq, sum_norm_sq_eq, star_star, star_mulVec, hH, dotProduct_mulVec, vecMul_vecMul, hHH,
    vecMul_one, dotProduct_comm]

theorem fvec_indep (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) : LinearIndependent ℂ (Formalism.QuantumDeterminants.fvec k r z) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp [Formalism.QuantumDeterminants.Tz, Formalism.QuantumDeterminants.herm] at hT
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hz0
  have hir : r ≤ i.val := by
    by_contra hlt
    exact hi (hz i (Or.inl (by omega)))
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  by_cases ha : a.val < r
  · have := congrFun hc ⟨a.val, by omega⟩
    rw [Finset.sum_apply, Finset.sum_eq_single a] at this
    · rw [Pi.smul_apply, Formalism.QuantumDeterminants.fvec_apply_lt z hz _ _ ha] at this
      simpa using this
    · intro b _ hb
      rw [Pi.smul_apply, Formalism.QuantumDeterminants.fvec_apply_lt z hz _ _ ha, if_neg (fun h => hb (Fin.ext h)), smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have := congrFun hc i
    rw [Finset.sum_apply, Finset.sum_eq_single a] at this
    · rw [Pi.smul_apply, Formalism.QuantumDeterminants.fvec_apply_ge z _ _ hir, if_pos (by omega)] at this
      exact (mul_eq_zero.1 this).resolve_right hi
    · intro b _ hb
      rw [Pi.smul_apply, Formalism.QuantumDeterminants.fvec_apply_ge z _ _ hir,
        if_neg (fun h => hb (Fin.ext (by omega))), smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem isUnit_det_of_unitary {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hHH : H * H = 1)
    (hg : gᴴ * H * g = H) : IsUnit g.det := by
  have h : (H * (gᴴ * H)) * g = 1 := by rw [Matrix.mul_assoc, hg, hHH]
  exact Matrix.isUnit_det_of_left_inverse h

theorem lengths : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → ∀ g ∈ GG k r, (∑ J, ‖(cmp (r + 1) g⁻¹ *ᵥ (wedge (Formalism.QuantumDeterminants.fvec k r z))) J‖ ^ 2 = ∏ a, lenA k r z g a ^ 2) ∧ (∑ c, ‖(dualM g⁻¹ *ᵥ (flat k r (Formalism.QuantumDeterminants.fvec k r z 0))) c‖ ^ 2 = lenA k r z g 0 ^ 2) ∧ (∀ a, 0 < lenA k r z g a) ∧ ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ a, lenA k r z (s * g) a = lenA k r z g a := by
  intro k r z hz hT g hg
  obtain ⟨hH, hHH, -⟩ := Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r
  have hu : IsUnit g.det := isUnit_det_of_unitary hHH hg
  have hl : ∀ g a, lenA k r z g a = majorantDistance (fun b => (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z b) :
      EuclideanSpace ℂ (Fin (2 * r + k + 1)))) a := fun _ _ => rfl
  refine ⟨?_, ?_, fun a => ?_, fun s hs a => ?_⟩
  · rw [cmp_mulVec_wedge, sum_norm_wedge]
    rfl
  · rw [hl, len_zero, EuclideanSpace.norm_sq_eq]
    exact sum_norm_dual _ g hH hHH hg hu _
  · rw [hl]
    refine len_pos _ ?_ a
    have hinj : Function.Injective (g⁻¹).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_nonsing_inv_det g hu))
    have h1 := (fvec_indep k r z hz hT).map' (Matrix.mulVecLin g⁻¹) (LinearMap.ker_eq_bot.2 hinj)
    exact h1.map' (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).symm.toLinearMap (LinearEquiv.ker _)
  · obtain ⟨U, h0, h1, hF⟩ := Formalism.QuantumDeterminants.S_F hz hs
    have hsu : IsUnit s.det := isUnit_det_of_unitary hHH (Formalism.QuantumDeterminants.Sset_UH hs)
    rw [hl, hl]
    symm
    refine len_eq_of_unitriangular _ _ U h0 h1 (fun b => ?_) a
    have hcol : s *ᵥ Formalism.QuantumDeterminants.fvec k r z b = ∑ c, U c b • Formalism.QuantumDeterminants.fvec k r z c := by
      funext i
      have := congrFun (congrFun hF i) b
      simpa [Matrix.mul_apply, Formalism.QuantumDeterminants.Fm, mulVec, dotProduct, mul_comm] using this
    have h2 : g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z b = (s * g)⁻¹ *ᵥ (s *ᵥ Formalism.QuantumDeterminants.fvec k r z b) := by
      rw [mulVec_mulVec, Matrix.mul_inv_rev, Matrix.mul_assoc, nonsing_inv_mul _ hsu, Matrix.mul_one]
    rw [h2, hcol, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, WithLp.toLp_sum, WithLp.toLp_smul]

end GlobalTheory.TensLen
