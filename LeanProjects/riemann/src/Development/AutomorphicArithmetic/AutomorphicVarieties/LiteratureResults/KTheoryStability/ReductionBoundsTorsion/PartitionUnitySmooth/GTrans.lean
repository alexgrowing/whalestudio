import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Smoothing
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.RealVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Realsurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Grampd

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

private theorem tr_eq (L : Type) [Field L] [NumberField L] (hC : IsTotallyComplex L) (a : 𝓞 L) :
    ((Algebra.trace ℤ (𝓞 L) a : ℤ) : ℝ) = 2 * ∑ w : InfinitePlace L, (embO w a).re := by
  classical
  have h1 := trace_eq_sum_embeddings ℂ (K := ℚ) (L := L) (x := (a : L))
  rw [← Algebra.coe_trace_int, ← Fintype.sum_equiv (RingHom.equivRatAlgHom L ℂ) (fun φ : L →+* ℂ => φ (a : L)) _
    (fun φ => rfl)] at h1
  have h2 := congrArg Complex.re h1
  rw [Complex.re_sum, ← Finset.sum_fiberwise Finset.univ InfinitePlace.mk] at h2
  have h3 : (algebraMap ℚ ℂ ((Algebra.trace ℤ (𝓞 L) a : ℤ) : ℚ)).re = ((Algebra.trace ℤ (𝓞 L) a : ℤ) : ℝ) := by simp
  rw [← h3, h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => (embO w a).re), Finset.sum_const, InfinitePlace.card_filter_mk_eq,
    (hC.isComplex w).mult_eq_two]
  · simp
  · intro φ hφ
    obtain rfl := (Finset.mem_filter.1 hφ).2
    change _ = ((InfinitePlace.mk φ).embedding (a : L)).re
    rcases InfinitePlace.embedding_mk_eq φ with e | e <;> rw [e]
    simp

private theorem pair {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.PosDef) (g v : Fin N → ℂ) :
    star (A⁻¹ *ᵥ star g) ⬝ᵥ (A *ᵥ v) = g ⬝ᵥ v := by
  have hd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA.isUnit
  rw [star_mulVec, star_star, hA.isHermitian.inv.eq, ← dotProduct_mulVec, mulVec_mulVec, nonsing_inv_mul _ hd, one_mulVec]

private theorem dual_eq {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (g : Fin N → ℂ) :
    star g ⬝ᵥ ((A⁻¹)ᵀ *ᵥ g) = g ⬝ᵥ (A⁻¹ *ᵥ star g) := by
  rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]

private theorem real_cs {ι : Type} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι ℝ} (hG : G.PosDef) (c x : ι → ℝ) (t : ℝ) :
    2 * t * (c ⬝ᵥ x) - t ^ 2 * (x ⬝ᵥ (G *ᵥ x)) ≤ c ⬝ᵥ (G⁻¹ *ᵥ c) := by
  have hd : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hG.isUnit
  have h0 := hG.posSemidef.dotProduct_mulVec_nonneg (t • x - G⁻¹ *ᵥ c)
  have e1 : G *ᵥ (G⁻¹ *ᵥ c) = c := by rw [mulVec_mulVec, mul_nonsing_inv _ hd, one_mulVec]
  have hT : Gᵀ = G := by simpa using hG.isHermitian.eq
  have e2 : (G⁻¹ *ᵥ c) ⬝ᵥ (G *ᵥ x) = c ⬝ᵥ x := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hT, e1]
  rw [star_trivial, mulVec_sub, mulVec_smul, e1, sub_dotProduct, dotProduct_sub, dotProduct_sub, smul_dotProduct,
    smul_dotProduct, dotProduct_smul, dotProduct_smul, e2, dotProduct_comm x c, dotProduct_comm (G⁻¹ *ᵥ c) c] at h0
  simp only [smul_eq_mul] at h0
  nlinarith

private theorem exists_f (L : Type) [Field L] [NumberField L] (hC : IsTotallyComplex L) (N : ℕ)
    (c : Fin N × BI L → ℤ) (hc : c ≠ 0) : ∃ f : Lat L N, f ≠ 0 ∧ ∀ x : Fin N × BI L → ℝ,
      (discr L : ℝ) * ((fun i => (c i : ℝ)) ⬝ᵥ x) = 2 * ∑ w, (toR f w ⬝ᵥ realVec x w).re := by
  classical
  set b := RingOfIntegers.basis L with hb
  set M := Algebra.traceMatrix ℤ b with hM
  have hD : discr L = M.det := Algebra.discr_def ℤ _
  let f : Lat L N := fun a => ∑ i, ((fun j => c (a, j)) ᵥ* M.adjugate) i • b i
  have hf : ∀ a j, Algebra.trace ℤ (𝓞 L) (f a * b j) = discr L * c (a, j) := by
    intro a j
    have e : (((fun j => c (a, j)) ᵥ* M.adjugate) ᵥ* M) j = discr L * c (a, j) := by
      rw [vecMul_vecMul, adjugate_mul, vecMul_smul, vecMul_one, hD]; rfl
    rw [← e]
    simp only [f, Finset.sum_mul, map_sum, smul_mul_assoc, map_zsmul, smul_eq_mul]
    rfl
  refine ⟨f, fun h0 => hc ?_, fun x => ?_⟩
  · funext ⟨a, j⟩
    have := hf a j
    rw [h0, Pi.zero_apply, zero_mul, map_zero] at this
    exact (mul_eq_zero.1 this.symm).resolve_left (discr_ne_zero L)
  · have e : ∀ a j, (discr L : ℝ) * (c (a, j) : ℝ) = 2 * ∑ w : InfinitePlace L, (embO w (f a) * embO w (b j)).re := by
      intro a j
      have := tr_eq L hC (f a * b j)
      rw [hf] at this
      simpa only [Int.cast_mul, map_mul] using this
    have e2 : ∀ w : InfinitePlace L, (toR f w ⬝ᵥ realVec x w).re =
        ∑ a, ∑ j, (embO w (f a) * embO w (b j)).re * x (a, j) := by
      intro w
      simp only [dotProduct, toR, realVec, Finset.mul_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
      rw [← Complex.re_mul_ofReal]
      congr 1
      ring
    simp only [e2]
    simp only [dotProduct, Fintype.sum_prod_type, Finset.mul_sum]
    rw [Finset.sum_comm (γ := InfinitePlace L)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm (γ := InfinitePlace L)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, e, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun w _ => mul_assoc _ _ _

private theorem num {D S g l p : ℝ} (hD : D ≠ 0) (hl : l ≤ S) (hp : D * p = 2 * S)
    (h : 2 * (2 / D) * p - (2 / D) ^ 2 * S ≤ g) : 4 / D ^ 2 * l ≤ g := by
  have e : p = 2 * S / D := by field_simp; linarith
  have e2 : 2 * (2 / D) * p - (2 / D) ^ 2 * S = 4 / D ^ 2 * S := by rw [e]; field_simp; ring
  rw [e2] at h
  exact (mul_le_mul_of_nonneg_left hl (by positivity)).trans h

theorem pf_GTrans : GTrans := by
  classical
  intro hB hZ L _ _ hC N hN
  haveI := hC
  obtain ⟨C, hC0, hT⟩ := hZ (Fintype.card (Fin N × BI L))
  have hD : (discr L : ℝ) ≠ 0 := Int.cast_ne_zero.2 (discr_ne_zero L)
  have hD2 : (0 : ℝ) < 4 / (discr L : ℝ) ^ 2 := by positivity
  refine ⟨C / (4 / (discr L : ℝ) ^ 2), div_pos hC0 hD2, fun h hh z => ?_⟩
  obtain ⟨g1, g2, g3, g4⟩ := gramq L N h
  obtain ⟨hl, hlq, -, hdP, -⟩ := (hB L N hN).1 h hh
  obtain ⟨hl', hlq', -⟩ := (hB L N hN).1 _ hdP
  have hG : (gram h).PosDef := by
    have h1 : ((lam h)⁻¹ • gram h).PosDef := by
      refine (grampd _ _ (g1.smul (IsSelfAdjoint.all _)) fun c hc => ?_).1
      rw [smul_mulVec, dotProduct_smul, smul_eq_mul, g2, g3, ← div_eq_inv_mul, one_le_div hl]
      refine hlq _ fun h0 => hc (g4.1 (h0.trans ?_))
      funext a
      simp [intVec]
    have h2 := h1.smul hl
    rwa [smul_smul, mul_inv_cancel₀ hl.ne', one_smul] at h2
  obtain ⟨p, rfl⟩ := realsurj L N z
  obtain ⟨c, hc⟩ := hT _ rfl (gram h) hG (4 / (discr L : ℝ) ^ 2 * lamD h) (mul_pos hD2 hl') (fun c hc => by
    obtain ⟨f, hf, e⟩ := exists_f L hC N c hc
    obtain ⟨x, hx⟩ := realsurj L N fun w => (mat h w)⁻¹ *ᵥ star (toR f w)
    have hS : q (dualH h) f = ∑ w, (toR f w ⬝ᵥ realVec x w).re := by
      rw [hx]
      exact Finset.sum_congr rfl fun w _ => congrArg Complex.re (dual_eq (mat h w) (toR f w))
    have hS2 : x ⬝ᵥ (gram h *ᵥ x) = q (dualH h) f := by
      rw [g2, hS, hx]
      exact Finset.sum_congr rfl fun w _ => congrArg Complex.re (pair (hh w) _ _)
    have k := real_cs hG (fun i => (c i : ℝ)) x (2 / discr L)
    rw [hS2] at k
    exact num hD (hlq' f hf) ((e x).trans (by rw [hS])) k) p
  refine ⟨intVec c, ?_⟩
  rw [g2] at hc
  have e : realVec (p - fun i => (c i : ℝ)) = realVec p - toR (intVec c) := by
    rw [← g3]
    funext w a
    simp [realVec, sub_mul, Finset.sum_sub_distrib]
  rw [e] at hc
  rw [div_div]
  exact hc

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
