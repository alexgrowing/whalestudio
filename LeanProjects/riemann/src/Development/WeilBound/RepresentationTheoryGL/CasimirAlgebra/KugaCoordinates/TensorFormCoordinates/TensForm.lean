import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep

open scoped TensorProduct MatrixOrder ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Cz.J

section
variable {V : Type} [AddCommGroup V] [Module ℂ V] {d : ℕ}

noncomputable abbrev ec (d : ℕ) : V ⊗[ℂ] (Fin d → ℂ) →ₗ[ℂ] (Fin d → V) :=
  TensorProduct.piScalarRightHom ℂ ℂ V (Fin d)

lemma ec_injective : Function.Injective (ec (V := V) d) := by
  intro x y h
  apply (TensorProduct.piScalarRight ℂ ℂ V (Fin d)).injective
  simpa using h

lemma ec_lTensor (T : Matrix (Fin d) (Fin d) ℂ) (x : V ⊗[ℂ] (Fin d → ℂ)) (k : Fin d) :
    ec d ((Matrix.toLin' T).lTensor V x) k = ∑ j, T k j • ec d x j := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v =>
    simp [Matrix.mulVec, dotProduct, Finset.sum_smul, mul_smul]
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy, smul_add, Finset.sum_add_distrib]

end

private theorem re_sum_posSemidef_mul_H_nonneg {V : Type} [AddCommGroup V] [Module ℂ V] {d : ℕ}
    (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hnn : ∀ φ : V, 0 ≤ (H φ φ).re)
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosSemidef) (u : Fin d → V) :
    0 ≤ (∑ k, ∑ j, A k j * H (u k) (u j)).re := by
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hA
  have e : ∑ k, ∑ j, (∑ i, Matrix.vecMulVec (v i) (star (v i))) k j * H (u k) (u j) =
      ∑ i, H (∑ k, star (v i k) • u k) (∑ k, star (v i k) • u k) := by
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, map_sum, map_smulₛₗ,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Pi.star_apply,
      starRingEnd_apply, star_star, RingHom.id_apply, Finset.sum_mul, Finset.mul_sum]
    calc _ = ∑ k, ∑ i, ∑ j, v i k * star (v i j) * H (u k) (u j) :=
          Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
          ring
  rw [e, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => hnn _

theorem tensForm_holds : TensForm := by
  intro V _ _ d H hsym hpos
  have hnn : ∀ φ : V, 0 ≤ (H φ φ).re := fun φ => by
    by_cases h : φ = 0
    · simp [h]
    · exact (hpos φ h).le
  let B : V ⊗[ℂ] (Fin d → ℂ) →ₗ[ℂ] V ⊗[ℂ] (Fin d → ℂ) →ₗ⋆[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
      (fun x y => ∑ k, H (ec (V := V) d y k) (ec (V := V) d x k))
      (by intros; simp [Finset.sum_add_distrib])
      (by intros; simp [Finset.mul_sum])
      (by intros; simp [Finset.sum_add_distrib])
      (by intros; simp [Finset.mul_sum])
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro x y
    simp only [B, LinearMap.mk₂'ₛₗ_apply]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsym]
  · intro x hx
    simp only [B, LinearMap.mk₂'ₛₗ_apply]
    rw [Complex.re_sum]
    have hne : ec (V := V) d x ≠ 0 := fun h => hx (ec_injective (by rw [h, map_zero]))
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hne
    exact Finset.sum_pos' (fun j _ => hnn _) ⟨k, Finset.mem_univ _, hpos _ hk⟩
  · intro φ ψ v w
    simp only [B, LinearMap.mk₂'ₛₗ_apply, ec, TensorProduct.piScalarRightHom_tmul, map_smulₛₗ,
      LinearMap.smul_apply, map_smul, smul_eq_mul, dotProduct, Finset.mul_sum, Pi.star_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [starRingEnd_apply, RingHom.id_apply]
    ring
  · intro T c hT hle x
    have hH : ((c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - T).IsHermitian := by
      refine Matrix.IsHermitian.sub ?_ hT
      simp [Matrix.IsHermitian, Matrix.conjTranspose_smul]
    have hA : ((c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - T).PosSemidef := by
      rw [Matrix.posSemidef_iff_dotProduct_mulVec]
      refine ⟨hH, fun v => ?_⟩
      rw [Complex.nonneg_iff]
      constructor
      · simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
          dotProduct_sub, dotProduct_smul, smul_eq_mul, Complex.sub_re, Complex.re_ofReal_mul]
        linarith [hle v]
      · have h0 := hH.im_star_dotProduct_mulVec_self v
        simpa using h0.symm
    have key := re_sum_posSemidef_mul_H_nonneg H hnn _ hA (ec (V := V) d x)
    simp only [B, LinearMap.mk₂'ₛₗ_apply, ec_lTensor, map_sum, map_smul, smul_eq_mul]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, sub_mul,
      Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Complex.sub_re, Complex.re_sum,
      Complex.re_ofReal_mul] at key
    rw [Complex.re_sum, Complex.re_sum, Finset.mul_sum]
    simp only [Complex.re_sum]
    linarith

end PositivityTheory.Rg.Cz.J
