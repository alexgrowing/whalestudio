import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.ImportsAlt
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

namespace AffineChartTrdeg

variable {F : Type} [Field F] {n : ℕ} (P : Ideal (MvPolynomial (Fin n) F)) [P.IsPrime]

omit [P.IsPrime] in

theorem aeval_genPt (f : MvPolynomial (Fin n) F) :
    aeval (genPt P) f = algebraMap (MvPolynomial (Fin n) F ⧸ P)
      (FractionRing (MvPolynomial (Fin n) F ⧸ P)) (Ideal.Quotient.mk P f) := by
  have h : aeval (genPt P) = (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ P)
      (FractionRing (MvPolynomial (Fin n) F ⧸ P))).comp (Ideal.Quotient.mkₐ F P) :=
    MvPolynomial.algHom_ext fun i => by simp [genPt]
  rw [h]
  rfl

omit [P.IsPrime] in

theorem aeval_genPt_eq_zero_iff (f : MvPolynomial (Fin n) F) :
    aeval (genPt P) f = 0 ↔ f ∈ P := by
  rw [aeval_genPt, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

theorem exists_isHomogeneous (j : Fin n) (hj : genPt P j ≠ 0)
    {a : FractionRing (MvPolynomial (Fin n) F ⧸ P)}
    (ha : a ∈ Algebra.adjoin F (Set.range fun m => genPt P m * (genPt P j)⁻¹)) :
    ∃ D : ℕ, ∀ D' ≥ D, ∃ h : MvPolynomial (Fin n) F,
      h.IsHomogeneous D' ∧ aeval (genPt P) h = a * genPt P j ^ D' := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    refine ⟨1, fun D' hD' => ?_⟩
    obtain ⟨e, rfl⟩ : ∃ e, D' = 1 + e := ⟨D' - 1, by omega⟩
    refine ⟨X m * X j ^ e, (isHomogeneous_X F m).mul (isHomogeneous_X_pow j e), ?_⟩
    simp only [map_mul, map_pow, aeval_X]
    rw [pow_add, pow_one]
    field_simp
  | algebraMap r =>
    exact ⟨0, fun D' _ => ⟨C r * X j ^ D', isHomogeneous_C_mul_X_pow r j D', by simp⟩⟩
  | add x y _ _ hx hy =>
    obtain ⟨D₁, h₁⟩ := hx
    obtain ⟨D₂, h₂⟩ := hy
    refine ⟨max D₁ D₂, fun D' hD' => ?_⟩
    obtain ⟨f, hf, ef⟩ := h₁ D' (le_of_max_le_left hD')
    obtain ⟨g, hg, eg⟩ := h₂ D' (le_of_max_le_right hD')
    exact ⟨f + g, hf.add hg, by rw [map_add, ef, eg, add_mul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨D₁, h₁⟩ := hx
    obtain ⟨D₂, h₂⟩ := hy
    refine ⟨D₁ + D₂, fun D' hD' => ?_⟩
    obtain ⟨e, rfl⟩ : ∃ e, D' = D₁ + e := ⟨D' - D₁, by omega⟩
    obtain ⟨f, hf, ef⟩ := h₁ D₁ le_rfl
    obtain ⟨g, hg, eg⟩ := h₂ e (by omega)
    exact ⟨f * g, hf.mul hg, by rw [map_mul, ef, eg, pow_add]; ring⟩

theorem transcendental (hP : IsHomogIdeal P) (j : Fin n) (hj : X j ∉ P) :
    Transcendental (Algebra.adjoin F (Set.range fun m => genPt P m * (genPt P j)⁻¹))
      (genPt P j) := by
  classical
  set A' := Algebra.adjoin F (Set.range fun m => genPt P m * (genPt P j)⁻¹)
  set ξ := genPt P
  have hξ : ξ j ≠ 0 := fun h => hj ((aeval_genPt_eq_zero_iff P (X j)).1 (by simpa using h))
  rintro ⟨p, hp, hpe⟩
  set N := p.natDegree + 1
  choose D hD using fun e => exists_isHomogeneous P j hξ (p.coeff e).2
  set M := (Finset.range N).sup D
  have hh : ∀ e, ∃ h : MvPolynomial (Fin n) F,
      h.IsHomogeneous M ∧ aeval ξ h = (p.coeff e : _) * ξ j ^ M := by
    intro e
    by_cases he : e < N
    · exact hD e M (Finset.le_sup (Finset.mem_range.2 he))
    · refine ⟨0, isHomogeneous_zero _ _ _, ?_⟩
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simp
  choose h hhom heval using hh
  set G := ∑ e ∈ Finset.range N, h e * X j ^ e
  have hG : G ∈ P := by
    rw [← aeval_genPt_eq_zero_iff]
    have h0 : Polynomial.aeval (ξ j) p = ∑ e ∈ Finset.range N, (p.coeff e : _) * ξ j ^ e := by
      rw [Polynomial.aeval_eq_sum_range]
      rfl
    calc aeval ξ G = ξ j ^ M * ∑ e ∈ Finset.range N, (p.coeff e : _) * ξ j ^ e := by
          simp only [G, map_sum, map_mul, map_pow, aeval_X, heval, Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ => by ring
      _ = 0 := by rw [← h0, hpe, mul_zero]
  have hcoeff : ∀ e < N, p.coeff e = 0 := by
    intro e he
    have hcomp : homogeneousComponent (M + e) G = h e * X j ^ e := by
      simp only [G, map_sum]
      rw [Finset.sum_eq_single e]
      · exact homogeneousComponent_eq_self ((hhom e).mul (isHomogeneous_X_pow j e))
      · intro b _ hb
        rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2
          ((hhom b).mul (isHomogeneous_X_pow j b))), if_neg (by omega)]
      · intro hne
        exact absurd (Finset.mem_range.2 he) hne
    have hmem : h e * X j ^ e ∈ P := hcomp ▸ hP G hG (M + e)
    have hhe : h e ∈ P := by
      rcases Ideal.IsPrime.mem_or_mem ‹_› hmem with h1 | h1
      · exact h1
      · exact absurd (Ideal.IsPrime.mem_of_pow_mem ‹_› e h1) hj
    have h2 := heval e
    rw [(aeval_genPt_eq_zero_iff P _).2 hhe, eq_comm, mul_eq_zero] at h2
    rcases h2 with h2 | h2
    · exact Subtype.ext h2
    · exact absurd (pow_eq_zero_iff'.1 h2).1 hξ
  refine hp (Polynomial.ext fun e => ?_)
  by_cases he : e < N
  · simpa using hcoeff e he
  · simpa using Polynomial.coeff_eq_zero_of_natDegree_lt (p := p) (by omega)

theorem proof : AffineChartTrdeg.Statement := by
  intro F _ n d P _ j hP hdim hj
  set R := MvPolynomial (Fin n) F ⧸ P
  set K := FractionRing R
  set ξ := genPt P
  set A' := Algebra.adjoin F (Set.range fun m => ξ m * (ξ j)⁻¹)
  have hξ : ξ j ≠ 0 := fun h => hj ((aeval_genPt_eq_zero_iff P (X j)).1 (by simpa using h))

  have hK : Algebra.trdeg F K = ((d + 1 : ℕ) : Cardinal) := by
    have : Algebra.FiniteType F R :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F P)
        (Ideal.Quotient.mkₐ_surjective F P)
    rw [GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_isFractionRing (k := F) (A := R) K]
    rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F] at hdim
    have h2 : (Algebra.trdeg F R).toENat = ((d + 1 : ℕ) : ℕ∞) := by exact_mod_cast hdim
    exact Cardinal.toENat_eq_natCast.mp h2

  set S := Algebra.adjoin A' (Set.range fun _ : Unit => ξ j)
  have hξS : ∀ m, ξ m ∈ S := by
    intro m
    have hr : ξ m * (ξ j)⁻¹ ∈ A' := Algebra.subset_adjoin ⟨m, rfl⟩
    have : ξ m = ξ m * (ξ j)⁻¹ * ξ j := by field_simp
    rw [this]
    exact S.mul_mem (S.algebraMap_mem (⟨_, hr⟩ : A')) (Algebra.subset_adjoin ⟨(), rfl⟩)
  have hRS : ∀ r : R, algebraMap R K r ∈ S := by
    intro r
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [← aeval_genPt]
    induction f using MvPolynomial.induction_on with
    | C c =>
      rw [aeval_C, IsScalarTower.algebraMap_apply F A' K]
      exact S.algebraMap_mem _
    | add f g hf hg => rw [map_add]; exact S.add_mem hf hg
    | mul_X f i hf => rw [map_mul, aeval_X]; exact S.mul_mem hf (hξS i)

  have halg : Algebra.IsAlgebraic S K := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    have hb0 : algebraMap R K b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    refine ⟨Polynomial.C ⟨_, hRS b⟩ * Polynomial.X - Polynomial.C ⟨_, hRS a⟩, fun h => hb0 ?_, ?_⟩
    · have := congrArg (Polynomial.coeff · 1) h
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, ↓reduceIte,
        one_ne_zero, Polynomial.coeff_zero] at this
      have h' := congrArg Subtype.val this
      simp only [Subalgebra.coe_sub, Subalgebra.coe_zero, sub_zero] at h'
      exact h'
    · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      show algebraMap R K b * (algebraMap R K a / algebraMap R K b) - algebraMap R K a = 0
      rw [mul_comm, div_mul_cancel₀ _ hb0, sub_self]

  have h1 : Algebra.trdeg A' K = 1 := by
    have hind : AlgebraicIndependent A' (fun _ : Unit => ξ j) :=
      algebraicIndependent_unique_type_iff.mpr (transcendental P hP.isHomog j hj)
    have hb : IsTranscendenceBasis A' (fun _ : Unit => ξ j) :=
      hind.isTranscendenceBasis_iff_isAlgebraic.mpr halg
    rw [← hb.cardinalMk_eq_trdeg, Cardinal.mk_fintype, Fintype.card_unit, Nat.cast_one]

  have : FaithfulSMul A' K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  have : FaithfulSMul F A' :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap F A').injective
  have hadd := trdeg_add_eq F A' (A := K)
  rw [h1, hK] at hadd
  have hfin : Algebra.trdeg F A' < Cardinal.aleph0 :=
    lt_of_le_of_lt le_self_add (by rw [hadd]; exact Cardinal.natCast_lt_aleph0)
  obtain ⟨k, hk⟩ := Cardinal.lt_aleph0.mp hfin
  rw [hk] at hadd ⊢
  norm_cast at hadd ⊢
  omega

end AffineChartTrdeg

end GroundTheory.Heights₂.Heights
