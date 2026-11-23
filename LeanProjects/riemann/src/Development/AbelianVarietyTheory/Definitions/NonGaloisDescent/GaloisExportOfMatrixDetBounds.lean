import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen
open scoped ENNReal TensorProduct

namespace GlobalTheory.TwSys.Test

section Ord
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem ordHyp_X (l M : ℕ) :
    OrdHyp O l M 1 1 0 (MvPolynomial.X (Sum.inl 0) + MvPolynomial.X (Sum.inr 0)) := by
  refine ⟨MvPolynomial.X (Sum.inl 0), 1, ?_, ?_, 1, fun _ => 1, by simp, fun _ => le_rfl, by simp⟩
  · apply Ideal.subset_span
    left
    exact ⟨0, by ring⟩
  · simp

theorem addVal_le_of_ordHyp {l M R v : ℕ} (hl : l ≠ 0) {f : MvPolynomial (Fin R ⊕ Fin R) O}
    (h : OrdHyp O l M R 0 v f) : IsDiscreteValuationRing.addVal O (f.coeff 0) ≤ v := by
  obtain ⟨Dd, g, h1, h2, u, n, hu, hn, h3⟩ := h
  have hn0 : ∀ i, n i = 0 := fun i => Nat.le_zero.1 (hn i)
  have e1 : MvPolynomial.constantCoeff (f - Dd * g) = 0 := by
    have : Ideal.span (Set.range (fun i : Fin R => (MvPolynomial.X (Sum.inr i) : MvPolynomial (Fin R ⊕ Fin R) O)) ∪
      Set.range (fun i : Fin R => (1 + MvPolynomial.X (Sum.inl i)) ^ (l ^ M) - 1)) ≤
        RingHom.ker MvPolynomial.constantCoeff := by
      rw [Ideal.span_le]
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩) <;> simp
    exact this h1
  have e2 : MvPolynomial.constantCoeff (Dd.map (IsLocalRing.residue O) - u * ∏ i, MvPolynomial.X (Sum.inl i) ^ n i) = 0 := by
    have : Ideal.span (Set.range fun q =>
          (MvPolynomial.X q : MvPolynomial (Fin R ⊕ Fin R) (IsLocalRing.ResidueField O)) ^ (l ^ M)) ≤
        RingHom.ker MvPolynomial.constantCoeff := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp [hl]
    exact this h3
  simp only [hn0, pow_zero, Finset.prod_const_one, mul_one, map_sub, MvPolynomial.constantCoeff_map, sub_eq_zero] at e2
  have hD : IsUnit (MvPolynomial.constantCoeff Dd) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, e2]
    exact hu
  rw [map_sub, map_mul, sub_eq_zero] at e1
  have : f.coeff 0 = MvPolynomial.constantCoeff Dd * g.coeff 0 := e1
  rw [this, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_eq_zero_iff.2 hD, zero_add]
  exact h2

theorem not_ordHyp_X {l M v : ℕ} (hl : l ≠ 0) : ¬ OrdHyp O l M 1 0 v (MvPolynomial.X (Sum.inr 0)) := by
  intro h
  have := addVal_le_of_ordHyp O hl h
  simp at this

end Ord

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

open Classical in

theorem exists_isCoord (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (M : ℕ) : ∃ d, IsCoord Y i M d := by
  let c : ∀ (Q : Finset (PlE D.host)) (P : PlE D.host), P ∈ Q → (GE N →* Multiplicative (ZMod (X.l i ^ M))) :=
    fun Q P hP => (AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ : ↥Q => ZMod (X.l i ^ M)) ⟨P, hP⟩)).comp
      (Y.delU i Q M)
  refine ⟨fun P => if h : ∃ Q, ConjCl (D := D) Q ∧ P ∈ Q then c h.choose P h.choose_spec.2 else 1, ?_⟩
  intro Q hQ P hP σ
  have h : ∃ Q, ConjCl (D := D) Q ∧ P ∈ Q := ⟨Q, hQ, hP⟩
  simp only [dif_pos h]
  have hU : ConjCl (D := D) (Q ∪ h.choose) := by
    intro P hP P' hc
    rcases Finset.mem_union.1 hP with h1 | h1
    · exact Finset.mem_union_left _ (hQ P h1 P' hc)
    · exact Finset.mem_union_right _ (h.choose_spec.1 P h1 P' hc)
  rw [Y.delU_res i M Q (Q ∪ h.choose) Finset.subset_union_left hQ hU σ P hP]
  exact (Y.delU_res i M h.choose (Q ∪ h.choose) Finset.subset_union_right h.choose_spec.1 hU σ P h.choose_spec.2).symm

open Classical in
theorem toLam_surjective (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] : Function.Surjective (toLam X i M ι) := by
  have hl : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ (Fact.out : (X.l i).Prime).ne_zero⟩
  have key : ∀ g : Del X i M ι, MonoidAlgebra.of (X.O0 i) (Del X i M ι) g ∈ (toLam X i M ι).range := by
    intro g
    refine ⟨∏ q, (1 + MvPolynomial.X q) ^ (Multiplicative.toAdd g q).val, ?_⟩
    simp only [toLam, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_prod, map_pow, map_add, map_one, MvPolynomial.aeval_X, add_sub_cancel]
    simp only [← map_pow, ← map_prod]
    congr 1
    apply Multiplicative.toAdd.injective
    ext q
    simp only [toAdd_prod, toAdd_pow, toAdd_ofAdd, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero]
    simp [nsmul_eq_mul]
  intro x
  have : x ∈ (toLam X i M ι).range := by
    induction x using MonoidAlgebra.induction_on with
    | of g => exact key g
    | add f g hf hg => exact add_mem hf hg
    | smul r f hf => exact Subalgebra.smul_mem _ hf r
  exact this

theorem galois_export_of_matrix_det_bounds (bkP : BKPh X) (hS : ThmS bkP) (hS4 : SelmerLengthsByDeterminant bkP) (h3 : ResidualBoundOddPrimes bkP) (hC : ThmC bkP) : GaloisSideTwistedSelmerAuxiliaryPrimes bkP := by
  intro i T hT
  have hO : OrdBound bkP i (IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i)) := by
    rcases Nat.eq_zero_or_pos (nu X i) with h | h
    · rw [h, pow_zero, IsDiscreteValuationRing.addVal_one]
      exact h3 i h
    · exact hC i h
  obtain ⟨R, Dd, M₀, h⟩ := hO T hT
  refine ⟨R, Dd, max M₀ 1, le_max_right _ _, fun M hM H S d hd z hz H' h1 h2 A => ?_⟩
  obtain ⟨P, hA, hSt, hF⟩ := h M (le_of_max_le_left hM) H S d hd z hz H' h1 h2 A
  refine ⟨P, hA, hSt, fun s hs Q hQ => ?_⟩
  have hA0 : SlopeTestRemainingChoices X i M ∅ P (fun q => d (P q)) :=
    ⟨fun q v hv => by
      obtain ⟨a, b, c, d', -, f⟩ := hA.1 q v hv
      exact ⟨a, b, c, d', by simp, f⟩, hA.2⟩
  obtain ⟨a, Φ, hΦ, -⟩ := hS i s (hT s hs) M _ P _ Q (le_of_max_le_right hM) hA0 hQ
  obtain ⟨F, hFd⟩ := toLam_surjective i M (Fin R ⊕ Fin R) Φ.det
  exact ⟨F, hS4 i s M _ P _ Q (le_of_max_le_right hM) hA0 hQ a Φ hΦ F hFd, hF s hs Q hQ a Φ hΦ F hFd⟩

end GlobalTheory.TwSys.Test

end
