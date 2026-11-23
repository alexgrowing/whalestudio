import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDehomNormPIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDehomCharpolyForms
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

namespace DehomNormPIntegral

theorem padicValRat_nonneg_of_mem {p : ℕ} [Fact p.Prime] {q : ℚ}
    (hq : q ∈ (Rat.padicValuation p).valuationSubring) : 0 ≤ padicValRat p q := by
  rw [Valuation.mem_valuationSubring_iff, Rat.padicValuation_le_one_iff] at hq
  rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hq]
  simp

theorem inv_natCast_mem {p : ℕ} [Fact p.Prime] {M : ℕ} (hM : ¬ p ∣ M) :
    ((M : ℚ)⁻¹) ∈ (Rat.padicValuation p).valuationSubring := by
  have hM0 : M ≠ 0 := fun h => hM (h ▸ dvd_zero p)
  rw [Valuation.mem_valuationSubring_iff, Rat.padicValuation_le_one_iff, Rat.inv_natCast_den, if_neg hM0]
  exact hM

theorem mem_range_map_iff {τ : Type*} (V : Subring ℚ) (F : MvPolynomial τ ℚ) :
    F ∈ (map V.subtype).range ↔ ∀ ν, F.coeff ν ∈ V := by
  classical
  constructor
  · rintro ⟨F', rfl⟩ ν
    rw [coeff_map]
    exact (F'.coeff ν).2
  · intro h
    refine ⟨∑ ν ∈ F.support, monomial ν ⟨F.coeff ν, h ν⟩, ?_⟩
    rw [map_sum]
    simp only [map_monomial]
    exact F.support_sum_monomial_coeff

theorem isIntegral_of_le_range {R Ω : Type*} [CommRing R] [CommRing Ω] [Algebra R Ω] (B : Subalgebra ℤ Ω)
    (hB : ∀ b ∈ B, ∃ r, algebraMap R Ω r = b) {x : Ω} (hx : IsIntegral B x) : IsIntegral R x := by
  obtain ⟨Q, hQm, hQ⟩ := hx
  have hl : Q.map (algebraMap B Ω) ∈ Polynomial.lifts (algebraMap R Ω) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro k
    rw [Polynomial.coeff_map]
    exact hB _ (Q.coeff k).2
  obtain ⟨Q', hQ', -, hQ'm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (hQm.map _)
  refine ⟨Q', hQ'm, ?_⟩
  rw [← Polynomial.eval_map, hQ', Polynomial.eval_map]
  exact hQ

theorem coeff_mem_of_dehom_coeff_mem {Ω : Type} [Field Ω] [CharZero Ω] {D : ℕ} {l : Fin (D + 1) → Ω}
    (hgen : ∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0)
    (j : Fin (D + 1)) {N : ℕ} {F : MvPolynomial (Fin (D + 1)) ℚ} (hF : F.IsHomogeneous N) (V : Subring ℚ)
    (hG : ∀ ν, (PullFormsGeneric.dehom j F).coeff ν ∈ V) (μ : Fin (D + 1) →₀ ℕ) : F.coeff μ ∈ V := by
  classical
  have hl := DehomCharpolyForms.ne_zero_of_generic hgen
  have hlj := hl j
  set H := rename Subtype.val (PullFormsGeneric.dehom j F) with hHdef
  set N2 := max N H.totalDegree with hN2
  have hHW : H ∈ (map V.subtype).range := by
    obtain ⟨G', hG'⟩ := (mem_range_map_iff V _).mpr hG
    exact ⟨rename Subtype.val G', by rw [map_rename, hG']⟩
  have hK : DehomCharpolyForms.homog j N2 H = X j ^ (N2 - N) * F := by
    have hF2 : (X j ^ (N2 - N) * F).IsHomogeneous N2 := by
      have := (isHomogeneous_X_pow (R := ℚ) j (N2 - N)).mul hF
      rwa [Nat.sub_add_cancel (le_max_left _ _)] at this
    refine sub_eq_zero.mp (hgen N2 _ ((DehomCharpolyForms.isHomogeneous_homog j N2 H).sub hF2) ?_)
    have hfun : (fun i => if h : i = j then (1 : Ω) else ((fun i => l i / l j) ∘ (Subtype.val : {i // i ≠ j} → Fin (D + 1))) ⟨i, h⟩) =
        fun i => l i / l j := by
      funext i
      split_ifs with h
      · subst h
        exact (div_self (hl _)).symm
      · rfl
    have hval : aeval (fun i => l i / l j) H = aeval (fun i => l i / l j) F := by
      rw [hHdef, aeval_rename, PullFormsGeneric.aeval_dehom, hfun]
    rw [map_sub, DehomCharpolyForms.aeval_homog l j hlj H (le_max_right _ _), hval,
      DehomCharpolyForms.aeval_div_of_isHomogeneous l j hF, map_mul, map_pow, aeval_X, sub_eq_zero]
    have : l j ^ N2 = l j ^ (N2 - N) * l j ^ N := by rw [← pow_add, Nat.sub_add_cancel (le_max_left _ _)]
    rw [this, inv_pow]
    field_simp
  have hKW : X j ^ (N2 - N) * F ∈ (map V.subtype).range := by
    rw [← hK, DehomCharpolyForms.homog]
    refine Subring.sum_mem _ fun e _ => Subring.mul_mem _ ⟨X j ^ (N2 - e), by simp⟩ ?_
    rw [mem_range_map_iff]
    intro ν
    rw [coeff_homogeneousComponent]
    split_ifs
    · exact (mem_range_map_iff V H).mp hHW ν
    · exact V.zero_mem
  have h1 : coeff (μ + Finsupp.single j (N2 - N)) (X j ^ (N2 - N) * F) = coeff μ F := by
    rw [X_pow_eq_monomial, mul_comm, coeff_mul_monomial, mul_one]
  rw [← h1]
  exact (mem_range_map_iff V _).mp hKW _

end DehomNormPIntegral

open DehomCharpolyForms DehomNormPIntegral in

theorem DehomNormPIntegral.proof : DehomNormPIntegral.Statement := by
  intro Ω _ _ D l P _ hP hgen p hp M hM j m u hu c hchom hcp μ
  classical
  have := Fact.mk hp
  have hl := ne_zero_of_generic hgen
  set n := Module.finrank P Ω with hn
  set f := LinearMap.charpoly (Algebra.lmul P Ω u) with hf

  have h0 : algebraMap P Ω (f.coeff 0) = aeval (fun i => l i / l j) (c n) := by
    have := congrArg (fun g => Polynomial.coeff g 0) hcp
    simp only [Polynomial.coeff_map, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow] at this
    rw [this, Finset.sum_eq_single n]
    · simp
    · intro b hb hbn
      have : b < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)) hbn
      rw [if_neg (by omega)]
    · intro h
      simp at h

  have hdet := LinearMap.det_eq_sign_charpoly_coeff (Algebra.lmul P Ω u)
  rw [← Algebra.norm_apply, ← hf] at hdet
  have hc0 : f.coeff 0 = (-1) ^ n * Algebra.norm P u := by
    rw [hdet, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

  let V := (Rat.padicValuation p).valuationSubring
  let σ := {i // i ≠ j}
  have hmemP : ∀ i, l i / l j ∈ P := fun i => hP ▸ IntermediateField.subset_adjoin ℚ _ ⟨i, j, hl j, rfl⟩
  let tP : σ → P := fun i => ⟨l i / l j, hmemP i⟩
  let ω : σ → Ω := fun i => l i / l j
  let _ : Algebra (MvPolynomial σ V) (MvPolynomial σ ℚ) := MvPolynomial.algebraMvPolynomial
  let ψP : MvPolynomial σ V →+* P :=
    (aeval tP : MvPolynomial σ ℚ →ₐ[ℚ] P).toRingHom.comp (algebraMap (MvPolynomial σ V) (MvPolynomial σ ℚ))
  let _ : Algebra (MvPolynomial σ V) P := ψP.toAlgebra
  let _ : Algebra (MvPolynomial σ V) Ω := (P.val.toRingHom.comp ψP).toAlgebra
  have _ : IsScalarTower (MvPolynomial σ V) P Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let fA : MvPolynomial σ ℚ →ₐ[MvPolynomial σ V] Ω :=
    { (aeval ω : MvPolynomial σ ℚ →ₐ[ℚ] Ω).toRingHom with
      commutes' := fun r => by
        show aeval ω _ = P.val (aeval tP _)
        exact (DFunLike.congr_fun (comp_aeval (f := tP) P.val) _).symm }
  have hfA : ∀ G, fA G = aeval ω G := fun _ => rfl
  have hinj : Function.Injective fA := by
    intro a b hab
    exact injective_chart hgen j (by rw [← hfA, ← hfA]; exact hab)
  have halg : ∀ r, algebraMap (MvPolynomial σ V) Ω r =
      aeval ω (map (algebraMap V ℚ) r) := fun r => ((fA.commutes r).symm.trans (hfA _)).trans rfl

  have hB : ∀ b ∈ Algebra.adjoin ℤ (insert ((M : Ω)⁻¹) (Set.range fun i => l i / l j)),
      ∃ r, algebraMap (MvPolynomial σ V) Ω r = b := by
    intro b hb
    have hle : Algebra.adjoin ℤ (insert ((M : Ω)⁻¹) (Set.range fun i => l i / l j)) ≤
        ((Algebra.ofId (MvPolynomial σ V) Ω).range).restrictScalars ℤ := by
      refine Algebra.adjoin_le ?_
      rintro _ (rfl | ⟨i, rfl⟩)
      · refine ⟨C ⟨(M : ℚ)⁻¹, inv_natCast_mem hM⟩, ?_⟩
        show algebraMap _ Ω _ = _
        rw [halg]
        simp
      · by_cases h : i = j
        · subst h
          refine ⟨1, ?_⟩
          show algebraMap _ Ω _ = _
          rw [map_one]
          exact (div_self (hl i)).symm
        · refine ⟨X ⟨i, h⟩, ?_⟩
          show algebraMap _ Ω _ = _
          rw [halg]
          simp [ω]
    obtain ⟨r, hr⟩ := hle hb
    exact ⟨r, hr⟩
  have hu' : IsIntegral (MvPolynomial σ V) u := isIntegral_of_le_range _ hB ((mem_integralClosure_iff _ _).mp hu)
  have hN : IsIntegral (MvPolynomial σ V) (algebraMap P Ω (Algebra.norm P u)) :=
    (Algebra.isIntegral_norm P hu').algebraMap
  have hx : IsIntegral (MvPolynomial σ V) (aeval (fun i => l i / l j) (c n)) := by
    rw [← h0, hc0, map_mul, map_pow, map_neg, map_one]
    exact (isIntegral_one.neg.pow n).mul hN

  have hdeh : aeval ω (PullFormsGeneric.dehom j (c n)) = aeval (fun i => l i / l j) (c n) := by
    rw [PullFormsGeneric.aeval_dehom]
    refine congrArg (fun g => aeval g (c n)) (funext fun i => ?_)
    split_ifs with h
    · subst h
      exact (div_self (hl _)).symm
    · rfl
  have hG : IsIntegral (MvPolynomial σ V) (PullFormsGeneric.dehom j (c n)) :=
    (isIntegral_algHom_iff fA hinj).mp (by rw [hfA, hdeh]; exact hx)
  have hGc : ∀ ν, (PullFormsGeneric.dehom j (c n)).coeff ν ∈ V.toSubring := by
    intro ν
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp (MvPolynomial.isIntegral_iff_isIntegral_coeff.mp hG ν)
    rw [← hy]
    exact y.2
  exact padicValRat_nonneg_of_mem (coeff_mem_of_dehom_coeff_mem hgen j (hchom) V.toSubring hGc μ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
