import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.StatementsFibreCompDimZ
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.OfChartPointSecPointSpecChart
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteIntegralClosureCharZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial IsDedekindDomain

theorem ringKrullDim_quotient_le_of_minimalPrimes {R : Type*} [CommRing R] (J : Ideal R)
    (k : WithBot ℕ∞) (h : ∀ W ∈ J.minimalPrimes, ringKrullDim (R ⧸ W) ≤ k) :
    ringKrullDim (R ⧸ J) ≤ k := by
  rw [ringKrullDim_quotient]
  refine iSup_le fun l => ?_
  obtain ⟨W, hW, hle⟩ := Ideal.exists_minimalPrimes_le (show J ≤ l.head.1.asIdeal from l.head.2)
  let l' : LTSeries (PrimeSpectrum.zeroLocus (R := R) W) :=
    ⟨l.length, fun i => ⟨(l i).1, show (W : Set R) ⊆ (l i).1.asIdeal from hle.trans (l.head_le i)⟩,
      fun i => l.step i⟩
  calc (l.length : WithBot ℕ∞) = l'.length := rfl
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := R) W) := Order.LTSeries.length_le_krullDim l'
    _ = ringKrullDim (R ⧸ W) := (ringKrullDim_quotient W).symm
    _ ≤ k := h W hW

section Fibres

variable {σ : Type} [Fintype σ] {P : Ideal (MvPolynomial σ ℤ)}

theorem fibreComponent_dim_eq (hP : P.IsPrime) (hPC : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥)
    {p : ℕ} (hp : p.Prime) {W : Ideal (MvPolynomial σ ℤ)}
    (hW : W ∈ (P ⊔ Ideal.span {(C (p : ℤ) : MvPolynomial σ ℤ)}).minimalPrimes) :
    ∃ m : ℕ, ringKrullDim (MvPolynomial σ ℤ ⧸ W) = m ∧ ∀ q : ℕ, q.Prime →
      ∀ W' ∈ (P ⊔ Ideal.span {(C (q : ℤ) : MvPolynomial σ ℤ)}).minimalPrimes,
        ringKrullDim (MvPolynomial σ ℤ ⧸ W') = m := by
  have := hP
  obtain ⟨n, f, hfC⟩ : ∃ (n : ℕ) (f : MvPolynomial σ ℤ ≃+* MvPolynomial (Fin n) ℤ),
      ∀ a : ℤ, f (C a) = C a :=
    ⟨_, (renameEquiv ℤ (Fintype.equivFin σ)).toRingEquiv, fun a => rename_C _ _⟩
  have hPn : (P.map (f : MvPolynomial σ ℤ →+* MvPolynomial (Fin n) ℤ)).IsPrime :=
    Ideal.map_isPrime_of_equiv f
  have hPnC : (P.map (f : MvPolynomial σ ℤ →+* MvPolynomial (Fin n) ℤ)).comap (C : ℤ →+* MvPolynomial _ ℤ) = ⊥ := by
    ext a
    rw [Ideal.mem_comap, Ideal.map_comap_of_equiv, Ideal.mem_comap,
      show f.symm (C a) = C a from f.symm_apply_eq.mpr (hfC a).symm, ← Ideal.mem_comap, hPC]
  have key : ∀ q : ℕ, q.Prime →
      ∀ W ∈ (P ⊔ Ideal.span {(C (q : ℤ) : MvPolynomial σ ℤ)}).minimalPrimes,
        ringKrullDim (MvPolynomial σ ℤ ⧸ W) = ringKrullDim (MvPolynomial (Fin n) ℚ ⧸
          (P.map (f : MvPolynomial σ ℤ →+* MvPolynomial (Fin n) ℤ)).map (MvPolynomial.map (algebraMap ℤ ℚ))) ∧
        ∃ m : ℕ, ringKrullDim (MvPolynomial σ ℤ ⧸ W) = m := by
    intro q hq W hW
    clear hp
    let v : HeightOneSpectrum ℤ := ⟨Ideal.span {(q : ℤ)},
      (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hq),
      by simpa using hq.ne_zero⟩
    have hmap : (P ⊔ Ideal.span {(C (q : ℤ) : MvPolynomial σ ℤ)}).map (f : MvPolynomial σ ℤ →+* MvPolynomial (Fin n) ℤ) =
        P.map (f : MvPolynomial σ ℤ →+* MvPolynomial (Fin n) ℤ) ⊔ Ideal.map (C : ℤ →+* MvPolynomial _ ℤ) v.asIdeal := by
      rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
        RingEquiv.coe_toRingHom, hfC]
    have hWn : W.map (f : MvPolynomial σ ℤ →+* MvPolynomial (Fin n) ℤ) ∈
        (P.map (f : MvPolynomial σ ℤ →+* MvPolynomial (Fin n) ℤ) ⊔ Ideal.map C v.asIdeal).minimalPrimes := by
      rw [← hmap, Ideal.minimalPrimes_map_of_surjective (f := (f : MvPolynomial σ ℤ →+* MvPolynomial (Fin n) ℤ)) f.surjective,
        RingHom.ker_coe_equiv, sup_bot_eq]
      exact ⟨W, hW, rfl⟩
    have hle := le_sup_right.trans hWn.1.2
    have hiso : ringKrullDim (MvPolynomial σ ℤ ⧸ W) =
        ringKrullDim (MvPolynomial (Fin n) ℤ ⧸ W.map (f : MvPolynomial σ ℤ →+* MvPolynomial (Fin n) ℤ)) :=
      ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv W _ f rfl)
    refine ⟨?_, ?_⟩
    · rw [hiso, ringKrullDim_eq_of_ringEquiv (Vertical.quotientResidueEquiv v _ hle)]
      exact Vertical.FibreCompDim.full ℤ ℚ _ _ _ v hPn hPnC hWn
    · rw [hiso]
      exact Vertical.exists_ringKrullDim_quotient_eq_nat v _ hWn.1.1 hle
  obtain ⟨h1, m, hm⟩ := key p hp W hW
  exact ⟨m, hm, fun q hq W' hW' => (key q hq W' hW').1.trans (h1.symm.trans hm)⟩

omit [Fintype σ] in

theorem fibreComponent_dim_succ_le (hP : P.IsPrime) (hPC : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥)
    {p : ℕ} (hp : p.Prime) {W : Ideal (MvPolynomial σ ℤ)}
    (hW : W ∈ (P ⊔ Ideal.span {(C (p : ℤ) : MvPolynomial σ ℤ)}).minimalPrimes) :
    ringKrullDim (MvPolynomial σ ℤ ⧸ W) + 1 ≤ ringKrullDim (MvPolynomial σ ℤ ⧸ P) := by
  have hCp : (C (p : ℤ) : MvPolynomial σ ℤ) ∉ P := fun h => by
    have : (p : ℤ) ∈ P.comap (C : ℤ →+* MvPolynomial σ ℤ) := h
    rw [hPC, Ideal.mem_bot] at this
    exact hp.ne_zero (by exact_mod_cast this)
  exact ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor (le_sup_left.trans hW.1.2))
    (Ideal.Quotient.factor_surjective _) (r := Ideal.Quotient.mk P (C (p : ℤ)))
    (mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]))
    (by
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hW.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl)))

theorem ringKrullDim_le_of_fibreComponents (k : WithBot ℕ∞)
    (h : ∀ q : ℕ, q.Prime → ∀ W ∈ (P ⊔ Ideal.span {(C (q : ℤ) : MvPolynomial σ ℤ)}).minimalPrimes,
      ringKrullDim (MvPolynomial σ ℤ ⧸ W) ≤ k) :
    ringKrullDim (MvPolynomial σ ℤ ⧸ P) ≤ k + 1 := by
  rw [ringKrullDim_le_iff_isMaximal_height_le]
  intro M hM
  have := Model.isJacobsonRing_int
  let := Ideal.Quotient.field M
  let g : MvPolynomial σ ℤ →+* (MvPolynomial σ ℤ ⧸ P) ⧸ M :=
    (Ideal.Quotient.mk M).comp (Ideal.Quotient.mk P)
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  have hI := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' (g.comp C)
    (MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing g hg) ⊥
  obtain ⟨q, hq, hqI⟩ := (Ideal.isPrime_int_iff.mp hI.isPrime).resolve_left
    (Ring.ne_bot_of_isMaximal_of_not_isField hI Int.not_isField)
  have hqM : Ideal.Quotient.mk P (C (q : ℤ)) ∈ M := by
    have : (q : ℤ) ∈ (⊥ : Ideal ((MvPolynomial σ ℤ ⧸ P) ⧸ M)).comap (g.comp C) := by
      rw [hqI]
      exact Ideal.subset_span rfl
    rwa [Ideal.mem_comap, Ideal.mem_bot, RingHom.comp_apply, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem] at this
  refine (Ideal.height_le_ringKrullDim_quotient_add_one hqM).trans (add_le_add_left ?_ 1)
  have hspan : Ideal.span {Ideal.Quotient.mk P (C (q : ℤ))} =
      (Ideal.span {(C (q : ℤ) : MvPolynomial σ ℤ)}).map (Ideal.Quotient.mk P) := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [hspan, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup P _)]
  exact ringKrullDim_quotient_le_of_minimalPrimes _ _ (h q hq)

end Fibres

theorem FibreCompDimZ.proof : FibreCompDimZ.Statement := by
  intro σ _ P hP hPC d p hp hdim W hW
  obtain ⟨m, hm, hall⟩ := fibreComponent_dim_eq hP hPC hp hW
  have h1 := fibreComponent_dim_succ_le hP hPC hp hW
  have h2 := ringKrullDim_le_of_fibreComponents (P := P) (m : WithBot ℕ∞)
    fun q hq W' hW' => (hall q hq W' hW').le
  rw [hm, hdim] at h1
  rw [hdim] at h2
  rw [hm]
  have h1' : m + 1 ≤ d + 1 := by exact_mod_cast h1
  have h2' : d + 1 ≤ m + 1 := by exact_mod_cast h2
  exact_mod_cast (by omega : m = d)

end GroundTheory.Heights₂.Heights
