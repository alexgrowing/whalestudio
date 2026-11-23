import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaComplexConjugationCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatumStatement

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.TwoTorsionPt

theorem not_integral_half {N : ℕ} (hN : Odd N) {x : ℂ} (hx : IsIntegral ℤ x)
    (h : x + (starRingEnd ℂ) x = (N : ℂ) / 2) : False := by
  have h1 : IsIntegral ℤ ((starRingEnd ℂ) x) := hx.map (starRingEnd ℂ).toIntAlgHom
  have h2 : IsIntegral ℤ (algebraMap ℚ ℂ ((N : ℚ) / 2)) := by
    have : algebraMap ℚ ℂ ((N : ℚ) / 2) = (N : ℂ) / 2 := by simp
    rw [this, ← h]; exact hx.add h1
  have h3 : IsIntegral ℤ ((N : ℚ) / 2) :=
    (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).1 h2
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
  have h4 : (N : ℚ) = 2 * (m : ℚ) := by
    have : (m : ℚ) = (N : ℚ) / 2 := by simpa using hm
    rw [this]; ring
  have h5 : (N : ℤ) = 2 * m := by exact_mod_cast h4
  obtain ⟨k, hk⟩ := hN
  omega

theorem isTwoTorsionCMPoint_of_odd_multiple (D : D7) (Λ : AddSubgroup ℂ) {δ : ℂ} (hδ : δ ≠ 0) {N : ℕ} (hN : Odd N)
    (hmem : δ * N ∈ Λ) (hint : ∀ w ∈ Λ, ∃ x : ℂ, IsIntegral ℤ x ∧ w = δ * x) :
    GL3Theta.IsTwoTorsionPointUnkilled D Λ (δ * N / 2) := by
  refine ⟨?_, ?_, ?_⟩
  · have : 2 * (δ * N / 2) = δ * N := by ring
    rw [this]; exact hmem
  · intro h
    obtain ⟨x, hx, e⟩ := hint _ h
    have e' : x = ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * (N / 2) := by
      apply mul_left_cancel₀ hδ
      rw [← e]; ring
    refine not_integral_half hN hx ?_
    rw [e']
    simp only [map_mul, map_div₀, map_add, map_one, Complex.conj_I, Complex.conj_ofReal,
      map_natCast, map_ofNat]
    ring
  · intro h
    obtain ⟨x, hx, e⟩ := hint _ h
    have e' : x = ((1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * (N / 2) := by
      apply mul_left_cancel₀ hδ
      rw [← e]; ring
    refine not_integral_half hN hx ?_
    rw [e']
    simp only [map_mul, map_div₀, map_sub, map_one, Complex.conj_I, Complex.conj_ofReal,
      map_natCast, map_ofNat]
    ring

theorem lamOf_integral (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    ∀ w ∈ lamOf D cc δ, ∃ x : ℂ, IsIntegral ℤ x ∧ w = δ * x := by
  intro w hw
  unfold lamOf at hw
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, -, rfl⟩ := hw
    refine ⟨_, ?_, rfl⟩
    have h0 : IsIntegral ℤ (c : D.host.K) := c.2
    exact h0.map (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).toIntAlgHom
  | zero => exact ⟨0, isIntegral_zero, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    exact ⟨x + y, hx.add hy, by ring⟩
  | neg a _ ha =>
    obtain ⟨x, hx, rfl⟩ := ha
    exact ⟨-x, hx.neg, by ring⟩

theorem norm_mem_lamOf (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    δ * (Ideal.absNorm cc : ℕ) ∈ lamOf D cc δ := by
  refine AddSubgroup.subset_closure ⟨((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K), Ideal.absNorm_mem cc, ?_⟩
  simp

theorem odd_norm {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ) :
    Odd (Ideal.absNorm cc) :=
  Nat.coprime_two_right.1 (Nat.Coprime.coprime_mul_right_right h.1.2)

theorem delta_ne {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ) : δ ≠ 0 :=
  (GlobalTheory.T.idealPeriodLattice_of_curveDatum D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ h).2.1

theorem exists_lamOf {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ) :
    ∃ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 :=
  ⟨_, isTwoTorsionCMPoint_of_odd_multiple D _ (delta_ne h) (odd_norm h) (norm_mem_lamOf D cc δ) (lamOf_integral D cc δ)⟩

theorem exists_bar {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ) (Λ : AddSubgroup ℂ)
    (hΛ : Λ.map (starRingEnd ℂ).toAddMonoidHom = lamOf D cc δ) :
    ∃ t0, GL3Theta.IsTwoTorsionPointUnkilled D Λ t0 := by
  have hδ : (starRingEnd ℂ) δ ≠ 0 := by simpa using delta_ne h
  refine ⟨_, isTwoTorsionCMPoint_of_odd_multiple D Λ hδ (odd_norm h) ?_ ?_⟩
  · have h1 := norm_mem_lamOf D cc δ
    rw [← hΛ] at h1
    obtain ⟨w, hw, e⟩ := h1
    have e1 : (starRingEnd ℂ) w = δ * (Ideal.absNorm cc : ℕ) := e
    have e2 : w = (starRingEnd ℂ) δ * (Ideal.absNorm cc : ℕ) := by
      rw [← Complex.conj_conj w, e1, map_mul, map_natCast]
    rw [← e2]; exact hw
  · intro w hw
    have h1 : (starRingEnd ℂ) w ∈ lamOf D cc δ := by
      rw [← hΛ]; exact ⟨w, hw, rfl⟩
    obtain ⟨x, hx, e⟩ := lamOf_integral D cc δ _ h1
    refine ⟨(starRingEnd ℂ) x, hx.map (starRingEnd ℂ).toIntAlgHom, ?_⟩
    rw [← Complex.conj_conj w, e, map_mul]

theorem exists_extension (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) :
    ∃ (M' : IntermediateField ℚ ℂ) (ρ' : M' →ₐ[ℚ] ℂ), (∀ x : ℂ, IsAlgebraic ℚ x → x ∈ M') ∧
      ∀ x ∈ M, x ∈ M' ∧ ρ' (TaylorLogMetric.liftM M' x) = ρ (TaylorLogMetric.liftM M x) := by
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic (K := ℚ) (L := M) (M := ℂ)
    (E := algebraicClosure M ℂ) ρ
  refine ⟨(algebraicClosure M ℂ).restrictScalars ℚ, φ, ?_, ?_⟩
  · intro x hx
    exact mem_algebraicClosure_iff.2 (hx.extendScalars (algebraMap ℚ M).injective)
  · intro x hx
    have hx' : x ∈ (algebraicClosure M ℂ).restrictScalars ℚ :=
      (algebraicClosure M ℂ).algebraMap_mem (⟨x, hx⟩ : M)
    refine ⟨hx', ?_⟩
    unfold TaylorLogMetric.liftM
    rw [dif_pos hx', dif_pos hx, ← hφ]
    rfl

theorem exists_point : ∀ D : D7, t0Ex D := by
  intro D cc δ hc
  refine ⟨exists_lamOf hc, ?_⟩
  intro M ρ h2 h3
  obtain ⟨M', ρ', halg, hext⟩ := exists_extension M ρ
  have hl : lamConj M ρ (lamOf D cc δ) = lamConj M' ρ' (lamOf D cc δ) := by
    unfold lamConj
    rw [(hext _ h2).2, (hext _ h3).2]
  rw [hl]
  have hD : DataIn D (tor0 D cc δ) M' := by
    refine ⟨fun τ x => halg _ ?_, (hext _ h2).1, (hext _ h3).1⟩
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (embT D τ).toRatAlgHom
  obtain ⟨hfix, hbar, -⟩ := GlobalTheory.T.cmTheta_complexConjugation_compatible D cc δ hc M' ρ' hD
  rcases hfix with hfix | hfix
  · obtain ⟨cc', δ', hc', -, e⟩ := GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice D cc δ hc M' ρ' hfix hD.2.1 hD.2.2 1 one_pos
    rw [e]
    exact exists_lamOf hc'
  · obtain ⟨cc', δ', hc', -, e⟩ :=
      GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice D cc δ hc M' (rhoBar M' ρ') hfix hD.2.1 hD.2.2 1 one_pos
    refine exists_bar hc' _ ?_
    rw [← e]
    exact (congrArg Tor.abelian₂ hbar).symm

end GlobalTheory.TwoTorsionPt
