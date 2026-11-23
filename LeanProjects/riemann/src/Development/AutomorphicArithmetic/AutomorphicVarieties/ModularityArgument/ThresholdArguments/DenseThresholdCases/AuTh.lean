import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuChi
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
theorem UpperTheory.V.Ws.isAlgChar_pushCh_th_of_good :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ ι : PadicAlgCl l ≃+* ℂ, Af.IsAlgChar ι (W.pushCh (algebraMap c.O (PadicAlgCl l)) D.th) := by
  intro hP Ω _ _ _ l hl c D h ι
  have hc : AdicCont (maximalIdeal c.O) fun g => (D.th g : c.O) := (GradeZeroInterpolatingElement.facts D h).2.2.2.2.2.2.2.2.2.2.1 0
  refine (_root_.UpperTheory.V.Af.algOfCyc_s hP ℚ Ω l ι).1 _ (auCont c D.th hc) fun w _ => ?_
  obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
  obtain ⟨m, hm, hx⟩ := h.xi_ord
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun e => hl.out.ne_one (by simpa [e] using hm)
  haveI : CompactSpace (G ℚ Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[ℚ] Ω))
  haveI : Finite (G ℚ Ω ⧸ D.ψ.ker) := Subgroup.quotient_finite_of_isOpen _ h.psi_open
  have hn : 0 < D.ψ.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hl1 : 0 < l - 1 := Nat.sub_pos_of_lt hl.out.one_lt
  refine ⟨A, hA, (D.e : ℤ) + 1, (l - 1) * m * D.ψ.ker.index, by positivity, fun s _ => ?_⟩
  have h1 : D.om s ^ (l - 1) = 1 := DFunLike.congr_fun h.om_pow s
  have h2 : D.ξ s ^ m = 1 := DFunLike.congr_fun hx s
  have h3 : D.ψ s ^ D.ψ.ker.index = 1 := by
    rw [← map_pow]
    exact D.ψ.ker.pow_index_mem s
  have e : D.th s * chiO ℚ Ω l c.O s ^ (-((D.e : ℤ) + 1)) = (D.om s)⁻¹ * D.ξ s * D.ψ s := by
    have e0 : D.th s = chiO ℚ Ω l c.O s * (D.om s)⁻¹ * D.ξ s * (chiO ℚ Ω l c.O s ^ (D.e : ℤ) * D.ψ s) := rfl
    rw [e0, zpow_neg, mul_inv_eq_iff_eq_mul, zpow_add_one]
    ac_rfl
  have e2 : (D.th s * chiO ℚ Ω l c.O s ^ (-((D.e : ℤ) + 1))) ^ ((l - 1) * m * D.ψ.ker.index) = 1 := by
    rw [e, mul_pow, mul_pow, inv_pow, pow_mul' (D.ψ s), h3, pow_mul (D.ξ s), pow_mul' (D.ξ s), h2, pow_mul (D.om s),
      pow_mul (D.om s), h1]
    simp
  rw [← (auChi ℚ Ω c).1]
  have := congrArg (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom) e2
  rw [map_pow, map_mul, map_zpow, map_one] at this
  exact this
end
