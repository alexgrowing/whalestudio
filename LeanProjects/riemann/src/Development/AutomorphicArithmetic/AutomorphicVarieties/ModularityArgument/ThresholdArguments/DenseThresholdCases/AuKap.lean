import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuChi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
theorem UpperTheory.V.Ws.isAlgChar_pushCh_link_kappa :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (ι : PadicAlgCl l ≃+* ℂ), Af.IsAlgChar ι (W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ) := by
  intro hP Ω _ _ _ l _ c D T c' h K ι
  refine (_root_.UpperTheory.V.Af.algOfCyc_s hP T.L Ω l ι).1 _ (auCont c' K.κ K.κ_cont) fun w hw => ?_
  obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
  have hl : A.valuation (l : Ω) < 1 := by
    have h1 := (hA ((l : ℕ) : 𝓞 T.L)).2 hw
    have e : algebraMap T.L Ω (((l : ℕ) : 𝓞 T.L) : T.L) = (l : Ω) := by simp
    rwa [e] at h1
  obtain ⟨a, b, k, hk, -, H⟩ := K.cyc A hl
  refine ⟨A, hA, a, k, hk, fun s hs => ?_⟩
  rw [← (auChi T.L Ω c').1]
  have h2 := congrArg (Units.map (algebraMap c'.O (PadicAlgCl l)).toMonoidHom) (H s hs).1
  rw [map_pow, map_mul, map_zpow, map_one] at h2
  exact h2
end
