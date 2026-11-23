import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ChainBetweenPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentialModularityTower

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
namespace UpperTheory.V.Ws.Chn
section Abs
variable {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [Field k] {Φ : Fr O Γ} {a : O →+* k}
end Abs
section In
variable {ι Γ R : Type} [Group Γ] [CommRing R] {P P' : PD ι Γ R}
end In
section Map
variable {O Γ R R' : Type} [CommRing O] [Group Γ] [CommRing R] [CommRing R'] {Φ : Fr O Γ} {a : O →+* R}
end Map
section Gal
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}
theorem seed_res_alt (T : Tower D) (𝔞 : Amb l) {ι : PadicAlgCl l ≃+* ℂ} {c₁ : Coef l} {h : c.O ≤ c₁.O}
    {Q : PD T.ι (G T.F Ω) c₁.O} (hQ : T.SeedPairAlt ι h Q) : (T.fr ∅).IsRes (𝔞.red c) (Q.map (𝔞.red c₁)) := by
  have h1 : (T.fr ∅).IsRes ((residue c₁.O).comp (inc h)) (Q.map (residue c₁.O)) := by
    refine ⟨pair_map hQ.pair _, hQ.res, fun i j n => ?_⟩
    have h2 := (hQ.cont i j 1).comp (Ideal.Quotient.lift (maximalIdeal c₁.O ^ 1) (residue c₁.O)
      fun x hx => (residue_eq_zero_iff x).2 (by rwa [pow_one] at hx))
    exact h2.comp (Ideal.Quotient.mk ((⊥ : Ideal (ResidueField c₁.O)) ^ n))
  have h2 := (chainMap (T.fr ∅) _ (𝔞.j c₁) _).1.2 h1
  have e1 : (𝔞.j c₁).comp ((residue c₁.O).comp (inc h)) = 𝔞.red c :=
    RingHom.ext fun x => congrArg (residue 𝔞.V) (𝔞.compat c c₁ h x)
  rw [e1] at h2
  exact h2
end Gal
end UpperTheory.V.Ws.Chn
end
