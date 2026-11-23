import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.PromodularityCaseThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentialModularityTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsAut4

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
namespace UpperTheory.V.Cu
section
variable {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) {R : Type} [CommRing R] (a : O →+* R)
end
section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}
end
def SeedIVAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T₀ : Tower D),
    Ctx3 D → T₀.Ok → Four T₀ → ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l),
    ∃ (w : ℕ) (s : PD T₀.ι (G T₀.F Ω) 𝔞.k), w.Prime ∧ T₀.Splits w ∧ (T₀.fr {w}).IsRes (𝔞.red c) s ∧ Supp nM s.r ∧
      ∀ (T : Tower D) (hT : T₀.Le T), T.Ok → Dies l w T.F →
        ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPairAlt ι h Q ∧ T₀.OverT hT s (Q.map (𝔞.red c₁)) ∧
          InA (Q.map (𝔞.red c₁)) ∧ Ent (Q.map (𝔞.red c₁)).r (-wBe) ∧ Ent (Q.map (𝔞.red c₁)).r (-wTh)
def ChainRankFour : Prop :=
  CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (ι : PadicAlgCl l ≃+* ℂ) (c' : Coef l) (h : c.O ≤ c'.O)
    (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B), T.PotentialModularityTower ι X J → ∀ C : ℕ, (T.fr ∅).Bounds ((residue c'.O).comp (inc h)) T.d C →
    30 * (C + 1) * (C + 1) ≤ T.d → ∀ x : X.A →ₐ[c'.O] ResidueField c'.O,
      (T.fr ∅).IsRes ((residue c'.O).comp (inc h)) (X.P.map (x : X.A →+* _)) →
      Good4 (T.fr ∅) ((residue c'.O).comp (inc h)) (X.P.map (x : X.A →+* _)) →
      X.SomeIn J (RingHom.ker x) → X.AllIn J (RingHom.ker x)
def RankFourChainReductionDense : Prop :=
  CohomologyHyp → HFit → _root_.UpperTheory.V.Cu.SeedIVAlt → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T₀ : Tower D), Ctx3 D → T₀.Ok → Four T₀ → TameL l T₀.F →
    ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (c₀ : PD Unit (G ℚ Ω) 𝔞.k), LatShape D T₀.pr (resQ T₀.F T₀.g0) (𝔞.red c) c₀ →
      ∃ T₁ : Tower D, T₀.Le T₁ ∧ TameL l T₁.F ∧ ∀ T : Tower D, T₁.Le T → T.Deep →
        ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPairAlt ι h Q ∧
          ∀ c₀' : PD T.ι (G T.F Ω) 𝔞.k, T.OverQ c₀ c₀' → (T.fr ∅).IsRes (𝔞.red c) c₀' →
            Chain4 (T.fr ∅) (𝔞.red c) c₀' (Q.map (𝔞.red c₁))
def PromodularityCaseThreeDense : Prop :=
  CohomologyHyp → UpperTheory.V.Published.FerreroWashington → HFit → _root_.UpperTheory.V.Cu.SeedIVAlt → _root_.UpperTheory.V.Ws.PMExAlt → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx3 D →
    ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) r u, KPair D 𝔞 r u → Star (mapRep 𝔞.toK r) → _root_.UpperTheory.V.Ws.ProModAlt D ι 𝔞 r
def AutomorphyRankFourDense : Prop :=
  CohomologyHyp → UpperTheory.V.Published.FerreroWashington → HFit → _root_.UpperTheory.V.Ws.SeedIIAlt → _root_.UpperTheory.V.Cu.SeedIVAlt → _root_.UpperTheory.V.Ws.PMExAlt → _root_.UpperTheory.V.Aut.SymplecticFourImageDense
end UpperTheory.V.Cu
end
end
