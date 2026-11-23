import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsAut4
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.CuspidalRankFourRegularAlgebraicTotallyComplex
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ArithmeticPointDecomposition

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp
namespace UpperTheory.V.Ws
namespace Amb
variable {l : ℕ} [Fact l.Prime] (𝔞 : Amb l)
end Amb
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
def PurityAtPoints (D : Raw Ω c) (ι : PadicAlgCl l ≃+* ℂ) : Prop :=
  ∀ (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e → ∀ r u, KPair D 𝔞 r u → Star (mapRep 𝔞.toK r) →
    _root_.UpperTheory.GalN.V.PureW ι (mapRep ((e : 𝔞.K →+* _).comp 𝔞.toK) r)
def AutmAlt (D : Raw Ω c) (ι : PadicAlgCl l ≃+* ℂ) : Prop :=
  ∀ (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e → ∀ r u, KPair D 𝔞 r u → Irr (mapRep 𝔞.toK r) →
    _root_.UpperTheory.V.Aut.IsAut4Alt ι (mapRep ((e : 𝔞.K →+* _).comp 𝔞.toK) r)
namespace Tower
variable {D : Raw Ω c} (T : Tower D)
structure IsSeedAlt (ι : PadicAlgCl l ≃+* ℂ) (P : PD T.ι (G T.F Ω) (PadicAlgCl l)) : Prop where
  irr : Irr (P.r.comp T.G'.subtype)
  aut : ∃ (h : Fin 4 → ℤ) (κ : G T.L Ω →* (PadicAlgCl l)ˣ) (π : CuspSub T.L 4) (a : ℤ) (k : ℕ),
    (∀ i : Fin 3, ∃ n : ℤ, 2 ≤ n ∧ h i.castSucc = h i.succ + 2 * n) ∧ T.Wts h P ∧ Continuous κ ∧ 0 < k ∧ Even (a + h 0) ∧
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := T.L) A, (κ s ^ 2 * cycBar T.L Ω l s ^ (-a)) ^ k = 1) ∧
    _root_.UpperTheory.V.Z.Win.Birth.CuspidalRankFourRegularAlgebraicTotallyComplex π ∧ Af.AttC ι (Af.tw (P.r.comp (resLe T.F_le)).toHomUnits κ) π
structure SeedPairAlt (ι : PadicAlgCl l ≃+* ℂ) {c₁ : Coef l} (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O) : Prop where
  pair : (T.fr ∅).IsPair (inc h) Q
  cont : Q.Cont (maximalIdeal c₁.O)
  res : (T.fr ∅).Res ((residue c₁.O).comp (inc h)) (Q.map (residue c₁.O))
  seed : T.IsSeedAlt ι (Q.map (algebraMap c₁.O (PadicAlgCl l)))
structure PotentialModularityTower (ι : PadicAlgCl l ≃+* ℂ) {c' : Coef l} {h : c.O ≤ c'.O} (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B) : Prop where
  fin : ∃ n : ℕ, maximalIdeal X.B ^ n ≤ J ⊔ (maximalIdeal c'.O).map (algebraMap c'.O X.B) ⊔
    Ideal.span {b | ∃ v i, ∃ s ∈ Ine (F := T.F) (T.pl v), b = X.ψ v i s - 1}
  p1 : ∀ (k : Type) [Field k] [Finite k] [Algebra c'.O k] (y : X.A →ₐ[c'.O] PowerSeries k),
    (∀ b ∈ maximalIdeal X.B, PowerSeries.constantCoeff (y (algebraMap X.B X.A b)) = 0) →
    (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
    (∀ v i j, i ≠ j → ∃ s ∈ T.U1 v, y (X.P.ψ v i s) ≠ y (X.P.ψ v j s)) →
    Irr (mapRep ((algebraMap (PowerSeries k) (FractionRing (PowerSeries k))).comp (y : X.A →+* PowerSeries k)) X.P.r) →
    X.LocZero J (y : X.A →+* PowerSeries k)
  seed : ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, T.IsSeedAlt ι (X.P.map (y : X.A →+* PadicAlgCl l)) →
    X.LocZero J (y : X.A →+* PadicAlgCl l)
  pur : ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
    T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) →
    ∀ r : G ℚ Ω →* M4 (PadicAlgCl l), r.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r → _root_.UpperTheory.GalN.V.PureW ι r
  aut : ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
    T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) →
    ∀ r : G ℚ Ω →* M4 (PadicAlgCl l), r.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r → Continuous r → D.Mult r →
      Irr (r.comp T.L.fixingSubgroup.subtype) → _root_.UpperTheory.V.Aut.IsAut4Alt ι r
end Tower
def SeedIIAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D),
    Ctx2 D → T.Ok → T.Two → T.Deep → ∀ ι : PadicAlgCl l ≃+* ℂ,
    ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPairAlt ι h Q ∧
      Fr.InV (Φ := T.fr ∅) (Q.map (residue c₁.O)) ∧
      (Ent (Q.map (residue c₁.O)).r (-wAl) ∨ (Ent (Q.map (residue c₁.O)).r wBe ∧ Ent (Q.map (residue c₁.O)).r (-wTh)))
def PMExAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D),
    T.Fit → T.Deep → ∀ ι : PadicAlgCl l ≃+* ℂ, ∃ c₁ : Coef l, ∀ (c' : Coef l) (h : c.O ≤ c'.O), c₁.O ≤ c'.O →
      ∀ X : Space (T.fr ∅) (inc h), ∃ J, T.PotentialModularityTower ι X J
def ProModAlt (D : Raw Ω c) (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (r : G ℚ Ω →* M4 𝔞.V) : Prop :=
  ∃ (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B) (y : X.A →+* 𝔞.V)
    (r₁ : G ℚ Ω →* M4 𝔞.V), T.Fit ∧ T.Deep ∧ T.PotentialModularityTower ι X J ∧ y.comp (algebraMap c'.O X.A) = 𝔞.a c' ∧
    (∀ b ∈ maximalIdeal X.B, y (algebraMap X.B X.A b) ∈ maximalIdeal 𝔞.V) ∧ (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) ∧
    IsConj4 (mapRep 𝔞.toK r) (mapRep 𝔞.toK r₁) ∧ (∀ g, IsGSp (𝔞.a c (D.th g)) (r₁ g)) ∧
    r₁.comp (resQ T.F) = (X.P.map y).r ∧
    ∀ v i, ∀ s ∈ Ine (F := T.F) (T.pl v), y (X.P.ψ v i s) = 𝔞.a c (D.ps i (resQ T.F s))
end UpperTheory.V.Ws
end
end
