import Mathlib
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.StrictlyAntitoneWeights.SigThreeSetFiniteOverField

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TV NumberField IsDedekindDomain Polynomial

namespace Formalism.MainNotions.V.Pf.V3

variable {D : D7} (V : VData D)

def LGUnr3 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K],
    Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ π : (V.spec K 3).Rep, V.IsRACSDC K 3 π →
    ∀ ρ : K.fixingSubgroup →* GL (Fin 3) (QbarL l), Continuous ρ → V.IsRi π (VData.toRecRep ρ) →
    ∀ M : ℕ, (V.spec K 3).level π M → ∀ v : HeightOneSpectrum (𝓞 K), ((M : ℕ) : 𝓞 K) ∉ v.asIdeal →
    ((l : ℕ) : 𝓞 K) ∉ v.asIdeal → ∀ (A : ValuationSubring QbarQ) (σ : K.fixingSubgroup),
    Formalism.ConjugateSelfDual.IsPlaceOver (F := K) A v →
    Formalism.ConjugateSelfDual.IsFrob (F := K) A (Formalism.ConjugateSelfDual.normV v) (IntermediateField.fixingSubgroupEquiv K σ) →
    ((ρ σ⁻¹ : GL (Fin 3) (QbarL l)) : Matrix (Fin 3) (Fin 3) (QbarL l)).charpoly.map (V.iotaC l).toRingHom =
      (V.spec K 3).hecke π v

def LGUnr2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (π : (V.spec ℚ 2).Rep) (W : GQ →* GL (Fin 2) (QbarL l)), Continuous W →
    Formalism.ConjugateSelfDual.Irred W → V.IsRi π W → ∀ M : ℕ, (V.spec ℚ 2).level π M → ∀ v : HeightOneSpectrum (𝓞 ℚ),
    ((M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal → ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal → Formalism.ConjugateSelfDual.UnramAt W v ∧
    ∀ (A : ValuationSubring QbarQ) (σ : GQ),
    Formalism.ConjugateSelfDual.IsPlaceOver (F := ℚ) A v → Formalism.ConjugateSelfDual.IsFrob (F := ℚ) A (Formalism.ConjugateSelfDual.normV v) σ →
    ((W σ⁻¹ : GL (Fin 2) (QbarL l)) : Matrix (Fin 2) (Fin 2) (QbarL l)).charpoly.map (V.iotaC l).toRingHom =
      (V.spec ℚ 2).hecke π v

def LocGlobWt2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (π : (V.spec ℚ 2).Rep) (W : GQ →* GL (Fin 2) (QbarL l)), Continuous W → ∀ e : ℕ,
    V.IsRi π (twistRep W ((epsL l) ^ e)⁻¹) →
    (∀ τ, V.HT l 2 ⊤ (V.plc l) (onTop W) τ = ({-(e : ℤ), (e : ℤ)} : Multiset ℤ)) →
    (V.spec ℚ 2).wt π = fun _ => ![2 * (e : ℤ), 0]

def RhoDet3 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] (π : (V.spec K 3).Rep)
    (ρ ρ' : K.fixingSubgroup →* GL (Fin 3) (QbarL l)), Continuous ρ → Continuous ρ' →
    Formalism.ConjugateSelfDual.Irred (VData.toRecRep ρ) → Formalism.ConjugateSelfDual.Irred (VData.toRecRep ρ') →
    V.IsRi π (VData.toRecRep ρ) → V.IsRi π (VData.toRecRep ρ') → IsIsoRep ρ ρ'

def RhoDet2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (π : (V.spec ℚ 2).Rep) (W W' : GQ →* GL (Fin 2) (QbarL l)), Continuous W →
    Continuous W' → Formalism.ConjugateSelfDual.Irred W → Formalism.ConjugateSelfDual.Irred W' → V.IsRi π W → V.IsRi π W' → IsIsoRep W W'

def HeckeInt3 : Prop :=
  ∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
    ∀ (M e : ℕ), 1 ≤ e → ∀ π ∈ Formalism.MainNotions.UnitaryThreeHeightBounds.Sig3 V K M e, ∀ v : HeightOneSpectrum (𝓞 K),
    ((M : ℕ) : 𝓞 K) ∉ v.asIdeal → ∀ z ∈ ((V.spec K 3).hecke π v).roots,
    IsIntegral ℤ ((Formalism.ConjugateSelfDual.normV v : ℂ) ^ (e - 1) * z)

def HeckeInt2 : Prop :=
  ∀ (M e : ℕ), ∀ π ∈ Sig2 V M e, ∀ v : HeightOneSpectrum (𝓞 ℚ), ((M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal →
    ∀ z ∈ ((V.spec ℚ 2).hecke π v).roots, IsIntegral ℤ z

def LocGlob2G : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (π : (V.spec ℚ 2).Rep) (ι : QbarL l ≃+* ℂ) (W : GQ →* GL (Fin 2) (QbarL l)),
    Continuous W → ∀ j : ℤ, IsRiAt V ι π (twistRep W ((epsL l) ^ j)) → ∀ M : ℕ, 0 < M → Ram2 V l W M →
    (V.spec ℚ 2).level π M

def CAut (F : Type) [Field F] [NumberField F] (n : ℕ) : Prop :=
  ∀ (π : (V.spec F n).Rep) (σ : ℂ ≃+* ℂ), ∃ π' : (V.spec F n).Rep,
    (∀ M : ℕ, (V.spec F n).level π M → ∀ v : HeightOneSpectrum (𝓞 F), ((M : ℕ) : 𝓞 F) ∉ v.asIdeal →
      (V.spec F n).hecke π' v = ((V.spec F n).hecke π v).map σ.toRingHom) ∧
    (∀ τ : F →+* ℂ, (V.spec F n).wt π' (σ.toRingHom.comp τ) = (V.spec F n).wt π τ) ∧
    (V.IsRACSDC F n π → V.IsRACSDC F n π')

def ClozelAutR : Prop :=
  (∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
    CAut V K 3) ∧ CAut V ℚ 2

structure Inp : Prop where
  lg3Pt : LG.LocGlob3Pt V
  lg2G : LocGlob2G V
  clozelR : ClozelAutR V
  lgUnr3 : LGUnr3 V
  lgUnr2 : LGUnr2 V
  wt2 : LocGlobWt2 V
  det3 : RhoDet3 V
  det2 : RhoDet2 V
  int3 : HeckeInt3 V
  int2 : HeckeInt2 V
  deJong : Formalism.MainNotions.UnitaryThreeHeightBounds.DeJong D V

def LitGeo : Prop :=
  Formalism.MainNotions.UnitaryThreeHeightBounds.lit0 D V ∧ Formalism.MainNotions.UnitaryThreeHeightBounds.lit1 D V ∧ Formalism.MainNotions.UnitaryThreeHeightBounds.lit2 D V ∧ Formalism.MainNotions.UnitaryThreeHeightBounds.lit3 D V ∧ Formalism.MainNotions.UnitaryThreeHeightBounds.lit4 D V ∧
    Formalism.MainNotions.UnitaryThreeHeightBounds.lit5 D V ∧ LG.lit6Pt D V ∧ Formalism.MainNotions.UnitaryThreeHeightBounds.lit9 D V ∧ Formalism.MainNotions.UnitaryThreeHeightBounds.LitB D V

def Adm0 : Prop :=
  Formalism.MainNotions.UnitaryThreeHeightBounds.adm1 D V ∧ Formalism.MainNotions.UnitaryThreeHeightBounds.adm2 D V ∧ Formalism.MainNotions.UnitaryThreeHeightBounds.adm3 D V ∧ Formalism.MainNotions.UnitaryThreeHeightBounds.ArchimedeanSignatureMatching D V ∧ UnitaryThreeAutomorphy V ∧
    Formalism.MainNotions.UnitaryThreeHeightBounds.adm6 D V ∧ Formalism.MainNotions.UnitaryThreeHeightBounds.adm8 D V

def Giv : Prop := LitGeo V ∧ Adm0 V ∧ Inp V

structure Dat (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ)
    [FiniteDimensional ℚ K] (g1 : GQ) : Prop where
  data : UnitaryThreeData V l e χ K
  norm : IsNormElt V l e χ K g1
  a : UnitaryThreeFiniteness V l e χ K g1
  b : UnitaryThreeIrreduciblePoints V l e χ K g1

abbrev LW (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) (g1 : GQ) : Prop :=
  LemmaWAt V l e χ K g1

def StepOl : Prop := ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → Formalism.MainNotions.GradedPowerSeriesLemmas.IsOl (V.Ol l) l

def StepVal : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], ∃ s : Formalism.MainNotions.GradedPowerSeriesLemmas.Ebar (V.Ol l) ≃+* QbarL l,
    (∀ x : V.Ol l, s (algebraMap (V.Ol l) (Formalism.MainNotions.GradedPowerSeriesLemmas.Ebar (V.Ol l)) x) = V.jO l x) ∧
    ∀ x : Formalism.MainNotions.GradedPowerSeriesLemmas.Ebar (V.Ol l), x ≠ 0 → ‖s x‖ ≤ 1 → ((Formalism.MainNotions.GradedPowerSeriesLemmas.vE x : ℚ) : ℝ) = vL l (s x)

def StepNormInt : Prop := ∀ (l : ℕ) [Fact l.Prime] (z : QbarL l), IsIntegral ℤ z → ‖z‖ ≤ 1

def StepNormZ : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (n : ℤ), n ≠ 0 → ‖((n : ℤ) : QbarL l)‖ = (l : ℝ) ^ (-(padicValInt l n : ℤ))

open Formalism.MainNotions.GradedPowerSeriesLemmas in

def StepA : Prop :=
  Giv V → ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∃ P : Pres V l e χ K g1,
      DataM P.𝔓 P.F P.G P.E1 P.E2 P.Z ∧ M1 P.𝔓 P.F P.G P.Z P.r' P.s' l ∧ V.Vlen l e χ ≤ VPrime P.𝔓 P.F

open Formalism.MainNotions.GradedPowerSeriesLemmas in

def ThirdModuleCondition : Prop :=
  Giv V → ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∀ P : Pres V l e χ K g1, DataM P.𝔓 P.F P.G P.E1 P.E2 P.Z →
      M3 P.𝔓 P.F P.G P.E1 P.E2 P.Z

open Formalism.MainNotions.GradedPowerSeriesLemmas in

def FourthModuleCondition : Prop :=
  Giv V → ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → LW V l e χ K g1 → ∀ P : Pres V l e χ K g1, DataM P.𝔓 P.F P.G P.E1 P.E2 P.Z →
      M4 P.𝔓 P.F P.G P.E1 P.E2 P.Z

def StepLabel : Prop :=
  Giv V → ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → LW V l e χ K g1 → ∀ p : ℕ, p.Prime → ¬ p ∣ 30 * l * condV D * dK K → ∀ Fr : FrobAt K p,
    ∃ lab : {ξ : V.S3 l e χ K g1 →+* QbarL l // V.IsPt3 ξ ∧ Both3 ξ} → Lab V K e,
      (∀ ξ, V.iotaC l ((V.rho3 ξ.1 Fr.φ : GL (Fin 3) (QbarL l)) : Matrix (Fin 3) (Fin 3) (QbarL l)).trace =
        tt V e Fr (lab ξ)) ∧
      ∀ ξ ξ', lab ξ = lab ξ' → SameOrbit3 ξ.1 ξ'.1

def StepEis : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (p : ℕ), p.Prime → p ≠ l → ∀ Fr : FrobAt K p,
    V.iotaC l (V.jO l (V.psi l e χ (Fr.φ : GQ))) = ((Fr.q : ℂ) ^ e)⁻¹ * zetaP V χ Fr ∧
    V.iotaC l (V.jO l (V.psi l e χ ((Fr.φ : GQ)⁻¹))) = (Fr.q : ℂ) ^ e * (zetaP V χ Fr)⁻¹

def StepFacInt : Prop :=
  Inp V → ∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
    ∀ (e : ℕ), 1 ≤ e → ∀ (χ : Chi D) (p : ℕ), p.Prime → ¬ p ∣ 30 * condV D * dK K → ∀ (Fr : FrobAt K p)
    (τ : Lab V K e), IsIntegral ℤ (fac V e χ Fr τ)

def StepFacBd : Prop :=
  Formalism.MainNotions.UnitaryThreeHeightBounds.Purity V → ∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K], Module.finrank ℚ K = 2 →
    IsTotallyComplex K → ∀ (e : ℕ), 1 ≤ e → ∀ (χ : Chi D) (p : ℕ), p.Prime → ¬ p ∣ 30 * condV D * dK K →
    ∀ (Fr : FrobAt K p) (τ : Lab V K e),
      0 < ‖fac V e χ Fr τ‖ ∧ ‖fac V e χ Fr τ‖ ≤ (Fr.q : ℝ) ^ e * ((Fr.q : ℝ) ^ e + 5)

def StepNNfix : Prop :=
  ClozelAutR V → LG.LocGlob3Pt V → LocGlob2G V → ∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K], Module.finrank ℚ K = 2 →
    IsTotallyComplex K → ∀ (e : ℕ), 1 ≤ e → ∀ (χ : Chi D) (p : ℕ), p.Prime → ¬ p ∣ 30 * condV D * dK K →
    ∀ (Fr : FrobAt K p) (σ : ℂ ≃+* ℂ), σ (NNc V e χ Fr) = NNc V e χ Fr

def StepAutC : Prop := ∀ z : ℂ, IsIntegral ℤ z → (∀ σ : ℂ ≃+* ℂ, σ z = z) → ∃ n : ℤ, z = n

def Sig3CountE (C : ℝ) (B : ℕ) : Prop :=
  ∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
    ∀ M e : ℕ, 0 < M → 1 ≤ e → (Formalism.MainNotions.UnitaryThreeHeightBounds.Sig3 V K M e).Finite ∧
      ((Formalism.MainNotions.UnitaryThreeHeightBounds.Sig3 V K M e).ncard : ℝ) ≤ C * (|(NumberField.discr K : ℝ)| * (M : ℝ) * (e : ℝ)) ^ B

def Sig2CountE (C : ℝ) (B : ℕ) : Prop :=
  ∀ (M k : ℕ), 0 < M → ∀ w : (ℚ →+* ℂ) → Fin 2 → ℤ, (∀ τ, w τ 0 - w τ 1 = (k : ℤ) - 1) →
    ({π | (V.spec ℚ 2).level π M ∧ (V.spec ℚ 2).wt π = w} : Set (V.spec ℚ 2).Rep).Finite ∧
    (({π | (V.spec ℚ 2).level π M ∧ (V.spec ℚ 2).wt π = w} : Set (V.spec ℚ 2).Rep).ncard : ℝ) ≤
      C * ((M : ℝ) * (k : ℝ)) ^ B

def CountBd (c : ℝ) (a b g : ℕ) : Prop :=
  ∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
    ∀ (e : ℕ), 1 ≤ e →
      (Fintype.card (Lab V K e) : ℝ) ≤ c * (dK K : ℝ) ^ a * (condV D : ℝ) ^ b * (e : ℝ) ^ g

open Classical in

def GaussianCaseFreeExponents (C₁ : ℝ) (bN be : ℕ) : Prop :=
  ∀ e ∈ eRange D, ∀ χ : Chi D, ∀ p : ℕ, p.Prime → ¬ p ∣ 30 * condV D →
    ∃ NN : GaussianInt, NN ≠ 0 ∧
      Real.log ‖GaussianInt.toComplex NN‖ ≤
        C₁ * (Formalism.MainNotions.UnitaryThreeHeightBounds.degQ D χ : ℝ) * (condV D : ℝ) ^ bN * (e : ℝ) ^ be * Real.log p ∧
      ∀ (l : ℕ) [Fact l.Prime], l ≠ p → ∀ K : IntermediateField ℚ QbarQ, [FiniteDimensional ℚ K] →
        UnitaryThreeData V l e χ K → UnitaryCaseGaussian V l e χ K →
        ∑ χ'' ∈ Finset.univ.filter (Formalism.MainNotions.UnitaryThreeHeightBounds.ChiConj D χ), V.Vlen l e χ'' ≤
          2 * (padicValInt l (Zsqrtd.norm NN) : ℕ∞)

def InertCaseFreeExponents (C₂ : ℝ) (bD bN be : ℕ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K],
    UnitaryThreeData V l e χ K → UnitaryCaseInert V l χ K →
    ∃ v : ℕ, V.Vlen l e χ = v ∧
      (v : ℝ) * Real.log l ≤
        C₂ * |(NumberField.discr K : ℝ)| ^ bD * (Formalism.MainNotions.UnitaryThreeHeightBounds.degQ D χ : ℝ) * (condV D : ℝ) ^ bN * (e : ℝ) ^ be *
          Real.log (Real.log ((condV D : ℝ) * l))

def c4 (β cP cD : ℝ) : ℝ := 8 * max (β * cP) 0 + 3 * max cD 0

def StepCount : Prop :=
  ∀ (X : Formalism.MainNotions.UnitaryThreeHeightBounds.SymSp) (β cP cD : ℝ) (aD : ℕ), 0 ≤ β → aD ≤ 18 → Formalism.MainNotions.UnitaryThreeHeightBounds.ClozelCoh V X →
    Formalism.MainNotions.UnitaryThreeHeightBounds.lit8E D V X β cP cD aD →
    ∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
    ∀ (e : ℕ), 1 ≤ e →
      (Fintype.card (Lab V K e) : ℝ) ≤ c4 β cP cD * (dK K : ℝ) ^ (max 5 aD) * (condV D : ℝ) ^ 18 * (e : ℝ) ^ 6

open Classical in

def StepOrbCard (D : D7) : Prop :=
  ∀ χ : Chi D, (Finset.univ.filter (Formalism.MainNotions.UnitaryThreeHeightBounds.ChiConj D χ)).card ≤ Formalism.MainNotions.UnitaryThreeHeightBounds.degQ D χ

def StepFrob : Prop :=
  ∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K], Module.finrank ℚ K = 2 → ∀ p : ℕ, p.Prime →
    Nonempty (FrobAt K p)

def StepQi : Prop :=
  ∃ (Ki : IntermediateField ℚ QbarQ) (_ : FiniteDimensional ℚ Ki), Module.finrank ℚ Ki = 2 ∧ IsTotallyComplex Ki ∧
    dK Ki = 4 ∧ ∀ K : IntermediateField ℚ QbarQ, IsQi K → K = Ki

def StepLeastPrime (c : ℝ) : Prop :=
  ∀ m : ℕ, 2 ≤ m → ∃ p : ℕ, p.Prime ∧ ¬ p ∣ m ∧ (p : ℝ) ≤ c * Real.log m

def LengthBoundAtFrobenius : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K],
    UnitaryThreeData V l e χ K → ∀ p : ℕ, p.Prime → ¬ p ∣ 30 * l * condV D * dK K → ∀ Fr : FrobAt K p,
    ∃ v : ℕ, V.Vlen l e χ = v ∧ (v : ℝ) ≤ 2 * vL l ((V.iotaC l).symm (prodChi V e χ Fr))

def NNProps (c5 : ℝ) (a b g : ℕ) : Prop :=
  ∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
    ∀ (e : ℕ), 1 ≤ e → ∀ (χ : Chi D) (p : ℕ), p.Prime → ¬ p ∣ 30 * condV D * dK K → ∀ Fr : FrobAt K p,
    ∃ n : ℤ, n ≠ 0 ∧ NNc V e χ Fr = n ∧
      Real.log |(n : ℝ)| ≤ c5 * (Formalism.MainNotions.UnitaryThreeHeightBounds.degQ D χ : ℝ) * (dK K : ℝ) ^ a * (condV D : ℝ) ^ b * (e : ℝ) ^ (g + 1) *
        Real.log p

def ProdInt : Prop :=
  ∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
    ∀ (e : ℕ), 1 ≤ e → ∀ (χ : Chi D) (p : ℕ), p.Prime → ¬ p ∣ 30 * condV D * dK K → ∀ Fr : FrobAt K p,
    IsIntegral ℤ (prodChi V e χ Fr) ∧ prodChi V e χ Fr ≠ 0

end Formalism.MainNotions.V.Pf.V3
