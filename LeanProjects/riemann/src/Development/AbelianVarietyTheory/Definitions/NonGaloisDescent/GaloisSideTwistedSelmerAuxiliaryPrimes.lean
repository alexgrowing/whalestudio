import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTameInertiaElementAtTwistPrime

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen
open scoped ENNReal TensorProduct

namespace GlobalTheory.TwSys

def Cheb : Prop := ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  (U : Subgroup (G F Ω)), IsOpen (U : Set (G F Ω)) → U.Normal → ∀ (g : G F Ω) (A : Finset (HeightOneSpectrum (𝓞 F))),
  ∃ v, v ∉ A ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧ v.asIdeal.ramificationIdx ℤ = 1 ∧
    ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ Ine (F := F) B ≤ U ∧ ∃ σ : G F Ω, IsFrob B (normV v) σ ∧ σ * g⁻¹ ∈ U

def OrdHyp (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l M R nmax v : ℕ)
    (f : MvPolynomial (Fin R ⊕ Fin R) O) : Prop :=
  ∃ Dd g : MvPolynomial (Fin R ⊕ Fin R) O,
    f - Dd * g ∈ Ideal.span (Set.range (fun i : Fin R => (MvPolynomial.X (Sum.inr i) : MvPolynomial (Fin R ⊕ Fin R) O)) ∪
      Set.range (fun i : Fin R => (1 + MvPolynomial.X (Sum.inl i)) ^ (l ^ M) - 1)) ∧
    IsDiscreteValuationRing.addVal O (g.coeff 0) ≤ v ∧
    ∃ (u : MvPolynomial (Fin R ⊕ Fin R) (IsLocalRing.ResidueField O)) (n : Fin R → ℕ), u.coeff 0 ≠ 0 ∧ (∀ i, n i ≤ nmax) ∧
      Dd.map (IsLocalRing.residue O) - u * ∏ i, MvPolynomial.X (Sum.inl i) ^ n i ∈
        Ideal.span (Set.range fun q =>
          (MvPolynomial.X q : MvPolynomial (Fin R ⊕ Fin R) (IsLocalRing.ResidueField O)) ^ (l ^ M))

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

def K1 : Prop := ∀ (i : X.Tw) (M : ℕ), 1 ≤ M → ∃ H S d, AdmFam X i M H S d

def PropE (N0 : X.Tw → ℕ) : Prop :=
  ∀ (i : X.Tw) (lam : X.abelian₂ i) (z : GE N), X.NonzeroIndexPlace i → (∃ s, SOk X i lam s) → (∑ δ, X.th i ∅ lam δ) ≠ 0 → IsTameInertiaElementAtTwistPrime X i z →
    ∃ (H : Subgroup (GE N)) (v : ℕ), IsOpen (H : Set (GE N)) ∧ H.Normal ∧
      (v : ℝ) / ((IsDiscreteValuationRing.addVal (X.O i) (X.l i : X.O i)).toNat : ℝ) = c0 X i lam + N0 i ∧
      ∀ (M R : ℕ) (P : Fin R ⊕ Fin R → PlE D.host) d (Q : Finset (PlE D.host)), 1 ≤ M →
        SlopeTestRemainingChoices X i M ∅ P d → Steps X i M H z P d → IsQ P Q →
        ∃ f : MvPolynomial (Fin R ⊕ Fin R) (X.O i), OrdHyp (X.O i) (X.l i) M R 2 v f ∧
          ∀ (k : ℕ) (u : Fin R ⊕ Fin R → (X.Ok i k)ˣ) (ψ' : X.RCG i Q →* (X.Ok i k)ˣ), (∀ q, u q ^ (X.l i ^ M) = 1) →
            (∀ g, ψ' (X.art i Q g) = ∏ q, u q ^ (Multiplicative.toAdd (d q g)).val) →
            algebraMap (X.Ok i k) (FractionRing (X.Ok i k))
                (MvPolynomial.aeval (fun q => ((u q : (X.Ok i k)ˣ) : X.Ok i k) - 1) f) =
              ((X.l i : ℕ) : FractionRing (X.Ok i k)) ^ N0 i * thEval X i Q lam k ψ'

variable {X} (bkP : BKPh X)

def ThmS : Prop :=
  ∀ (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (M : ℕ) (ι : Type) [Fintype ι] (P : ι → PlE D.host) d
    (Q : Finset (PlE D.host)), 1 ≤ M → SlopeTestRemainingChoices X i M ∅ P d → IsQ P Q →
    ∃ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)), Computes bkP i s M d Q Φ ∧ ∀ b c, ¬ IsUnit (Φ b c)

def SelmerLengthsByDeterminant : Prop :=
  ∀ (i : X.Tw) (s : X.Sig i) (M : ℕ) (ι : Type) [Fintype ι] (P : ι → PlE D.host) d (Q : Finset (PlE D.host)),
    1 ≤ M → SlopeTestRemainingChoices X i M ∅ P d → IsQ P Q → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)),
    Computes bkP i s M d Q Φ → ∀ F, toLam X i M ι F = Φ.det → SelPoly bkP i s M d Q F

def OrdBound (i : X.Tw) (μ : ℕ∞) : Prop :=
  ∀ (T : Set (X.Sig i)), (∀ s ∈ T, GalHyp bkP i s) → ∃ R Dd M₀ : ℕ, ∀ M, M₀ ≤ M →
    ∀ H S d, AdmFam X i M H S d → ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ (H' : Subgroup (GE N)), IsOpen (H' : Set (GE N)) → H'.Normal →
    ∀ A : Finset (PlE D.host), ∃ P : Fin R ⊕ Fin R → PlE D.host,
      SlopeTestRemainingChoices X i M A P (fun q => d (P q)) ∧ Steps X i M H' z P (fun q => d (P q)) ∧
      ∀ s ∈ T, ∀ Q, IsQ P Q → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M (Fin R ⊕ Fin R))),
        Computes bkP i s M (fun q => d (P q)) Q Φ → ∀ F, toLam X i M (Fin R ⊕ Fin R) F = Φ.det →
        ∃ m : Fin R ⊕ Fin R →₀ ℕ, m.degree ≤ Dd ∧ IsDiscreteValuationRing.addVal (X.O0 i) (F.coeff m) ≤ μ

def ResidualBoundOddPrimes : Prop := ∀ i : X.Tw, nu X i = 0 → OrdBound bkP i 0

def ThmC : Prop :=
  ∀ i : X.Tw, 0 < nu X i → OrdBound bkP i (IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i))

def GaloisSideTwistedSelmerAuxiliaryPrimes : Prop :=
  ∀ (i : X.Tw) (T : Set (X.Sig i)), (∀ s ∈ T, GalHyp bkP i s) → ∃ R Dd M₀ : ℕ, 1 ≤ M₀ ∧ ∀ M, M₀ ≤ M →
    ∀ H S d, AdmFam X i M H S d → ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ (H' : Subgroup (GE N)), IsOpen (H' : Set (GE N)) → H'.Normal →
    ∀ A : Finset (PlE D.host), ∃ P : Fin R ⊕ Fin R → PlE D.host,
      SlopeTestRemainingChoices X i M A P (fun q => d (P q)) ∧ Steps X i M H' z P (fun q => d (P q)) ∧
      ∀ s ∈ T, ∀ Q, IsQ P Q → ∃ F, SelPoly bkP i s M (fun q => d (P q)) Q F ∧
        ∃ m : Fin R ⊕ Fin R →₀ ℕ, m.degree ≤ Dd ∧ IsDiscreteValuationRing.addVal (X.O0 i) (F.coeff m) ≤
          IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i)

variable (Y : NExp D.R D.host D.what₂ D.LL0 N X)

def ConjCl (Q : Finset (PlE D.host)) : Prop := ∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q

def IsCoord (i : X.Tw) (M : ℕ) (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) : Prop :=
  ∀ Q, ConjCl (D := D) Q → ∀ (P : PlE D.host) (hP : P ∈ Q) (σ : GE N),
    Multiplicative.toAdd (Y.delU i Q M σ) ⟨P, hP⟩ = Multiplicative.toAdd (d P σ)

def DelUTie : Prop := ∀ (i : X.Tw) (M : ℕ), X.NonzeroIndexPlace i → 1 ≤ M → ∃ H S d, AdmFam X i M H S d ∧ IsCoord Y i M d

def HeckeLaws : Prop :=
  ∀ i : X.Tw, X.NonzeroIndexPlace i → (∀ j b k P k' P', Formalism.MainNotions.IntegralHeckeForms.HkIdx i k P → Formalism.MainNotions.IntegralHeckeForms.HkIdx i k' P' →
      Y.hkF i j b k P * Y.hkF i j b k' P' = Y.hkF i j b k' P' * Y.hkF i j b k P) ∧
    ∀ s P, X.hEig i s 0 P = 1

def PqF (i : X.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) (y : X.Ok i k) :
    Module.End (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b) :=
  1 + ∑ n ∈ Finset.Icc 1 D.R.r, ((-1 : X.Ok i k) ^ n * ((normV P : ℕ) : X.Ok i k) ^ (n * (n - 1) / 2) * y ^ n) •
    (Formalism.MainNotions.IntegralHeckeForms.hkO Y i j b n P).baseChange (X.Ok i k)

open Classical in

def ThURel : Prop :=
  ∀ i : X.Tw, X.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
    ∃ (ch : Set (PlE D.host)) (sg : Bool), (∀ P P', IsConjPl D.host P P' → P ≠ P' → (P ∈ ch ↔ P' ∉ ch)) ∧
      (∀ M k χ (a : Y.Dat i j b), Formalism.MainNotions.IntegralHeckeForms.specU Y i j b ∅ M k χ (Y.thU i j b ∅ M a) =
        (1 : X.Ok i k) ⊗ₜ[X.O i] Y.th i j b a) ∧
      ∀ (M : ℕ) d (Q : Finset (PlE D.host)) (a : Y.Dat i j b), IsCoord Y i M d → QOk X i Q →
        Formalism.MainNotions.IntegralHeckeForms.ClsQ (D := D) Q → Disjoint Q (Y.lev i j b a) →
        (∀ P ∈ Q, GoodChar X i M P (d P) ∧ normV P % (2 * X.l i ^ M) = 1) →
        ∀ (P Pb : PlE D.host), P ∈ Q → Pb ∈ Q → P ≠ Pb → IsConjPl D.host P Pb → P ∈ ch →
        ∀ (k : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
          (χ' : Multiplicative (DelQM D.host (X.l i) ((Q.erase P).erase Pb) M) →* (X.Ok i k)ˣ),
          (∀ x : DelQM D.host (X.l i) Q M, χ (Multiplicative.ofAdd x) = χ' (Multiplicative.ofAdd fun v =>
            x ⟨v.1, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase v.2)⟩)) →
          ∀ σ : GE N, IsFrob (N.plOm.1 P) (normV P) σ →
            Formalism.MainNotions.IntegralHeckeForms.specU Y i j b Q M k χ (Y.thU i j b Q M a) =
              PqF Y i j b k P ((psiAt sg χ' (Y.delU i ((Q.erase P).erase Pb) M σ) : (X.Ok i k)ˣ) : X.Ok i k)
                (Formalism.MainNotions.IntegralHeckeForms.specU Y i j b ((Q.erase P).erase Pb) M k χ' (Y.thU i j b ((Q.erase P).erase Pb) M a))

def PropABCD : Prop :=
  ∀ (i : X.Tw) (F : Formalism.MainNotions.IntegralHeckeForms.RFam Y i) (j : ℕ) (b : Bool) (z : GE N), X.NonzeroIndexPlace i → j ∈ Finset.Icc 1 D.R.m →
    Formalism.MainNotions.IntegralHeckeForms.ABHyp Y i F j b → IsTameInertiaElementAtTwistPrime X i z →
    ∃ (H : Subgroup (GE N)) (A : Finset (PlE D.host)) (v nmax : ℕ), IsOpen (H : Set (GE N)) ∧ H.Normal ∧
      ∀ (M R : ℕ) (P : Fin R ⊕ Fin R → PlE D.host) d (Q : Finset (PlE D.host)), 1 ≤ M → IsCoord Y i M d →
        SlopeTestRemainingChoices X i M A P (fun q => d (P q)) → Steps X i M H z P (fun q => d (P q)) → (hQ : IsQ P Q) →
        ∃ f : MvPolynomial (Fin R ⊕ Fin R) (X.O i), OrdHyp (X.O i) (X.l i) M R nmax v f ∧
          ∀ (k : ℕ) (u : Fin R ⊕ Fin R → (X.Ok i k)ˣ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
            (∀ q, u q ^ (X.l i ^ M) = 1) →
            (∀ x : DelQM D.host (X.l i) Q M, χ (Multiplicative.ofAdd x) =
              ∏ q, u q ^ (x ⟨P q, (hQ _).2 ⟨q, Or.inl rfl⟩⟩).val) →
            MvPolynomial.aeval (fun q => ((u q : (X.Ok i k)ˣ) : X.Ok i k) - 1) f ≠ 0 →
            ∀ Tψ : Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b),
              Formalism.MainNotions.IntegralHeckeForms.IsLatIn Tψ (((Submodule.span (FractionRing (X.O i)) (F.B j b : Set (Y.Fm i j b))).restrictScalars
                (X.O i)).baseChange (X.Ok i k)) →
              (∀ a ∈ F.S j b, ((F.A j b).baseChange (X.Ok i k))
                (Formalism.MainNotions.IntegralHeckeForms.specU Y i j b Q M k χ (Y.thU i j b Q M a)) ∈ Tψ) →
              Formalism.MainNotions.IntegralHeckeForms.sIdx (X.l i) ((F.B j b).baseChange (X.Ok i k)) Tψ ≤
                Formalism.MainNotions.IntegralHeckeForms.sIdx (X.l i) (F.B j b) (F.Th j b) +
                  (nval (X.Ok i k) (X.l i) (MvPolynomial.aeval (fun q => ((u q : (X.Ok i k)ˣ) : X.Ok i k) - 1) f) -
                    (v : ℝ) / ((IsDiscreteValuationRing.addVal (X.O i) (X.l i : X.O i)).toNat : ℝ))

def AllGood : Prop := ∀ i : X.Tw, X.NonzeroIndexPlace i → ∀ s : X.Sig i, goodE Y i s

end GlobalTheory.TwSys

end
