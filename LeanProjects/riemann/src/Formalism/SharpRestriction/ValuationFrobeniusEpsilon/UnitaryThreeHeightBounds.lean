import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.InstLocalRingSymplecticCoefficients
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.UnitaryThreeIrreduciblePoints
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.GradedCompletionLemmas
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.GradedPowerSeriesLemmas

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TV

namespace Formalism.MainNotions.UnitaryThreeHeightBounds

variable (D : D7) (V : VData D)

export Formalism.MainNotions.V (ChiConj degQ ChiConj.refl ChiConj.symm)

def ix (P : V1.LiftProb) (h : P.kind = .typeThree) : Fin 3 → Fin P.kind.n :=
  Fin.cast (congrArg V1.GGKind.n h).symm

def posTab : Fin 8 → Fin 3 × Fin 3 := ![(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2), (0, 1), (1, 0)]

variable {D}

def InRamificationSet (l : ℕ) (K : IntermediateField ℚ QbarQ) (q : ℕ) : Prop :=
  q = l ∨ q ∣ condV D ∨ ¬ V.Iq q ≤ K.fixingSubgroup

structure UnitaryThreeLiftingProblem (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ)
    (g1 : GQ) where

  P : V1.LiftProb
  hl : P.l = l

  eO : P.O ≃+* V.Ol l

  pr : GQ →* P.Gam
  pr_cont : Continuous pr
  pr_surj : Function.Surjective pr
  pr_ker : pr.ker = (Subgroup.closure {σ : GQ | ∃ (A : ValuationSubring QbarQ) (q : ℕ), q.Prime ∧
    Formalism.MainNotions.V.Lang.IsPlaceAbove ℚ A q ∧ ¬ InRamificationSet V l K q ∧ σ ∈ Formalism.MainNotions.V.Lang.Ine (F := ℚ) A}).topologicalClosure

  pr_inj : ∀ q : ℕ, q.Prime → InRamificationSet V l K q → ∀ g ∈ V.Dq q, pr g = 1 → g = 1

  hk : P.kind = .typeThree
  GF_eq : P.GF = K.fixingSubgroup.map pr
  cc_eq : P.cc = pr V.cc

  lPl_card : Fintype.card P.lPl = 1
  Gv_eq : ∀ v, P.Gv v = (V.Dq l).map pr

  qe : P.qPl ≃ {q : ℕ // q.Prime ∧ q ≠ l ∧ InRamificationSet V l K q}
  Gq_eq : ∀ q, P.Gq q = (V.Dq (qe q)).map pr
  Iq_eq : ∀ q, P.Iq q = (V.Iq (qe q)).map pr
  degF_eq : P.degF = 1
  cv_eq : ∀ v, P.cv v = pr V.cc

  chi_eq : P.chi = 1
  cyc_eq : ∀ g : GQ, ((P.cyc (pr g) : (IsLocalRing.ResidueField P.O)ˣ) : IsLocalRing.ResidueField P.O) =
    IsLocalRing.residue P.O (eO.symm (V.zO l (eps l g : ℤ_[l])))

  hrk : P.rk = 1
  dg_eq : ∀ (i : Fin 3) s, P.dg (ix P hk i) s = 1 - (i : ℤ)

  rbar_K : ∀ g ∈ K.fixingSubgroup, ∀ i j : Fin 3, P.rbar (pr g) (ix P hk i) (ix P hk j) =
    IsLocalRing.residue P.O (eO.symm (Matrix.diagonal ![V.psi l e χ g, 1, V.psi l e χ g⁻¹] i j))
  rbar_c : ∀ i j : Fin 3, P.rbar (pr V.cc) (ix P hk i) (ix P hk j) = Jad3 _ i j

  ne : Fin 8 ≃ Fin P.nN
  nx_C : ∀ k : Fin 8, (k : ℕ) < 6 → P.nx (ne k) = Finsupp.single (pr V.cc) 1
  lift_problem_vanishing : ∀ k : Fin 8, 6 ≤ (k : ℕ) →
    P.nx (ne k) = Finsupp.single (pr g1) 1 - Finsupp.single (pr (V.cc * g1⁻¹ * V.cc)) 1
  npos_eq : ∀ k : Fin 8, P.npos (ne k) = (ix P hk (posTab k).1, ix P hk (posTab k).2)
  ncst_eq : ∀ k : Fin 8, P.ncst (ne k) = if (k : ℕ) < 6 then Jad3 P.O (posTab k).1 (posTab k).2 else 0

  Q : Formalism.MainNotions.UnusedSlot38.AQuot P
  eS : Q.Ahat.C ≃+* V.S3hat l e χ K g1
  eS_O : ∀ x : P.O, eS (algebraMap P.O Q.Ahat.C x) = algebraMap (V.Ol l) (V.S3hat l e χ K g1) (eO x)
  eS_r : ∀ (g : K.fixingSubgroup) (i j : Fin 3), eS (Q.q (P.uBox (pr g) (ix P hk i) (ix P hk j))) =
    ((V.rS3hat l e χ K g1 g : GL (Fin 3) (V.S3hat l e χ K g1)) :
      Matrix (Fin 3) (Fin 3) (V.S3hat l e χ K g1)) i j

variable (D)

def ForallUnitaryThreeLiftingProblems (φ : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) (g1 : GQ),
    UnitaryThreeLiftingProblem V l e χ K g1 → Prop) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K],
    Formalism.MainNotions.V.UnitaryThreeData V l e χ K → ∀ g1 : GQ, Formalism.MainNotions.V.IsNormElt V l e χ K g1 →
    ∀ T : UnitaryThreeLiftingProblem V l e χ K g1, φ l e χ K g1 T

def adm1 : Prop := ForallUnitaryThreeLiftingProblems D V fun _ _ _ _ _ _ T => Formalism.MainNotions.UnusedSlot38.liftZP_unit T.P

def adm2 : Prop := Formalism.MainNotions.UnusedSlot38.FiniteTypeRingPart ∧ ForallUnitaryThreeLiftingProblems D V fun _ _ _ _ _ _ T => Formalism.MainNotions.UnusedSlot38.UniversalLiftFiniteType T.P

def adm3 : Prop := Formalism.MainNotions.UnusedSlot38.PointsLemma D V

def ArchimedeanSignatureMatching : Prop := ForallUnitaryThreeLiftingProblems D V fun _ _ _ _ _ _ T => Formalism.MainNotions.UnusedSlot38.LitG T.P → Formalism.MainNotions.UnusedSlot38.RelativePresentation T.P

def adm5 : Prop := Formalism.MainNotions.V.UnitaryThreeAutomorphyWeights V

def adm6 : Prop := Formalism.MainNotions.V.LemmaK V

def adm8 : Prop := Formalism.MainNotions.GradedPowerSeriesLemmas.Conclusion2 D V

def admitted : Prop :=
  adm1 D V ∧ adm2 D V ∧ adm3 D V ∧ ArchimedeanSignatureMatching D V ∧ adm5 D V ∧ adm6 D V ∧ adm8 D V

theorem first_hypothesis_of_lifting (h : Formalism.MainNotions.UnusedSlot38.Conclusion1 D V) : adm1 D V := fun _ _ _ _ _ _ _ _ _ T => h T.P
theorem second_hypothesis_of_lifting (h : Formalism.MainNotions.UnusedSlot38.Conclusion2 D V) : adm2 D V := ⟨h.1, fun _ _ _ _ _ _ _ _ _ T => h.2 T.P⟩
theorem integrality_of_commutation (h : Formalism.MainNotions.UnusedSlot38.PointsLemma D V) : adm3 D V := h
theorem fourth_hypothesis_of_lifting (h : Formalism.MainNotions.UnusedSlot38.Conclusion5 D V) : ArchimedeanSignatureMatching D V :=
  fun _ _ _ _ _ _ _ _ _ T hL => (Formalism.MainNotions.UnusedSlot38.lifting_lemma_of_literature h T.P hL).1
theorem lemma_M_prime_hypothesis (h : Formalism.MainNotions.GradedPowerSeriesLemmas.Conclusion2 D V) : adm8 D V := h

def Conclusion1 : Prop := Formalism.MainNotions.GradedPowerSeriesLemmas.Conclusion1 D V

open Classical in

def GaussianCaseHeightBound (C₁ : ℝ) : Prop :=
  ∀ e ∈ eRange D, ∀ χ : Chi D, ∀ p : ℕ, p.Prime → ¬ p ∣ 30 * condV D →
    ∃ NN : GaussianInt, NN ≠ 0 ∧
      Real.log ‖GaussianInt.toComplex NN‖ ≤
        C₁ * (degQ D χ : ℝ) * (condV D : ℝ) ^ 18 * (e : ℝ) ^ 7 * Real.log p ∧
      ∀ (l : ℕ) [Fact l.Prime], l ≠ p → ∀ K : IntermediateField ℚ QbarQ, [FiniteDimensional ℚ K] →
        Formalism.MainNotions.V.UnitaryThreeData V l e χ K → Formalism.MainNotions.V.UnitaryCaseGaussian V l e χ K →
        ∑ χ'' ∈ Finset.univ.filter (ChiConj D χ), V.Vlen l e χ'' ≤
          2 * (padicValInt l (Zsqrtd.norm NN) : ℕ∞)

def InertBoundExponent (C₂ : ℝ) (bD : ℕ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K],
    Formalism.MainNotions.V.UnitaryThreeData V l e χ K → Formalism.MainNotions.V.UnitaryCaseInert V l χ K →
    ∃ v : ℕ, V.Vlen l e χ = v ∧
      (v : ℝ) * Real.log l ≤
        C₂ * |(NumberField.discr K : ℝ)| ^ bD * (degQ D χ : ℝ) * (condV D : ℝ) ^ 18 * (e : ℝ) ^ 7 *
          Real.log (Real.log ((condV D : ℝ) * l))

def InertCaseHeightBound (C₂ : ℝ) : Prop := InertBoundExponent D V C₂ 6

def Conclusion2 (C₁ C₂ : ℝ) : Prop := GaussianCaseHeightBound D V C₁ ∧ InertCaseHeightBound D V C₂

def Conclusion₂ (C₁ C₂ : ℝ) : Prop := Conclusion1 D V ∧ Conclusion2 D V C₁ C₂

def ConclusionE₂ (C₁ C₂ : ℝ) (bD : ℕ) : Prop := Conclusion1 D V ∧ GaussianCaseHeightBound D V C₁ ∧ InertBoundExponent D V C₂ bD

def Stmt (C₁ C₂ : ℝ) : Prop := admitted D V → Conclusion₂ D V C₁ C₂

def GaussianCaseConjugationInvariant : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ χ'' : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K],
    ChiConj D χ χ'' → Formalism.MainNotions.V.UnitaryThreeData V l e χ K → Formalism.MainNotions.V.UnitaryCaseGaussian V l e χ K →
    Formalism.MainNotions.V.UnitaryThreeData V l e χ'' K ∧ Formalism.MainNotions.V.UnitaryCaseGaussian V l e χ'' K

section Lit

open NumberField IsDedekindDomain

variable {D}

def FixMu (M : ℕ) : Subgroup GQ := (IntermediateField.adjoin ℚ {ζ : QbarQ | ζ ^ M = 1}).fixingSubgroup

def NOut (H : Subgroup GQ) (S : Finset ℕ) : Subgroup GQ :=
  Subgroup.closure {σ : GQ | σ ∈ H ∧ ∃ A : ValuationSubring QbarQ, Formalism.MainNotions.V.Lang.IsFinitePlace ℚ A ∧
    (∀ q ∈ S, ¬ Formalism.MainNotions.V.Lang.IsPlaceAbove ℚ A q) ∧ σ ∈ Formalism.MainNotions.V.Lang.Ine (F := ℚ) A}

def epsQ (l : ℕ) [Fact l.Prime] (g : GQ) : ℚ_[l] := ((eps l g : ℤ_[l]) : ℚ_[l])

def Soule : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (F : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ F]
    (S : Finset ℕ), l ∈ S → (∀ p ∈ S, p.Prime) → ∀ j : ℕ, 2 ≤ j →
    ∀ c : F.fixingSubgroup × F.fixingSubgroup → ℚ_[l], Continuous c →
      (∀ g h n m : F.fixingSubgroup, (n : GQ) ∈ NOut F.fixingSubgroup S →
        (m : GQ) ∈ NOut F.fixingSubgroup S → c (g * n, h * m) = c (g, h)) →
      (∀ g h k : F.fixingSubgroup,
        epsQ l g ^ j * c (h, k) - c (g * h, k) + c (g, h * k) - c (g, h) = 0) →
      ∃ b : F.fixingSubgroup → ℚ_[l], Continuous b ∧
        (∀ g n : F.fixingSubgroup, (n : GQ) ∈ NOut F.fixingSubgroup S → b (g * n) = b g) ∧
        ∀ g h : F.fixingSubgroup, c (g, h) = epsQ l g ^ j * b h - b (g * h) + b g

def vecM {R : Type} {n : ℕ} (X : Matrix (Fin n) (Fin n) R) : Fin (n * n) → R :=
  fun k => X (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

open Classical in

def IsGGn {l : ℕ} [Fact l.Prime] {n : ℕ} (K : IntermediateField ℚ QbarQ) (μ : GQ →* (QbarL l)ˣ)
    (r : GQ → Matrix (Fin n) (Fin n) (QbarL l)) : Prop :=
  (∀ g, IsUnit (r g).det) ∧
  ∀ g h, r (g * h) = r g * (if g ∈ K.fixingSubgroup then r h else (μ h : QbarL l) • ((r h)⁻¹).transpose)

def IsAd {l : ℕ} [Fact l.Prime] {n : ℕ} (K : IntermediateField ℚ QbarQ)
    (r : GQ → Matrix (Fin n) (Fin n) (QbarL l)) (Ad : GQ →* GL (Fin (n * n)) (QbarL l)) : Prop :=
  ∀ (g : GQ) (X : Matrix (Fin n) (Fin n) (QbarL l)),
    (Ad g : Matrix (Fin (n * n)) (Fin (n * n)) (QbarL l)).mulVec (vecM X) =
      vecM (V1.adAct K.fixingSubgroup r g X)

def IrredOn {l : ℕ} [Fact l.Prime] {n : ℕ} {H : Subgroup GQ} (H' : Subgroup GQ)
    (ρ : H →* GL (Fin n) (QbarL l)) : Prop :=
  0 < n ∧ ∀ W : Submodule (QbarL l) (Fin n → QbarL l),
    (∀ σ : H, (σ : GQ) ∈ H' → ∀ w ∈ W, (ρ σ : Matrix (Fin n) (Fin n) (QbarL l)).mulVec w ∈ W) →
    W = ⊥ ∨ W = ⊤

def Thorne : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (n : ℕ) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K],
    Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ π : (V.spec K n).Rep,
    ∀ ρ : K.fixingSubgroup →* GL (Fin n) (QbarL l), Continuous ρ →
    ∀ κ : K.fixingSubgroup →* (QbarL l)ˣ, Continuous κ →
    V.IsRi π (VData.toRecRep (Formalism.MainNotions.V.twistRep ρ κ)) →
    IrredOn (eps l).ker ρ →
    ∀ (μ : GQ →* (QbarL l)ˣ) (r : GQ → Matrix (Fin n) (Fin n) (QbarL l)), Continuous μ → IsGGn K μ r →
    (∀ g : K.fixingSubgroup, r g = (ρ g : Matrix (Fin n) (Fin n) (QbarL l))) →
    ∀ Ad : GQ →* GL (Fin (n * n)) (QbarL l), IsAd K r Ad →
      Subsingleton (V.finiteCohomology l (n * n) ⊤ (Formalism.MainNotions.V.onTop Ad))

def Thorne2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K],
    Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ π : (V.spec K 2).Rep,
    ∀ ρ : K.fixingSubgroup →* GL (Fin 2) (QbarL l), Continuous ρ →
    ∀ κ : K.fixingSubgroup →* (QbarL l)ˣ, Continuous κ →
    V.IsRi π (VData.toRecRep (Formalism.MainNotions.V.twistRep ρ κ)) →
    IrredOn (eps l).ker ρ →
    ∀ (μ : GQ →* (QbarL l)ˣ) (r : GQ → Matrix (Fin 2) (Fin 2) (QbarL l)), Continuous μ → IsGGn K μ r →
    (∀ g : K.fixingSubgroup, r g = (ρ g : Matrix (Fin 2) (Fin 2) (QbarL l))) →
    ∀ Ad : GQ →* GL (Fin (2 * 2)) (QbarL l), IsAd K r Ad →
      Subsingleton (V.finiteCohomology l (2 * 2) ⊤ (Formalism.MainNotions.V.onTop Ad))

variable {V} in
theorem Thorne.two (h : Thorne V) : Thorne2 V := fun l _ => h l 2

namespace Adj

abbrev Ine (P : ℕ → ValuationSubring QbarQ) (q : ℕ) : Subgroup GQ := Formalism.MainNotions.V.Lang.Ine (F := ℚ) (P q)

abbrev Dec (P : ℕ → ValuationSubring QbarQ) (q : ℕ) : Subgroup GQ := Formalism.MainNotions.V.Lang.Dec (F := ℚ) (P q)

def epsK (K : IntermediateField ℚ QbarQ) (l : ℕ) [Fact l.Prime] : K.fixingSubgroup →* (QbarL l)ˣ :=
  (epsL l).comp K.fixingSubgroup.subtype

def inB {l n : ℕ} [Fact l.Prime] (g : GL (Fin n) (QbarL l)) (X : Matrix (Fin n) (Fin n) (QbarL l)) :
    Matrix (Fin n) (Fin n) (QbarL l) :=
  ((g⁻¹ : GL (Fin n) (QbarL l)) : Matrix (Fin n) (Fin n) (QbarL l)) * X * (g : Matrix (Fin n) (Fin n) (QbarL l))

def SymSign {l : ℕ} [Fact l.Prime] (μ : GQ →* (QbarL l)ˣ) : Prop :=
  ∀ c : GQ, c * c = 1 → (μ c : QbarL l) = 1

def OrdFlag (P : ℕ → ValuationSubring QbarQ) (l : ℕ) {n : ℕ} [Fact l.Prime] (K : IntermediateField ℚ QbarQ)
    (ρ : K.fixingSubgroup →* GL (Fin n) (QbarL l)) (g : GL (Fin n) (QbarL l)) (h : Fin n → ℤ) : Prop :=
  StrictAnti h ∧
    (∀ σ : K.fixingSubgroup, (σ : GQ) ∈ Dec P l → (inB g (ρ σ : Matrix (Fin n) (Fin n) (QbarL l))).BlockTriangular id) ∧
    ∃ U : Subgroup GQ, IsOpen (U : Set GQ) ∧ ∀ σ : K.fixingSubgroup, (σ : GQ) ∈ Ine P l → (σ : GQ) ∈ U →
      ∀ i : Fin n, inB g (ρ σ : Matrix (Fin n) (Fin n) (QbarL l)) i i = ((epsL l (σ : GQ) ^ h i : (QbarL l)ˣ) : QbarL l)

def FinIneOff (P : ℕ → ValuationSubring QbarQ) (l : ℕ) {n : ℕ} [Fact l.Prime] (K : IntermediateField ℚ QbarQ)
    (ρ : K.fixingSubgroup →* GL (Fin n) (QbarL l)) : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ l → (ρ '' {σ : K.fixingSubgroup | (σ : GQ) ∈ Ine P q}).Finite

def RegSpan {l n : ℕ} [Fact l.Prime] (K : IntermediateField ℚ QbarQ) (ρ : K.fixingSubgroup →* GL (Fin n) (QbarL l)) :
    Prop :=
  Submodule.span (QbarL l) {X : Matrix (Fin n) (Fin n) (QbarL l) | ∃ σ : K.fixingSubgroup, epsL l (σ : GQ) = 1 ∧
    X = (ρ σ : Matrix (Fin n) (Fin n) (QbarL l)) ∧ X.charpoly.Separable} = ⊤

def NoCyc1 (P : ℕ → ValuationSubring QbarQ) (l : ℕ) {n : ℕ} [Fact l.Prime] (K : IntermediateField ℚ QbarQ)
    (ρ : K.fixingSubgroup →* GL (Fin n) (QbarL l)) (g : GL (Fin n) (QbarL l)) : Prop :=
  ∀ i j : Fin n, i < j → ∃ σ : K.fixingSubgroup, (σ : GQ) ∈ HcrSub l 1 (Dec P l) ∧
    inB g (ρ σ : Matrix (Fin n) (Fin n) (QbarL l)) i i ≠
      (epsL l (σ : GQ) : QbarL l) * inB g (ρ σ : Matrix (Fin n) (Fin n) (QbarL l)) j j

def IneMu (P : ℕ → ValuationSubring QbarQ) (l : ℕ) {n : ℕ} [Fact l.Prime] (K : IntermediateField ℚ QbarQ)
    (ρ : K.fixingSubgroup →* GL (Fin n) (QbarL l)) (g : GL (Fin n) (QbarL l)) (h : Fin n → ℤ) : Prop :=
  ∀ σ : K.fixingSubgroup, (σ : GQ) ∈ Ine P l → (σ : GQ) ∈ HcrSub l 1 (Dec P l) →
    ∀ i : Fin n, inB g (ρ σ : Matrix (Fin n) (Fin n) (QbarL l)) i i = ((epsL l (σ : GQ) ^ h i : (QbarL l)ˣ) : QbarL l)

def CrysOpen (l : ℕ) {n : ℕ} [Fact l.Prime] (K : IntermediateField ℚ QbarQ)
    (ρ : K.fixingSubgroup →* GL (Fin n) (QbarL l)) : Prop :=
  ∃ U : Subgroup GQ, IsOpen (U : Set GQ) ∧
    V.Crys l n (Dec V.plc l ⊓ U ⊓ K.fixingSubgroup) (V.plc l) (ρ.comp (Subgroup.inclusion inf_le_right))

end Adj

open Adj in

def ThorneB : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ n : ℕ, 2 ≤ n → ∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K],
    Module.finrank ℚ K = 2 → IsTotallyComplex K →
    ∀ ρ : K.fixingSubgroup →* GL (Fin n) (QbarL l), Continuous ρ →
    ∀ b : ℤ, (∃ π : (V.spec K n).Rep, V.IsRACSDC K n π ∧
      V.IsRi π (Formalism.BasicNotions.VData.toRecRep (Formalism.MainNotions.V.twistRep ρ (epsK K l ^ (-b))))) →
    IrredOn (Formalism.BasicNotions.TV.eps l).ker ρ → (n ≤ 3 ∨ RegSpan K ρ) → FinIneOff V.plc l K ρ →
    ∀ (g : GL (Fin n) (QbarL l)) (h : Fin n → ℤ), OrdFlag V.plc l K ρ g h →
    (NoCyc1 V.plc l K ρ g ∧ IneMu V.plc l K ρ g h ∨ CrysOpen V l K ρ) →
    ∀ (μ : GQ →* (QbarL l)ˣ) (r : GQ → Matrix (Fin n) (Fin n) (QbarL l)), Continuous μ →
    IsGGn K μ r → (∀ g : K.fixingSubgroup, r g = (ρ g : Matrix (Fin n) (Fin n) (QbarL l))) → SymSign μ →
    (∀ σ : K.fixingSubgroup, μ σ = epsL l σ ^ (1 - (n : ℤ) + 2 * b)) →
    ∀ Ad : GQ →* GL (Fin (n * n)) (QbarL l), IsAd K r Ad →
      Subsingleton (V.finiteCohomology l (n * n) ⊤ (Formalism.MainNotions.V.onTop Ad))

def BaseChange2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K],
    Module.finrank ℚ K = 2 → ∀ π : (V.spec ℚ 2).Rep, ∀ W : GQ →* GL (Fin 2) (QbarL l), Continuous W →
    V.IsRi π W → Formalism.ConjugateSelfDual.Irred (VData.toRecRep (W.comp K.fixingSubgroup.subtype)) →
    ∃ πK : (V.spec K 2).Rep, V.IsRi πK (VData.toRecRep (W.comp K.fixingSubgroup.subtype))

def IsRiAt {F : Type} [Field F] [NumberField F] [Algebra F QbarQ] {n l : ℕ} [Fact l.Prime] (ι : QbarL l ≃+* ℂ)
    (π : (V.spec F n).Rep) (ρ : Formalism.ConjugateSelfDual.G F QbarQ →* GL (Fin n) (QbarL l)) : Prop :=
  TV.GeoMatch ρ ι.toRingHom ((V.spec F n).hecke π)

theorem isRi_iff {F : Type} [Field F] [NumberField F] [Algebra F QbarQ] {n l : ℕ} [Fact l.Prime]
    (π : (V.spec F n).Rep) (ρ : Formalism.ConjugateSelfDual.G F QbarQ →* GL (Fin n) (QbarL l)) :
    V.IsRi π ρ ↔ IsRiAt V (V.iotaC l) π ρ := Iff.rfl

def IndPl (l : ℕ) [Fact l.Prime] (H : Subgroup GQ) (τ : IntermediateField.fixedField H →+* QbarL l) : Prop :=
  ∀ x : IntermediateField.fixedField H, ((x : QbarQ) ∈ V.plc l ↔ ‖τ x‖ ≤ 1)

def PureAt (F : Type) [Field F] [NumberField F] (n : ℕ) (π : (V.spec F n).Rep) : Prop :=
  ∀ M : ℕ, (V.spec F n).level π M → ∀ v : HeightOneSpectrum (𝓞 F), ((M : ℕ) : 𝓞 F) ∉ v.asIdeal →
    ∀ (τ : F →+* ℂ) (z : ℂ), ((V.spec F n).hecke π v).IsRoot z →
      ‖z‖ = (Formalism.ConjugateSelfDual.normV v : ℝ) ^ (((∑ i, ((V.spec F n).wt π τ i +
        (V.spec F n).wt π (ComplexEmbedding.conjugate τ) i) : ℤ) : ℝ) / (2 * n))

def Purity : Prop :=
  (∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K], Module.finrank ℚ K = 2 →
    IsTotallyComplex K → ∀ π : (V.spec K 3).Rep, V.IsRACSDC K 3 π → PureAt V K 3 π) ∧
  ∀ π : (V.spec ℚ 2).Rep, PureAt V ℚ 2 π

def Ram3 (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ QbarQ) (ρ : K.fixingSubgroup →* GL (Fin 3) (QbarL l))
    (M : ℕ) : Prop :=
  (∀ q : ℕ, q.Prime → q ≠ l → ∀ σ : K.fixingSubgroup, (σ : GQ) ∈ V.Iq q → (σ : GQ) ∈ FixMu M →
      ρ σ = 1) ∧
    (∃ a : ℕ, ((l - 1) ∣ a ∨ l ∣ M) ∧
      V.Crys l 3 (HcrSub l a (V.Dq l ⊓ K.fixingSubgroup)) (V.plc l)
        (ρ.comp (Subgroup.inclusion (inf_le_left.trans inf_le_right))))

def LocGlob3G : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : QbarL l ≃+* ℂ) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K],
    Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ π : (V.spec K 3).Rep, V.IsRACSDC K 3 π →
    ∀ ρ : K.fixingSubgroup →* GL (Fin 3) (QbarL l), Continuous ρ → ∀ j : ℤ,
    IsRiAt V ι π (VData.toRecRep (Formalism.MainNotions.V.twistRep ρ (((epsL l).comp K.fixingSubgroup.subtype) ^ j))) →
    ∀ M : ℕ, 0 < M →
    (∀ q : ℕ, q.Prime → q ≠ l → ∀ σ : K.fixingSubgroup, (σ : GQ) ∈ V.Iq q → (σ : GQ) ∈ FixMu M →
      ρ σ = 1) →
    (∃ a : ℕ, ((l - 1) ∣ a ∨ l ∣ M) ∧
      V.Crys l 3 (HcrSub l a (V.Dq l ⊓ K.fixingSubgroup)) (V.plc l)
        (ρ.comp (Subgroup.inclusion (inf_le_left.trans inf_le_right)))) →
    (V.spec K 3).level π M

def LocGlobWt3 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K],
    Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ π : (V.spec K 3).Rep, V.IsRACSDC K 3 π →
    ∀ ρ : K.fixingSubgroup →* GL (Fin 3) (QbarL l), Continuous ρ →
    V.IsRi π (VData.toRecRep (Formalism.MainNotions.V.twistRep ρ ((epsL l).comp K.fixingSubgroup.subtype)⁻¹)) →
    ∀ (e a : ℕ),
    (∀ τ, IndPl V l (HcrSub l a (V.Dq l ⊓ K.fixingSubgroup)) τ →
      V.HT l 3 (HcrSub l a (V.Dq l ⊓ K.fixingSubgroup)) (V.plc l)
        (ρ.comp (Subgroup.inclusion (inf_le_left.trans inf_le_right))) τ =
      ({-(e : ℤ), 0, (e : ℤ)} : Multiset ℤ)) →
    ∀ (τ : K →+* ℂ) (i : Fin 3), (V.spec K 3).wt π τ i = ![(e : ℤ) + 1, 1, 1 - (e : ℤ)] i

def Ram2 (l : ℕ) [Fact l.Prime] (W : GQ →* GL (Fin 2) (QbarL l)) (M : ℕ) : Prop :=
  (∀ q : ℕ, q.Prime → q ≠ l → ∀ σ : GQ, σ ∈ V.Iq q → σ ∈ FixMu M → W σ = 1) ∧
    (∃ (a : ℕ) (K' : IntermediateField ℚ QbarQ), ((l - 1) ∣ a ∨ l ∣ M) ∧ V.Iq l ≤ K'.fixingSubgroup ∧
      V.Crys l 2 (HcrSub l a (V.Dq l ⊓ K'.fixingSubgroup)) (V.plc l)
        (W.comp (HcrSub l a (V.Dq l ⊓ K'.fixingSubgroup)).subtype))

def LocGlob2G : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : QbarL l ≃+* ℂ) (π : (V.spec ℚ 2).Rep) (W : GQ →* GL (Fin 2) (QbarL l)),
    Continuous W →
    ∀ j : ℤ, IsRiAt V ι π (Formalism.MainNotions.V.twistRep W ((epsL l) ^ j)) → ∀ M : ℕ, 0 < M →
    (∀ q : ℕ, q.Prime → q ≠ l → ∀ σ : GQ, σ ∈ V.Iq q → σ ∈ FixMu M → W σ = 1) →
    (∃ (a : ℕ) (K' : IntermediateField ℚ QbarQ), ((l - 1) ∣ a ∨ l ∣ M) ∧ V.Iq l ≤ K'.fixingSubgroup ∧
      V.Crys l 2 (HcrSub l a (V.Dq l ⊓ K'.fixingSubgroup)) (V.plc l)
        (W.comp (HcrSub l a (V.Dq l ⊓ K'.fixingSubgroup)).subtype)) →
    (V.spec ℚ 2).level π M

def ClozelAut : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (π : (V.spec F n).Rep) (σ : ℂ ≃+* ℂ),
    ∃ π' : (V.spec F n).Rep,
      (∀ M : ℕ, (V.spec F n).level π M ↔ (V.spec F n).level π' M) ∧
      (∀ M : ℕ, (V.spec F n).level π M → ∀ v : HeightOneSpectrum (𝓞 F), ((M : ℕ) : 𝓞 F) ∉ v.asIdeal →
        (V.spec F n).hecke π' v = ((V.spec F n).hecke π v).map σ.toRingHom) ∧
      (∀ τ : F →+* ℂ, (V.spec F n).wt π' (σ.toRingHom.comp τ) = (V.spec F n).wt π τ) ∧
      (V.IsRACSDC F n π → V.IsRACSDC F n π')

def CAut (F : Type) [Field F] [NumberField F] (n : ℕ) : Prop :=
  ∀ (π : (V.spec F n).Rep) (σ : ℂ ≃+* ℂ), ∃ π' : (V.spec F n).Rep,
    (∀ M : ℕ, (V.spec F n).level π M → ∀ v : HeightOneSpectrum (𝓞 F), ((M : ℕ) : 𝓞 F) ∉ v.asIdeal →
      (V.spec F n).hecke π' v = ((V.spec F n).hecke π v).map σ.toRingHom) ∧
    (∀ τ : F →+* ℂ, (V.spec F n).wt π' (σ.toRingHom.comp τ) = (V.spec F n).wt π τ) ∧
    (V.IsRACSDC F n π → V.IsRACSDC F n π')

def ClozelAutR : Prop :=
  (∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
    CAut V K 3) ∧ CAut V ℚ 2

structure SymSp where

  hdim : IntermediateField ℚ QbarQ → ℕ → ℕ → ℕ

  cells : IntermediateField ℚ QbarQ → ℕ → ℕ

  vol : IntermediateField ℚ QbarQ → ℕ → ℝ
  vol_nonneg : ∀ K M, 0 ≤ vol K M

def Sig3 (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] (M e : ℕ) : Set (V.spec K 3).Rep :=
  {π | V.IsRACSDC K 3 π ∧ (V.spec K 3).level π M ∧
    ∀ (τ : K →+* ℂ) (i : Fin 3), (V.spec K 3).wt π τ i = ![(e : ℤ) + 1, 1, 1 - (e : ℤ)] i}

def ClozelCoh (X : SymSp) : Prop :=
  ∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K], Module.finrank ℚ K = 2 →
    IsTotallyComplex K → ∀ M e : ℕ, 0 < M → 3 ∣ M → 1 ≤ e →
    (Sig3 V K M e).ncard ≤ X.hdim K M e ∧ X.hdim K M e ≤ X.cells K M * e ^ 6

def Gelander (X : SymSp) (β : ℝ) : Prop :=
  ∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K], Module.finrank ℚ K = 2 →
    IsTotallyComplex K → ∀ M : ℕ, 0 < M → 3 ∣ M → (X.cells K M : ℝ) ≤ β * X.vol K M

def Prasad (X : SymSp) (cP : ℝ) : Prop :=
  ∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K], Module.finrank ℚ K = 2 →
    IsTotallyComplex K → ∀ M : ℕ, 0 < M →
    X.vol K (3 * M) ≤ cP * (8 * classNumber K) * |(discr K : ℝ)| ^ 4 * (M : ℝ) ^ 18

def ClassNoBound : Prop :=
  ∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K], Module.finrank ℚ K = 2 →
    IsTotallyComplex K →
    (classNumber K : ℝ) ≤ Real.sqrt (|discr K| : ℝ) * (Real.log (|discr K| : ℝ) + 2) / Real.pi

def DimFormulaE (cD : ℝ) (aD : ℕ) : Prop :=
  ∀ (M k : ℕ), 0 < M → ∀ w : (ℚ →+* ℂ) → Fin 2 → ℤ, (∀ τ, w τ 0 - w τ 1 = (k : ℤ) - 1) →
    ({π | (V.spec ℚ 2).level π M ∧ (V.spec ℚ 2).wt π = w} : Set (V.spec ℚ 2).Rep).Finite ∧
    (({π | (V.spec ℚ 2).level π M ∧ (V.spec ℚ 2).wt π = w} : Set (V.spec ℚ 2).Rep).ncard : ℝ) ≤
      cD * k * (M : ℝ) ^ aD

def DimFormula (cD : ℝ) : Prop := DimFormulaE V cD 4

def Sig2 (M e : ℕ) : Set (V.spec ℚ 2).Rep :=
  {π | (V.spec ℚ 2).level π M ∧ (V.spec ℚ 2).wt π = fun _ => ![2 * (e : ℤ), 0]}

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
    V.IsRi π (Formalism.MainNotions.V.twistRep W ((epsL l) ^ e)⁻¹) →
    (∀ τ, V.HT l 2 ⊤ (V.plc l) (Formalism.MainNotions.V.onTop W) τ = ({-(e : ℤ), (e : ℤ)} : Multiset ℤ)) →
    (V.spec ℚ 2).wt π = fun _ => ![2 * (e : ℤ), 0]

def HeckeInt3 : Prop :=
  ∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
    ∀ (M e : ℕ), 1 ≤ e → ∀ π ∈ Sig3 V K M e, ∀ v : HeightOneSpectrum (𝓞 K),
    ((M : ℕ) : 𝓞 K) ∉ v.asIdeal → ∀ z ∈ ((V.spec K 3).hecke π v).roots,
    IsIntegral ℤ ((Formalism.ConjugateSelfDual.normV v : ℂ) ^ (e - 1) * z)

def HeckeInt2 : Prop :=
  ∀ (M e : ℕ), ∀ π ∈ Sig2 V M e, ∀ v : HeightOneSpectrum (𝓞 ℚ), ((M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal →
    ∀ z ∈ ((V.spec ℚ 2).hecke π v).roots, IsIntegral ℤ z

def RhoDet3 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] (π : (V.spec K 3).Rep)
    (ρ ρ' : K.fixingSubgroup →* GL (Fin 3) (QbarL l)), Continuous ρ → Continuous ρ' →
    Formalism.ConjugateSelfDual.Irred (VData.toRecRep ρ) → Formalism.ConjugateSelfDual.Irred (VData.toRecRep ρ') →
    V.IsRi π (VData.toRecRep ρ) → V.IsRi π (VData.toRecRep ρ') → Formalism.MainNotions.V.IsIsoRep ρ ρ'

def RhoDet2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (π : (V.spec ℚ 2).Rep) (W W' : GQ →* GL (Fin 2) (QbarL l)), Continuous W →
    Continuous W' → Formalism.ConjugateSelfDual.Irred W → Formalism.ConjugateSelfDual.Irred W' → V.IsRi π W → V.IsRi π W' → Formalism.MainNotions.V.IsIsoRep W W'

def OrdBridge : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ e : ℕ, 1 ≤ e → ∀ π : (V.spec ℚ 2).Rep,
    Formalism.MainNotions.V.LevelPrimeTo V ℚ 2 π l → ∀ Vg : GQ →* GL (Fin 2) (QbarL l), Continuous Vg → Formalism.MainNotions.V.IsVg V π Vg →
    (∀ τ, V.HT l 2 ⊤ (V.plc l) (Formalism.MainNotions.V.onTop Vg) τ = {0, 2 * (e : ℤ)}) →
    (∃ w : Fin 2 → QbarL l, w ≠ 0 ∧
      (∀ g ∈ V.Dq l, ∃ c : QbarL l, (Vg g : Matrix (Fin 2) (Fin 2) (QbarL l)).mulVec w = c • w) ∧
      ((∀ g ∈ V.Iq l, (Vg g : Matrix (Fin 2) (Fin 2) (QbarL l)).mulVec w = w) ∨
        ∀ g ∈ V.Iq l, (Vg g : Matrix (Fin 2) (Fin 2) (QbarL l)).mulVec w =
          (((epsL l g)⁻¹ ^ (2 * e) : (QbarL l)ˣ) : QbarL l) • w)) →
    Formalism.MainNotions.V.OrdinaryAt V π l

def TwistDir : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (π : (V.spec ℚ 2).Rep) (W : GQ →* GL (Fin 2) (QbarL l)), Continuous W → V.IsRi π W →
    ∀ φ : DirichletCharacter ℂ l, ∃ π' : (V.spec ℚ 2).Rep,
      V.IsRi π' (Formalism.MainNotions.V.twistRep W (Formalism.MainNotions.V.phiL V l φ)) ∧ (V.spec ℚ 2).wt π' = (V.spec ℚ 2).wt π

def LocOpen (l : ℕ) (H : Subgroup GQ) : Prop :=
  IsClosed (H : Set GQ) ∧ ∃ U : Subgroup GQ, IsOpen (U : Set GQ) ∧ H ⊓ V.Dq l = U ⊓ V.Dq l

def IsBlockTri {H R : Type} [Group H] [CommRing R] {m k : ℕ} (ρ : H →* GL (Fin (m + k)) R)
    (ρ₁ : H →* GL (Fin m) R) (ρ₂ : H →* GL (Fin k) R) : Prop :=
  ∀ g : H, ∃ B : Matrix (Fin m) (Fin k) R, ((ρ g : GL (Fin (m + k)) R) : Matrix (Fin (m + k)) (Fin (m + k)) R) =
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (ρ₁ g : Matrix (Fin m) (Fin m) R) B 0 (ρ₂ g : Matrix (Fin k) (Fin k) R))

def IsBlockSum {H R : Type} [Group H] [CommRing R] {m k : ℕ} (ρ : H →* GL (Fin (m + k)) R)
    (ρ₁ : H →* GL (Fin m) R) (ρ₂ : H →* GL (Fin k) R) : Prop :=
  ∀ g : H, ((ρ g : GL (Fin (m + k)) R) : Matrix (Fin (m + k)) (Fin (m + k)) R) =
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (ρ₁ g : Matrix (Fin m) (Fin m) R) 0 0 (ρ₂ g : Matrix (Fin k) (Fin k) R))

def FonIso : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (n : ℕ) (H : Subgroup GQ), LocOpen V l H → ∀ (ρ : H →* GL (Fin n) (QbarL l))
    (M : GL (Fin n) (QbarL l)),
    (V.Crys l n H (V.plc l) ρ → V.Crys l n H (V.plc l) ((MulAut.conj M).toMonoidHom.comp ρ)) ∧
    ∀ τ, V.HT l n H (V.plc l) ((MulAut.conj M).toMonoidHom.comp ρ) τ = V.HT l n H (V.plc l) ρ τ

def FonRes : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (n : ℕ) (H H' : Subgroup GQ) (h : H' ≤ H), LocOpen V l H → LocOpen V l H' →
    ∀ ρ : H →* GL (Fin n) (QbarL l),
    (V.Crys l n H (V.plc l) ρ → V.Crys l n H' (V.plc l) (ρ.comp (Subgroup.inclusion h))) ∧
    (V.Crys l n H' (V.plc l) (ρ.comp (Subgroup.inclusion h)) →
      V.DeRham l n H (V.plc l) ρ ∧
      (∀ M : Multiset ℤ, (∀ τ, IndPl V l H τ → V.HT l n H (V.plc l) ρ τ = M) ↔
        ∀ τ, IndPl V l H' τ → V.HT l n H' (V.plc l) (ρ.comp (Subgroup.inclusion h)) τ = M) ∧
      (H ⊓ V.Iq l ≤ H' → V.Crys l n H (V.plc l) ρ))

def FonSub : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (m k : ℕ) (H : Subgroup GQ), LocOpen V l H →
    ∀ (ρ : H →* GL (Fin (m + k)) (QbarL l)) (ρ₁ : H →* GL (Fin m) (QbarL l)) (ρ₂ : H →* GL (Fin k) (QbarL l)),
    IsBlockTri ρ ρ₁ ρ₂ → V.Crys l (m + k) H (V.plc l) ρ →
    V.Crys l m H (V.plc l) ρ₁ ∧ V.Crys l k H (V.plc l) ρ₂ ∧
    ∀ τ, IndPl V l H τ → V.HT l (m + k) H (V.plc l) ρ τ = V.HT l m H (V.plc l) ρ₁ τ + V.HT l k H (V.plc l) ρ₂ τ

def FonSum : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (m k : ℕ) (H : Subgroup GQ), LocOpen V l H →
    ∀ (ρ : H →* GL (Fin (m + k)) (QbarL l)) (ρ₁ : H →* GL (Fin m) (QbarL l)) (ρ₂ : H →* GL (Fin k) (QbarL l)),
    IsBlockSum ρ ρ₁ ρ₂ → V.Crys l m H (V.plc l) ρ₁ → V.Crys l k H (V.plc l) ρ₂ → V.Crys l (m + k) H (V.plc l) ρ

def FonChar : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (H : Subgroup GQ), LocOpen V l H → ∀ κ : H →* (QbarL l)ˣ, Continuous κ → ∀ w : ℤ,
    (∀ g : H, (g : GQ) ∈ V.Iq l → κ g = epsL l (g : GQ) ^ w) →
    V.Crys l 1 H (V.plc l) (Formalism.MainNotions.V.charRep κ) ∧
    ∀ τ, IndPl V l H τ → V.HT l 1 H (V.plc l) (Formalism.MainNotions.V.charRep κ) τ = {-w}

def FonTwist : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (n : ℕ) (H : Subgroup GQ), LocOpen V l H → ∀ (ρ : H →* GL (Fin n) (QbarL l))
    (κ : H →* (QbarL l)ˣ), V.Crys l n H (V.plc l) ρ → V.Crys l 1 H (V.plc l) (Formalism.MainNotions.V.charRep κ) →
    V.Crys l n H (V.plc l) (Formalism.MainNotions.V.twistRep ρ κ) ∧
    ∀ (τ) (w : ℤ), IndPl V l H τ → V.HT l 1 H (V.plc l) (Formalism.MainNotions.V.charRep κ) τ = {w} →
      V.HT l n H (V.plc l) (Formalism.MainNotions.V.twistRep ρ κ) τ = (V.HT l n H (V.plc l) ρ τ).map (· + w)

def FonDescTri : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (H H' : Subgroup GQ) (h : H' ≤ H), LocOpen V l H → LocOpen V l H' →
    ∀ (ρ : H →* GL (Fin (1 + 1)) (QbarL l)) (κ₁ κ₂ : H →* (QbarL l)ˣ), Continuous ρ →
    IsBlockTri ρ (Formalism.MainNotions.V.charRep κ₁) (Formalism.MainNotions.V.charRep κ₂) →
    V.Crys l 1 H (V.plc l) (Formalism.MainNotions.V.charRep κ₁) → V.Crys l 1 H (V.plc l) (Formalism.MainNotions.V.charRep κ₂) →
    V.Crys l (1 + 1) H' (V.plc l) (ρ.comp (Subgroup.inclusion h)) → V.Crys l (1 + 1) H (V.plc l) ρ

def BKSum : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (m k : ℕ) (ρ : GQ →* GL (Fin (m + k)) (QbarL l)) (ρ₁ : GQ →* GL (Fin m) (QbarL l))
    (ρ₂ : GQ →* GL (Fin k) (QbarL l)), Continuous ρ₁ → Continuous ρ₂ → IsBlockSum ρ ρ₁ ρ₂ →
    ∀ c : GQ → (Fin (m + k) → QbarL l), c ∈ V.bkf l (m + k) ρ ↔
      (fun g i => c g (Fin.castAdd k i)) ∈ V.bkf l m ρ₁ ∧ (fun g i => c g (Fin.natAdd m i)) ∈ V.bkf l k ρ₂

def BKUnr : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (κ : GQ →* (QbarL l)ˣ), Continuous κ → (∀ g ∈ V.Iq l, κ g = 1) →
    ∀ c : GQ → (Fin 1 → QbarL l), c ∈ V.bkf l 1 (Formalism.MainNotions.V.charRep κ) ↔
      c ∈ TV.Z1 (Formalism.MainNotions.V.charRep κ) ∧ ∀ g ∈ V.Iq l, c g = 0

def BKNeg : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (κ : GQ →* (QbarL l)ˣ), Continuous κ → ∀ w : ℕ, 1 ≤ w →
    (∃ U : Subgroup GQ, IsOpen (U : Set GQ) ∧ ∀ g ∈ V.Iq l, g ∈ U → κ g = (epsL l g)⁻¹ ^ w) →
    ∀ c ∈ V.bkf l 1 (Formalism.MainNotions.V.charRep κ), TV.CobOn (Formalism.MainNotions.V.charRep κ) c (V.Dq l)

def BKExtNeg : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (H : Subgroup GQ), LocOpen V l H → ∀ ρ : H →* GL (Fin 2) (QbarL l), Continuous ρ →
    V.Crys l 2 H (V.plc l) ρ → (∀ g : H, (ρ g : Matrix (Fin 2) (Fin 2) (QbarL l)) 1 0 = 0) → ∀ w : ℕ, 1 ≤ w →
    (∃ U : Subgroup GQ, IsOpen (U : Set GQ) ∧ ∀ g : H, (g : GQ) ∈ V.Iq l → (g : GQ) ∈ U →
      (ρ g : Matrix (Fin 2) (Fin 2) (QbarL l)) 0 0 =
        (((epsL l (g : GQ))⁻¹ ^ w : (QbarL l)ˣ) : QbarL l) * (ρ g : Matrix (Fin 2) (Fin 2) (QbarL l)) 1 1) →
    ∃ x : QbarL l, ∀ g : H, (g : GQ) ∈ V.Dq l → (ρ g : Matrix (Fin 2) (Fin 2) (QbarL l)) 0 1 =
      x * ((ρ g : Matrix (Fin 2) (Fin 2) (QbarL l)) 0 0 - (ρ g : Matrix (Fin 2) (Fin 2) (QbarL l)) 1 1)

def SouleSel : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (F : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ F]
    (S : Finset ℕ), l ∈ S → ∀ w : ℕ, 1 ≤ w → ∀ κ : F.fixingSubgroup →* (QbarL l)ˣ, Continuous κ →
    (∃ n : ℕ, 0 < n ∧ κ ^ n = 1) →
    (∀ g : F.fixingSubgroup, (g : GQ) ∈ NOut F.fixingSubgroup S → κ g = 1) →
    ∀ c : F.fixingSubgroup → QbarL l, Continuous c →
      (∀ g h : F.fixingSubgroup, c (g * h) = c g + (((epsL l (g : GQ))⁻¹ ^ w * κ g : (QbarL l)ˣ) : QbarL l) * c h) →
      (∀ g : F.fixingSubgroup, (g : GQ) ∈ NOut F.fixingSubgroup S → c g = 0) →
      (∀ A : ValuationSubring QbarQ, Formalism.MainNotions.V.Lang.IsPlaceAbove ℚ A l → ∃ m : QbarL l,
        ∀ g : F.fixingSubgroup, (g : GQ) ∈ Formalism.MainNotions.V.Lang.Dec (F := ℚ) A →
          c g = ((((epsL l (g : GQ))⁻¹ ^ w * κ g : (QbarL l)ˣ) : QbarL l) - 1) * m) →
      ∃ m : QbarL l, ∀ g : F.fixingSubgroup,
        c g = ((((epsL l (g : GQ))⁻¹ ^ w * κ g : (QbarL l)ˣ) : QbarL l) - 1) * m

def UnramAb : Prop :=
  ∀ (F : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ F], (IsTotallyComplex F ∨ F = ⊥) →
    ∀ g ∈ F.fixingSubgroup, g ^ classNumber F ∈
      (NOut F.fixingSubgroup ∅ ⊔ ⁅F.fixingSubgroup, F.fixingSubgroup⁆).topologicalClosure

def r0M (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) (g : GQ) :
    Matrix (Fin 3) (Fin 3) (V.Ol l) :=
  extendToGroupWithForm (fun i g => ![V.psi l e χ g, 1, V.psi l e χ g⁻¹] i) K V.cc g

variable {V}

section Rcr

variable {l : ℕ} [Fact l.Prime] {e : ℕ} {χ : Chi D} {K : IntermediateField ℚ QbarQ} {g1 : GQ}

def uM (T : UnitaryThreeLiftingProblem V l e χ K g1) (v : T.P.lPl) (y : T.P.Gv v) : Matrix (Fin 3) (Fin 3) (T.P.RV v).C :=
  fun i j => T.P.uV v y (ix T.P T.hk i) (ix T.P T.hk j)

def OverO (T : UnitaryThreeLiftingProblem V l e χ K g1) (v : T.P.lPl) (ξ : (T.P.RV v).C →+* QbarL l) : Prop :=
  ∀ x : T.P.O, ξ (algebraMap T.P.O (T.P.RV v).C x) = V.jO l (T.eO x)

def IsCrPt (T : UnitaryThreeLiftingProblem V l e χ K g1) (v : T.P.lPl) (a : ℕ) (ξ : (T.P.RV v).C →+* QbarL l) : Prop :=
  OverO T v ξ ∧
  ∃ ρ : (HcrSub l a (V.Dq l ⊓ K.fixingSubgroup) : Subgroup GQ) →* GL (Fin 3) (QbarL l),
    (∀ (g : (HcrSub l a (V.Dq l ⊓ K.fixingSubgroup) : Subgroup GQ)) (y : T.P.Gv v),
      (y : T.P.Gam) = T.pr g → ∀ i j : Fin 3, (ρ g : Matrix (Fin 3) (Fin 3) (QbarL l)) i j = ξ (uM T v y i j)) ∧
    V.Crys l 3 _ (V.plc l) ρ ∧
    ∀ τ, IndPl V l _ τ → V.HT l 3 _ (V.plc l) ρ τ = ({-(e : ℤ), 0, (e : ℤ)} : Multiset ℤ)

def IsOrdPt (T : UnitaryThreeLiftingProblem V l e χ K g1) (v : T.P.lPl) (ξ : (T.P.RV v).C →+* QbarL l) : Prop :=
  OverO T v ξ ∧
  ∃ ρ : (V.Dq l ⊓ K.fixingSubgroup : Subgroup GQ) →* GL (Fin 3) (QbarL l),
    (∀ (g : (V.Dq l ⊓ K.fixingSubgroup : Subgroup GQ)) (y : T.P.Gv v),
      (y : T.P.Gam) = T.pr g → ∀ i j : Fin 3, (ρ g : Matrix (Fin 3) (Fin 3) (QbarL l)) i j = ξ (uM T v y i j)) ∧
    Ord3Raw (V.jO l) (fun i g => ![V.psi l e χ g, 1, V.psi l e χ g⁻¹] i) (V.Dq l) (V.Iq l) K.fixingSubgroup ρ

def Iord (T : UnitaryThreeLiftingProblem V l e χ K g1) (v : T.P.lPl) : Ideal (T.P.RV v).C :=
  ⨅ ξ : {ξ : (T.P.RV v).C →+* QbarL l // IsOrdPt T v ξ}, RingHom.ker ξ.1

def IsInitialPoint (T : UnitaryThreeLiftingProblem V l e χ K g1) (v : T.P.lPl) (φ₀ : (T.P.RV v).C →ₐ[T.P.O] T.P.O) : Prop :=
  ∀ g ∈ V.Dq l, ∀ y : T.P.Gv v, (y : T.P.Gam) = T.pr g → ∀ i j : Fin 3,
    T.eO (φ₀ (uM T v y i j)) = r0M V l e χ K g i j

def IsRt (T : UnitaryThreeLiftingProblem V l e χ K g1) (v : T.P.lPl) (P : Ideal (T.P.RV v).C) : Prop :=
  P.IsPrime ∧ Iord T v ≤ P ∧
  (∀ Q : Ideal (T.P.RV v).C, Q.IsPrime → Iord T v ≤ Q → Q ≤ P → Q = P) ∧
  ∃ φ₀ : (T.P.RV v).C →ₐ[T.P.O] T.P.O, IsInitialPoint T v φ₀ ∧ P ≤ RingHom.ker (φ₀ : (T.P.RV v).C →+* T.P.O)

def IsTan (T : UnitaryThreeLiftingProblem V l e χ K g1) (v : T.P.lPl) (P : Ideal (T.P.RV v).C)
    (c : T.P.Gv v → Matrix (Fin 3) (Fin 3) (QbarL l)) : Prop :=
  ∃ Φ : (T.P.RV v).C →+* DualNumber (QbarL l), (∀ x ∈ P, Φ x = 0) ∧
    (∀ x : T.P.O, Φ (algebraMap T.P.O (T.P.RV v).C x) = TrivSqZeroExt.inl (V.jO l (T.eO x))) ∧
    ∀ g ∈ V.Dq l, ∀ y : T.P.Gv v, (y : T.P.Gam) = T.pr g → ∀ i j : Fin 3,
      Φ (uM T v y i j) = TrivSqZeroExt.inl (V.jO l (r0M V l e χ K g i j)) +
        TrivSqZeroExt.inr ((c y * (r0M V l e χ K g).map (V.jO l)) i j)

end Rcr

variable (D V)

def OrdReg : Prop := ForallUnitaryThreeLiftingProblems D V fun l _ _ _ _ _ T => ∀ (v : T.P.lPl) (φ₀ : (T.P.RV v).C →ₐ[T.P.O] T.P.O), IsInitialPoint T v φ₀ →
  ∀ m : Ideal (Localization.Away (((l : ℕ) : (T.P.RV v).C ⧸ Iord T v))), ∀ [m.IsMaximal],
    m = Ideal.map (algebraMap ((T.P.RV v).C ⧸ Iord T v) (Localization.Away (((l : ℕ) : (T.P.RV v).C ⧸ Iord T v))))
      (Ideal.map (Ideal.Quotient.mk (Iord T v)) (RingHom.ker (φ₀ : (T.P.RV v).C →+* T.P.O))) →
    IsRegularLocalRing (Localization.AtPrime m) ∧ ringKrullDim (Localization.AtPrime m) = 12

def InitialPointOrdinaryClosure : Prop := ForallUnitaryThreeLiftingProblems D V fun _ _ _ _ _ _ T => ∀ (v : T.P.lPl) (φ₀ : (T.P.RV v).C →ₐ[T.P.O] T.P.O), IsInitialPoint T v φ₀ →
  Iord T v ≤ RingHom.ker (φ₀ : (T.P.RV v).C →+* T.P.O)

def TangentCocyclesFlat : Prop := ForallUnitaryThreeLiftingProblems D V fun l _ _ _ K _ T => ∀ (v : T.P.lPl) (P : Ideal (T.P.RV v).C), IsRt T v P →
  ∀ Φ : (T.P.RV v).C →+* DualNumber (QbarL l), (∀ x ∈ P, Φ x = 0) →
    (∀ x : T.P.O, Φ (algebraMap T.P.O (T.P.RV v).C x) = TrivSqZeroExt.inl (V.jO l (T.eO x))) →
    ∀ (μ : GQ →* (QbarL l)ˣ) (r c : GQ → Matrix (Fin 3) (Fin 3) (QbarL l))
      (Ad : GQ →* GL (Fin (3 * 3)) (QbarL l)), IsGGn K μ r → IsAd K r Ad →
    (∀ g ∈ V.Dq l, ∀ y : T.P.Gv v, (y : T.P.Gam) = T.pr g → ∀ i j : Fin 3,
      Φ (uM T v y i j) =
        TrivSqZeroExt.inl (r g i j) + TrivSqZeroExt.inr ((c g * r g) i j)) →
    (fun g => vecM (c g)) ∈ TV.Z1 Ad → (fun g => vecM (c g)) ∈ V.bkf l (3 * 3) Ad

def OrdOpen : Prop := ForallUnitaryThreeLiftingProblems D V fun l _ _ _ _ _ T => ∀ (v : T.P.lPl) (P : Ideal (T.P.RV v).C), IsRt T v P →
  ∃ d : (T.P.RV v).C, d ∉ P ∧
    ∀ ξ : (T.P.RV v).C →+* QbarL l, OverO T v ξ → (∀ x ∈ P, ξ x = 0) → ξ d ≠ 0 → IsOrdPt T v ξ

def TypeConst : Prop := ForallUnitaryThreeLiftingProblems D V fun l _ _ χ _ _ T => ∀ (v : T.P.lPl) (P : Ideal (T.P.RV v).C), IsRt T v P →
  ∀ ξ : (T.P.RV v).C →+* QbarL l, OverO T v ξ → (∀ x ∈ P, ξ x = 0) → IsCrPt T v (V.aOf l χ) ξ

open Polynomial in

def Lemma2 : Prop := ForallUnitaryThreeLiftingProblems D V fun l _ e χ _ _ T => ∀ (v : T.P.lPl) (P : Ideal (T.P.RV v).C), IsRt T v P →
  (∀ s ∈ V.Iq l, ∀ y : T.P.Gv v, (y : T.P.Gam) = T.pr s →
    ((uM T v y).map (Ideal.Quotient.mk P)).charpoly = ∏ i : Fin 3, (X - C (Ideal.Quotient.mk P
      (algebraMap T.P.O (T.P.RV v).C (T.eO.symm (![V.psi l e χ s, 1, V.psi l e χ s⁻¹] i)))))) ∧
  ∀ (s : Fin 3 → GQ) (y : Fin 3 → T.P.Gv v), (∀ i, s i ∈ V.Iq l) → (∀ i, (y i : T.P.Gam) = T.pr (s i)) →
    ∀ a b : Fin 3,
      ((uM T v (y 0) - Matrix.scalar (Fin 3) (algebraMap T.P.O (T.P.RV v).C (T.eO.symm (V.psi l e χ (s 0))))) *
        (uM T v (y 1) - 1) *
        (uM T v (y 2) - Matrix.scalar (Fin 3) (algebraMap T.P.O (T.P.RV v).C (T.eO.symm (V.psi l e χ (s 2)⁻¹)))))
        a b ∈ P

def TanDims : Prop := ForallUnitaryThreeLiftingProblems D V fun l _ _ _ _ _ T => ∀ (v : T.P.lPl) (P : Ideal (T.P.RV v).C), IsRt T v P →
  ∀ w : Fin 5, ∃ W : Submodule (QbarL l) (T.P.Gv v → Matrix (Fin 3) (Fin 3) (QbarL l)),
    (∀ c, c ∈ W ↔ IsTan T v P c ∧ ∀ y (i j : Fin 3), ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) ≠ ((w : ℕ) : ℤ) - 2 → c y i j = 0) ∧
    Module.finrank (QbarL l) W = ![1, 2, 3, 4, 2] w

def lit0 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K],
    Formalism.MainNotions.V.UnitaryThreeData V l e χ K → ∀ g1 : GQ, Formalism.MainNotions.V.IsNormElt V l e χ K g1 →
    Nonempty (UnitaryThreeLiftingProblem V l e χ K g1)

def lit1 : Prop := LitShaEFinite V

def lit2 : Prop := ForallUnitaryThreeLiftingProblems D V fun _ _ _ _ _ _ T => Formalism.MainNotions.UnusedSlot38.LitG T.P

def lit3 (D : D7) (_V : VData D) : Prop := Soule

def lit4 : Prop := ThorneB V ∧ Thorne2 V

def lit5 : Prop := BaseChange2 V

def lit6 : Prop := Purity V ∧ LocGlob3G V ∧ LocGlobWt3 V ∧ LocGlob2G V

def lit7 (X : SymSp) : Prop := ClozelAutR V ∧ ClozelCoh V X

def lit8E (X : SymSp) (β cP cD : ℝ) (aD : ℕ) : Prop :=
  Gelander X β ∧ Prasad X cP ∧ ClassNoBound ∧ DimFormulaE V cD aD

def lit8 (X : SymSp) (β cP cD : ℝ) : Prop := lit8E D V X β cP cD 4

def lit9 : Prop := (OrdReg D V ∧ InitialPointOrdinaryClosure D V) ∧ TangentCocyclesFlat D V ∧ OrdOpen D V ∧ TypeConst D V

def LocalGlobalChebotarev : Prop :=
  LGUnr3 V ∧ LGUnr2 V ∧ LocGlobWt2 V ∧ HeckeInt3 V ∧ HeckeInt2 V ∧ RhoDet3 V ∧ RhoDet2 V

def OrdinaryModularTwists : Prop := OrdBridge V ∧ TwistDir V

def BlochKatoResults : Prop := BKSum V ∧ BKUnr V ∧ BKNeg V ∧ BKExtNeg V

def FontaineTheoryResults : Prop := FonIso V ∧ FonRes V ∧ FonSub V ∧ FonSum V ∧ FonChar V ∧ FonTwist V ∧ FonDescTri V

def PoitouTateClassField (D : D7) (_V : VData D) : Prop := SouleSel ∧ UnramAb

def GradedTangentSpace : Prop := Lemma2 D V ∧ TanDims D V

def LitB : Prop := LocalGlobalChebotarev D V ∧ OrdinaryModularTwists D V ∧ BlochKatoResults D V ∧ FontaineTheoryResults D V ∧ PoitouTateClassField D V ∧ GradedTangentSpace D V

def LitE (X : SymSp) (β cP cD : ℝ) (aD : ℕ) : Prop :=
  lit0 D V ∧ lit1 D V ∧ lit2 D V ∧ lit3 D V ∧ lit4 D V ∧ lit5 D V ∧ lit6 D V ∧ lit7 D V X ∧
    lit8E D V X β cP cD aD ∧ lit9 D V ∧ LitB D V

def Lit (X : SymSp) (β cP cD : ℝ) : Prop := LitE D V X β cP cD 4

def LiftingLemmasStatement (X : SymSp) (β cP cD C₁ C₂ : ℝ) : Prop := Lit D V X β cP cD → admitted D V → Conclusion₂ D V C₁ C₂

def ExponentFormsStatement (X : SymSp) (β cP cD : ℝ) (aD : ℕ) (C₁ C₂ : ℝ) : Prop :=
  LitE D V X β cP cD aD → admitted D V → ConclusionE₂ D V C₁ C₂ (max 6 (aD + 1))

theorem stmtLE_four (X : SymSp) (β cP cD C₁ C₂ : ℝ) :
    ExponentFormsStatement D V X β cP cD 4 C₁ C₂ ↔ LiftingLemmasStatement D V X β cP cD C₁ C₂ := Iff.rfl

theorem Gelander.max_zero {X : SymSp} {β : ℝ} (h : Gelander X β) : Gelander X (max β 0) := by
  intro K _ h2 hc M hM h3
  exact (h K h2 hc M hM h3).trans (mul_le_mul_of_nonneg_right (le_max_left β 0) (X.vol_nonneg K M))

theorem LitE.max_zero {D : D7} {V : VData D} {X : SymSp} {β cP cD : ℝ} {aD : ℕ} (h : LitE D V X β cP cD aD) :
    LitE D V X (max β 0) cP cD aD :=
  let ⟨h0, h1, h2, h3, h4, h5, h6, h7, ⟨g, r⟩, h9⟩ := h
  ⟨h0, h1, h2, h3, h4, h5, h6, h7, ⟨g.max_zero, r⟩, h9⟩

theorem Lit.max_zero {D : D7} {V : VData D} {X : SymSp} {β cP cD : ℝ} (h : Lit D V X β cP cD) :
    Lit D V X (max β 0) cP cD := LitE.max_zero h

end Lit

def UniformConstantStatement : Prop :=
  ∀ β cP cD : ℝ, ∃ C₁ C₂ : ℝ, ∀ (D : D7) (V : VData D) (X : SymSp), LiftingLemmasStatement D V X β cP cD C₁ C₂

def UniformExponentFormsStatement : Prop :=
  ∀ (β cP cD : ℝ) (aD : ℕ), aD ≤ 18 → ∃ C₁ C₂ : ℝ, ∀ (D : D7) (V : VData D) (X : SymSp),
    ExponentFormsStatement D V X β cP cD aD C₁ C₂

theorem UniformExponentFormsStatement.abs (h : UniformExponentFormsStatement) : UniformConstantStatement := fun β cP cD => h β cP cD 4 (by norm_num)

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (VF : ∀ x (i : Fm.Ix x), VData (Fm.D x i))

def OrbitValuationBound (C₁ C₂ : ℝ) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Conclusion₂ (Fm.D x i) (VF x i) C₁ C₂
def AdmF : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, admitted (Fm.D x i) (VF x i)
def LitF (X : SymSp) (β cP cD : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Lit (Fm.D x i) (VF x i) X β cP cD
def KudlaFamilyStatement (C₁ C₂ : ℝ) : Prop := AdmF Fm VF → OrbitValuationBound Fm VF C₁ C₂
def FamilyLiftingStatement (X : SymSp) (β cP cD C₁ C₂ : ℝ) : Prop :=
  LitF Fm VF X β cP cD → AdmF Fm VF → OrbitValuationBound Fm VF C₁ C₂

def FamilyExponentFormsBound (C₁ C₂ : ℝ) (bD : ℕ) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ConclusionE₂ (Fm.D x i) (VF x i) C₁ C₂ bD
def LitFE (X : SymSp) (β cP cD : ℝ) (aD : ℕ) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, LitE (Fm.D x i) (VF x i) X β cP cD aD
def FamilyExponentFormsStatement (X : SymSp) (β cP cD : ℝ) (aD : ℕ) (C₁ C₂ : ℝ) : Prop :=
  LitFE Fm VF X β cP cD aD → AdmF Fm VF → FamilyExponentFormsBound Fm VF C₁ C₂ (max 6 (aD + 1))

theorem family_exponent_forms_of (X : SymSp) (β cP cD : ℝ) (aD : ℕ) (C₁ C₂ : ℝ)
    (h : ∀ x (i : Fm.Ix x), ExponentFormsStatement (Fm.D x i) (VF x i) X β cP cD aD C₁ C₂) :
    FamilyExponentFormsStatement Fm VF X β cP cD aD C₁ C₂ := by
  rintro ⟨a, hL⟩ ⟨b, hA⟩
  exact ⟨max a b, fun x hx i => h x i (hL x (le_trans (le_max_left a b) hx) i)
    (hA x (le_trans (le_max_right a b) hx) i)⟩

theorem family_statement_of_records (X : SymSp) (β cP cD C₁ C₂ : ℝ)
    (h : ∀ x (i : Fm.Ix x), LiftingLemmasStatement (Fm.D x i) (VF x i) X β cP cD C₁ C₂) :
    FamilyLiftingStatement Fm VF X β cP cD C₁ C₂ := by
  rintro ⟨a, hL⟩ ⟨b, hA⟩
  exact ⟨max a b, fun x hx i => h x i (hL x (le_trans (le_max_left a b) hx) i)
    (hA x (le_trans (le_max_right a b) hx) i)⟩

end Fam

section X

open NumberField IsDedekindDomain

def IsCSDOne {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {n l : ℕ} [Fact l.Prime]
    (ρ : Formalism.ConjugateSelfDual.G K Ω →* GL (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) : Prop :=
  ∃ s : K ≃+* K, s ≠ RingEquiv.refl K ∧
    ∃ (τ : Ω ≃+* Ω) (hτ : ∀ x : K, τ (algebraMap K _ x) = algebraMap K _ (s x)), (∀ x, τ (τ x) = x) ∧
    ∃ J : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l), J.det ≠ 0 ∧ J.transpose = J ∧ ∀ σ : Formalism.ConjugateSelfDual.G K Ω,
      (ρ σ : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)).transpose * J *
        (ρ (Formalism.ConjugateSelfDual.conjGal s τ hτ σ) : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) = J

def OrdFixAt {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {n l : ℕ} [Fact l.Prime]
    (ρ : Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) (A : ValuationSubring Ω) (k : Fin n → ℤ) (M : ℕ) : Prop :=
  ∃ g : GL (Fin n) (Formalism.ConjugateSelfDual.Qbar l),
    (∀ σ ∈ A.decompositionSubgroup F,
      ((g⁻¹ * ρ σ * g : GL (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)).BlockTriangular id) ∧
    ∀ σ ∈ Formalism.ConjugateSelfDual.Inertia (F := F) A, (∀ ζ : Ω, ζ ^ M = 1 → σ ζ = ζ) → ∀ i : Fin n,
      ((g⁻¹ * ρ σ * g : GL (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) i i =
        ((Formalism.ConjugateSelfDual.cyc F Ω l σ : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l) ^ (k i)

def OrdFixAbove {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {n l : ℕ} [Fact l.Prime]
    (ρ : Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) (k : Fin n → ℤ) (M : ℕ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → ∀ A, Formalism.ConjugateSelfDual.IsPlaceOver A v → OrdFixAt ρ A k M

variable {D}

def LocGlob3N : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K],
    Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ π : (V.spec K 3).Rep, V.IsRACSDC K 3 π →
    ∀ (ι : QbarL l ≃+* ℂ) (ρ : K.fixingSubgroup →* GL (Fin 3) (QbarL l)), Continuous ρ →
    Formalism.ConjugateSelfDual.Irred (VData.toRecRep ρ) → IsCSDOne (VData.toRecRep ρ) → ∀ k : Fin 3 → ℤ, StrictAnti k →
    ∀ M : ℕ, 0 < M → OrdFixAbove (VData.toRecRep ρ) k M → ∀ j : ℤ,
    (∀ (τ : K →+* ℂ) (i : Fin 3), (V.spec K 3).wt π τ i = -k i.rev - j) →
    IsRiAt V ι π (VData.toRecRep (Formalism.MainNotions.V.twistRep ρ (((epsL l).comp K.fixingSubgroup.subtype) ^ j))) →
    Ram3 V l K ρ M → (V.spec K 3).level π M

theorem LocGlob3G.toN {D : D7} {V : VData D} (h : LocGlob3G V) : LocGlob3N V :=
  fun l _ _ K _ h2 hc π hπ ι ρ hρ _ _ _ _ M hM _ j _ hri hr => h l ι K h2 hc π hπ ρ hρ j hri M hM hr.1 hr.2

def Sig3CountE (C : ℝ) (B : ℕ) : Prop :=
  ∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
    ∀ M e : ℕ, 0 < M → 1 ≤ e → (Sig3 V K M e).Finite ∧
      ((Sig3 V K M e).ncard : ℝ) ≤ C * (|(NumberField.discr K : ℝ)| * (M : ℝ) * (e : ℝ)) ^ B

def Sig2CountE (C : ℝ) (B : ℕ) : Prop :=
  ∀ (M k : ℕ), 0 < M → ∀ w : (ℚ →+* ℂ) → Fin 2 → ℤ, (∀ τ, w τ 0 - w τ 1 = (k : ℤ) - 1) →
    ({π | (V.spec ℚ 2).level π M ∧ (V.spec ℚ 2).wt π = w} : Set (V.spec ℚ 2).Rep).Finite ∧
    (({π | (V.spec ℚ 2).level π M ∧ (V.spec ℚ 2).wt π = w} : Set (V.spec ℚ 2).Rep).ncard : ℝ) ≤
      C * ((M : ℝ) * (k : ℝ)) ^ B

theorem DimFormulaE.toSig2 {D : D7} {V : VData D} {cD : ℝ} {aD : ℕ} (h : DimFormulaE V cD aD) :
    Sig2CountE V (max cD 0) (max aD 1) := by
  intro M k hM w hw
  refine ⟨(h M k hM w hw).1, (h M k hM w hw).2.trans ?_⟩
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h1 : max aD 1 ≠ 0 := by have := le_max_right aD 1; omega
    simp [h1]
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have e1 : (k : ℝ) ≤ (k : ℝ) ^ (max aD 1) := by
      calc (k : ℝ) = (k : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (k : ℝ) ^ (max aD 1) := pow_le_pow_right₀ hk1 (le_max_right _ _)
    have e2 : (M : ℝ) ^ aD ≤ (M : ℝ) ^ (max aD 1) := pow_le_pow_right₀ hM1 (le_max_left _ _)
    have e3 : (k : ℝ) * (M : ℝ) ^ aD ≤ ((M : ℝ) * (k : ℝ)) ^ (max aD 1) := by
      rw [mul_pow, mul_comm]
      exact mul_le_mul e2 e1 (by positivity) (by positivity)
    calc cD * k * (M : ℝ) ^ aD = cD * ((k : ℝ) * (M : ℝ) ^ aD) := by ring
      _ ≤ max cD 0 * ((k : ℝ) * (M : ℝ) ^ aD) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max cD 0 * ((M : ℝ) * (k : ℝ)) ^ (max aD 1) := mul_le_mul_of_nonneg_left e3 (le_max_right _ _)

variable (D)

open Classical in

def GaussianCaseFreeExponents (C₁ : ℝ) (bN be : ℕ) : Prop :=
  ∀ e ∈ eRange D, ∀ χ : Chi D, ∀ p : ℕ, p.Prime → ¬ p ∣ 30 * condV D →
    ∃ NN : GaussianInt, NN ≠ 0 ∧
      Real.log ‖GaussianInt.toComplex NN‖ ≤
        C₁ * (degQ D χ : ℝ) * (condV D : ℝ) ^ bN * (e : ℝ) ^ be * Real.log p ∧
      ∀ (l : ℕ) [Fact l.Prime], l ≠ p → ∀ K : IntermediateField ℚ QbarQ, [FiniteDimensional ℚ K] →
        Formalism.MainNotions.V.UnitaryThreeData V l e χ K → Formalism.MainNotions.V.UnitaryCaseGaussian V l e χ K →
        ∑ χ'' ∈ Finset.univ.filter (ChiConj D χ), V.Vlen l e χ'' ≤
          2 * (padicValInt l (Zsqrtd.norm NN) : ℕ∞)

def InertCaseFreeExponents (C₂ : ℝ) (bD bN be : ℕ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K],
    Formalism.MainNotions.V.UnitaryThreeData V l e χ K → Formalism.MainNotions.V.UnitaryCaseInert V l χ K →
    ∃ v : ℕ, V.Vlen l e χ = v ∧
      (v : ℝ) * Real.log l ≤
        C₂ * |(NumberField.discr K : ℝ)| ^ bD * (degQ D χ : ℝ) * (condV D : ℝ) ^ bN * (e : ℝ) ^ be *
          Real.log (Real.log ((condV D : ℝ) * l))

def HeightBoundsFreeExponents (C₁ C₂ : ℝ) (bD bN be : ℕ) : Prop := Conclusion1 D V ∧ GaussianCaseFreeExponents D V C₁ bN be ∧ InertCaseFreeExponents D V C₂ bD bN be

theorem gaussian_bound_text_iff (C₁ : ℝ) : GaussianCaseFreeExponents D V C₁ 18 7 ↔ GaussianCaseHeightBound D V C₁ := Iff.rfl
theorem inert_bound_text_iff (C₂ : ℝ) (bD : ℕ) : InertCaseFreeExponents D V C₂ bD 18 7 ↔ InertBoundExponent D V C₂ bD := Iff.rfl
theorem free_exponents_eighteen_seven_iff (C₁ C₂ : ℝ) (bD : ℕ) : HeightBoundsFreeExponents D V C₁ C₂ bD 18 7 ↔ ConclusionE₂ D V C₁ C₂ bD := Iff.rfl

theorem free_exponents_six_eighteen_seven_iff (C₁ C₂ : ℝ) : HeightBoundsFreeExponents D V C₁ C₂ 6 18 7 ↔ Conclusion₂ D V C₁ C₂ := Iff.rfl

def lit6N : Prop := Purity V ∧ LocGlob3N V ∧ LocGlobWt3 V ∧ LocGlob2G V

theorem lit6.toN {D : D7} {V : VData D} (h : lit6 D V) : lit6N D V := ⟨h.1, h.2.1.toN, h.2.2⟩

def DeJong : Prop := ForallUnitaryThreeLiftingProblems D V fun l _ _ _ _ _ T => ∀ (W : V1.TR T.P.O) [IsDomain W.C], ((l : ℕ) : W.C) ≠ 0 →
  ∀ F : W.C, F ≠ 0 →
    ∃ y : W.C →+* QbarL l, (∀ x : T.P.O, y (algebraMap T.P.O W.C x) = V.jO l (T.eO x)) ∧ y F ≠ 0

def DeJongGenericFibrePoints : Prop := DeJong D V

def LitGeo : Prop :=
  lit0 D V ∧ lit1 D V ∧ lit2 D V ∧ lit3 D V ∧ lit4 D V ∧ lit5 D V ∧ lit6N D V ∧ lit9 D V ∧ LitB D V ∧ DeJongGenericFibrePoints D V

def LitX (C₃ : ℝ) (B₃ : ℕ) (C₂ : ℝ) (B₂ : ℕ) : Prop :=
  LitGeo D V ∧ ClozelAutR V ∧ Sig3CountE V C₃ B₃ ∧ Sig2CountE V C₂ B₂

theorem LitE.toX {D : D7} {V : VData D} {X : SymSp} {β cP cD : ℝ} {aD : ℕ} (h : LitE D V X β cP cD aD)
    (h16 : DeJongGenericFibrePoints D V) {C₃ : ℝ} {B₃ : ℕ} (h3 : Sig3CountE V C₃ B₃) : LitX D V C₃ B₃ (max cD 0) (max aD 1) :=
  let ⟨h0, h1, h2, h3', h4, h5, h6, h7, h8, h9, hB⟩ := h
  ⟨⟨h0, h1, h2, h3', h4, h5, h6.toN, h9, hB, h16⟩, h7.1, h3, h8.2.2.2.toSig2⟩

def FreeExponentStatement (C₃ : ℝ) (B₃ : ℕ) (C₂ : ℝ) (B₂ : ℕ) (C₁ C₂' : ℝ) : Prop :=
  LitX D V C₃ B₃ C₂ B₂ → admitted D V → HeightBoundsFreeExponents D V C₁ C₂' (max B₃ B₂ + 1) (max B₃ B₂) (max B₃ B₂ + 1)

end X

def UniformFreeExponentOnClass (𝒞 : ∀ D : D7, VData D → Prop) : Prop :=
  ∀ (C₃ : ℝ) (B₃ : ℕ) (C₂ : ℝ) (B₂ : ℕ), ∃ C₁ C₂' : ℝ, ∀ (D : D7) (V : VData D), 𝒞 D V →
    FreeExponentStatement D V C₃ B₃ C₂ B₂ C₁ C₂'

def UniformFreeExponentAllRecords : Prop :=
  ∀ (C₃ : ℝ) (B₃ : ℕ) (C₂ : ℝ) (B₂ : ℕ), ∃ C₁ C₂' : ℝ, ∀ (D : D7) (V : VData D), FreeExponentStatement D V C₃ B₃ C₂ B₂ C₁ C₂'

theorem UniformFreeExponentAllRecords.on (h : UniformFreeExponentAllRecords) (𝒞 : ∀ D : D7, VData D → Prop) : UniformFreeExponentOnClass 𝒞 :=
  fun C₃ B₃ C₂ B₂ => let ⟨C₁, C₂', h'⟩ := h C₃ B₃ C₂ B₂; ⟨C₁, C₂', fun D V _ => h' D V⟩

theorem stmtLAbsXOn_true : UniformFreeExponentOnClass (fun _ _ => True) ↔ UniformFreeExponentAllRecords :=
  ⟨fun h C₃ B₃ C₂ B₂ => let ⟨C₁, C₂', h'⟩ := h C₃ B₃ C₂ B₂; ⟨C₁, C₂', fun D V => h' D V trivial⟩, fun h => h.on _⟩

section FamX

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (VF : ∀ x (i : Fm.Ix x), VData (Fm.D x i))

def FamilyFreeExponentBound (C₁ C₂ : ℝ) (bD bN be : ℕ) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, HeightBoundsFreeExponents (Fm.D x i) (VF x i) C₁ C₂ bD bN be
def LitFX (C₃ : ℝ) (B₃ : ℕ) (C₂ : ℝ) (B₂ : ℕ) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, LitX (Fm.D x i) (VF x i) C₃ B₃ C₂ B₂
def FamilyFreeExponentStatement (C₃ : ℝ) (B₃ : ℕ) (C₂ : ℝ) (B₂ : ℕ) (C₁ C₂' : ℝ) : Prop :=
  LitFX Fm VF C₃ B₃ C₂ B₂ → AdmF Fm VF → FamilyFreeExponentBound Fm VF C₁ C₂' (max B₃ B₂ + 1) (max B₃ B₂) (max B₃ B₂ + 1)

theorem family_bound_text_iff (C₁ C₂ : ℝ) : FamilyFreeExponentBound Fm VF C₁ C₂ 6 18 7 ↔ OrbitValuationBound Fm VF C₁ C₂ := Iff.rfl

theorem family_free_exponent_of (C₃ : ℝ) (B₃ : ℕ) (C₂ : ℝ) (B₂ : ℕ) (C₁ C₂' : ℝ)
    (h : ∀ x (i : Fm.Ix x), FreeExponentStatement (Fm.D x i) (VF x i) C₃ B₃ C₂ B₂ C₁ C₂') :
    FamilyFreeExponentStatement Fm VF C₃ B₃ C₂ B₂ C₁ C₂' := by
  rintro ⟨a, hL⟩ ⟨b, hA⟩
  exact ⟨max a b, fun x hx i => h x i (hL x (le_trans (le_max_left a b) hx) i)
    (hA x (le_trans (le_max_right a b) hx) i)⟩

theorem UniformFreeExponentOnClass.fam {𝒞 : ∀ D : D7, VData D → Prop} (h : UniformFreeExponentOnClass 𝒞) (C₃ : ℝ) (B₃ : ℕ) (C₂ : ℝ) (B₂ : ℕ) :
    ∃ C₁ C₂' : ℝ, ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (VF : ∀ x (i : Fm.Ix x), VData (Fm.D x i)),
      (∀ x (i : Fm.Ix x), 𝒞 (Fm.D x i) (VF x i)) → FamilyFreeExponentStatement Fm VF C₃ B₃ C₂ B₂ C₁ C₂' :=
  let ⟨C₁, C₂', h'⟩ := h C₃ B₃ C₂ B₂
  ⟨C₁, C₂', fun Fm VF hc => family_free_exponent_of Fm VF C₃ B₃ C₂ B₂ C₁ C₂' fun x i => h' _ _ (hc x i)⟩

end FamX

end Formalism.MainNotions.UnitaryThreeHeightBounds
