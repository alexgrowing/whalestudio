import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.ModelSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsExamples
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver secOver secMOver GeneratesOver cechHc cechZc
  quotPart cechMap IsMGraded)
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing intNum IsMultiProjPrime specialIdeal genFib IsModelOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim resDeg)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)

section Coordinates

variable {K : Type} {ι : K → Type} {Ω : Type*}

def blockVec (y : (Σ k, ι k) → Ω) (k : K) : ι k → Ω := fun i => y ⟨k, i⟩

def oneBlock {κ : Type} (x : κ → Ω) : (Σ _ : Unit, κ) → Ω := fun p => x p.2

def baseDeg [DecidableEq K] (k₀ : K) : K → ℤ := Pi.single k₀ 1

variable {K₁ K₀ : Type} {ι₁ : K₁ → Type} {ι₀ : K₀ → Type}

def joinVec (y₁ : (Σ k, ι₁ k) → Ω) (y₀ : (Σ k, ι₀ k) → Ω) : (Σ k, Sum.elim ι₁ ι₀ k) → Ω
  | ⟨Sum.inl k, i⟩ => y₁ ⟨k, i⟩
  | ⟨Sum.inr k, i⟩ => y₀ ⟨k, i⟩

def joinChart (c₁ : ∀ k, ι₁ k) (c₀ : ∀ k, ι₀ k) : ∀ k, Sum.elim ι₁ ι₀ k
  | Sum.inl k => c₁ k
  | Sum.inr k => c₀ k

def pullDeg (β : K₀ → ℤ) : K₁ ⊕ K₀ → ℤ := Sum.elim 0 β

instance joinFintype [∀ k, Fintype (ι₁ k)] [∀ k, Fintype (ι₀ k)] :
    ∀ k, Fintype (Sum.elim ι₁ ι₀ k)
  | Sum.inl k => (inferInstance : Fintype (ι₁ k))
  | Sum.inr k => (inferInstance : Fintype (ι₀ k))

end Coordinates

section Points

variable {S : Type*} [CommRing S] {Ω : Type*} [Field Ω] [Algebra S Ω]
variable {K : Type} {ι : K → Type}

def locIn (A : Subalgebra S Ω) (p : Ideal A) : Subring Ω :=
  Subring.closure {u | ∃ a b : A, b ∉ p ∧ u = (a : Ω) / b}

variable (S) in

def modelPts (y : (Σ k, ι k) → Ω) : Set (Subring Ω) :=
  {z | ∃ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) ∧
    ∃ p : Ideal (chartRingOver S y c), p.IsPrime ∧ z = locIn (chartRingOver S y c) p}

variable (S) in

def SameModel {K' : Type} {ι' : K' → Type} (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) : Prop :=
  modelPts S y = modelPts S y'

variable (S) in

def IsModelWithBase (y : (Σ k, ι k) → Ω) (k₀ : K) : Prop :=
  (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) ∧ SameModel S y (oneBlock (blockVec y k₀))

variable (S) in

def Dominates {K₁ : Type} {ι₁ : K₁ → Type} (y₁ : (Σ k, ι₁ k) → Ω) (y₀ : (Σ k, ι k) → Ω) : Prop :=
  ∀ z₁ ∈ modelPts S y₁, ∃ z₀ ∈ modelPts S y₀, z₀ ≤ z₁ ∧ ∀ a ∈ z₀, a⁻¹ ∈ z₁ → a⁻¹ ∈ z₀

variable (S) in

def IsBirational (y : (Σ k, ι k) → Ω) : Prop :=
  ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → Subfield.closure (chartRingOver S y c : Set Ω) = ⊤

variable (S) in

def IsNormalModel (y : (Σ k, ι k) → Ω) : Prop :=
  ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → IsIntegrallyClosed (chartRingOver S y c)

end Points

section Bundles

variable (S : Type*) [CommRing S] {Ω : Type*} [Field Ω] [Algebra S Ω]
variable {K : Type} [Fintype K] {ι : K → Type}

def IsGenerated (y : (Σ k, ι k) → Ω) (β : K → ℤ) : Prop :=
  ∃ (n : ℕ) (s : Fin n → Ω), (∀ j, s j ∈ secOver S y β) ∧ GeneratesOver S y β s

def VeryAmple (y : (Σ k, ι k) → Ω) (β : K → ℤ) : Prop :=
  ∃ (n : ℕ) (x' : Fin n → Ω), (∀ j, x' j ∈ secOver S y β) ∧ GeneratesOver S y β x' ∧
    SameModel S y (oneBlock x')

def MultipleVeryAmple (y : (Σ k, ι k) → Ω) (μ ν : K → ℤ) (t : ℚ) : Prop :=
  ∃ (a : ℕ) (m : ℤ), 1 ≤ a ∧ (m : ℚ) = a * t ∧ VeryAmple S y (a • μ + m • ν)

def preimRing (y : (Σ k, ι k) → Ω) {n : ℕ} (h : Fin n → Ω) (j : Fin n) : Subalgebra S Ω :=
  ⨅ (c : ∀ k, ι k) (_ : ∀ k, y ⟨k, c k⟩ ≠ 0),
    chartRingOver S (joinVec y (oneBlock h)) (joinChart c (fun _ : Unit => j))

def IsAmpleByFiniteMap (y : (Σ k, ι k) → Ω) (η : K → ℤ) : Prop :=
  ∃ (m n : ℕ) (h : Fin n → Ω), 1 ≤ m ∧ (∀ j, h j ∈ secOver S y (m • η)) ∧
    GeneratesOver S y (m • η) h ∧
    ∀ j, h j ≠ 0 → ∃ (r : ℕ) (b : Fin r → Ω), (∀ l, b l ∈ preimRing S y h j) ∧
      (preimRing S y h j : Set Ω) ⊆
        Submodule.span (ReciprocityTheory.ChartRestriction.G.Geo.chartRing S h j) (Set.range b)

end Bundles

section Graded

variable (S : Type*) [CommRing S] {Ω : Type*} [Field Ω] [Algebra S Ω]
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

def twistSum (y : (Σ k, ι k) → Ω) (k₀ : K) (β : K → ℤ) (c₁ : ℤ) :
    Submodule (ReciprocityTheory.ChartRestriction.G.Geo.coneRing S (blockVec y k₀)) (Polynomial Ω) :=
  Submodule.span _ {f | ∃ (n : ℕ) (s : Ω), s ∈ secOver S y (β + (c₁ + n) • baseDeg k₀) ∧
    f = Polynomial.C s * Polynomial.X ^ n}

def genRing {n : ℕ} (η : Fin n → Ω) : Subalgebra S (Polynomial Ω) :=
  Algebra.adjoin S (Set.range fun j => Polynomial.C (η j) * Polynomial.X)

def powerSum (y : (Σ k, ι k) → Ω) (γ β : K → ℤ) {n : ℕ} (η : Fin n → Ω) :
    Submodule (genRing S η) (Polynomial Ω) :=
  Submodule.span _ {f | ∃ (b : ℕ) (s : Ω), s ∈ secOver S y (γ + b • β) ∧
    f = Polynomial.C s * Polynomial.X ^ b}

end Graded

section Residue

variable (S : Type*) [CommRing S] {Ω : Type*} [Field Ω] [Algebra S Ω]
variable {K : Type} {ι : K → Type}

def ResField (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c)) [p.IsPrime] :
    Type _ :=
  FractionRing (chartRingOver S y c ⧸ p)

instance resField.field (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c))
    [p.IsPrime] : Field (ResField S y c p) :=
  @FractionRing.field _ _ (Ideal.Quotient.isDomain p)

instance resField.algebraQuot (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (p : Ideal (chartRingOver S y c)) [p.IsPrime] :
    Algebra (chartRingOver S y c ⧸ p) (ResField S y c p) :=
  inferInstanceAs (Algebra _ (FractionRing (chartRingOver S y c ⧸ p)))

instance resField.algebraBase (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (p : Ideal (chartRingOver S y c)) [p.IsPrime] : Algebra S (ResField S y c p) :=
  inferInstanceAs (Algebra S (FractionRing (chartRingOver S y c ⧸ p)))

open Classical in

def residue (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c)) [p.IsPrime]
    (u : Ω) : ResField S y c p :=
  if h : u ∈ chartRingOver S y c then
    algebraMap (chartRingOver S y c ⧸ p) _ (Ideal.Quotient.mk p ⟨u, h⟩)
  else 0

def modVec (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c)) [p.IsPrime] :
    (Σ k, ι k) → ResField S y c p :=
  fun q => residue S y c p (y q / y ⟨q.1, c q.1⟩)

def resImage (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c)) [p.IsPrime]
    (z : Subring Ω) : Set (ResField S y c p) :=
  {v | ∃ a b : chartRingOver S y c, b ∉ p ∧ (a : Ω) / b ∈ z ∧
    v = algebraMap (chartRingOver S y c ⧸ p) (ResField S y c p) (Ideal.Quotient.mk p a) /
      algebraMap (chartRingOver S y c ⧸ p) (ResField S y c p) (Ideal.Quotient.mk p b)}

end Residue

section Numbers

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def IsNefIdeal (F : Type) [Field F] (P : Ideal (MRing ι F)) (β : K → ℤ) : Prop :=
  ∀ W : Ideal (MRing ι F), IsMultiProjPrime W → P ≤ W → relDim W = ((1 : ℕ) : WithBot (WithTop ℤ)) →
    0 ≤ intNum F W ![β]

def IsNef (F : Type) [Field F] {Ω : Type*} [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω)
    (β : K → ℤ) : Prop :=
  IsNefIdeal F (mIdealOver F y) β

end Numbers

section StepObjects

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type*} [Field Ω]

def stepL (k₀ : K) (μ : K → ℤ) (a : ℕ) (m : ℤ) : K → ℤ := a • μ + m • baseDeg k₀

variable (S : Type*) [CommRing S] [Algebra S Ω] [∀ k, Fintype (ι k)]

def divIdeal (y : (Σ k, ι k) → Ω) (D : K → ℤ) (σ : Ω) : Ideal (MRingOver S ι) :=
  Ideal.span {g | ∃ δ : K → ℕ, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g δ ∧
    ∃ f ∈ secOver S y ((fun k => (δ k : ℤ)) - D), aeval y g = σ * f}

def IsStepData (F : Type) [Field F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (d : ℕ)
    (μ : K → ℤ) (r : ℚ) (a : ℕ) (m : ℤ) (c₁ : ℕ) (σ : Ω) : Prop :=
  IsModelWithBase F y k₀ ∧ relDim (mIdealOver F y) = ((d : ℕ) : WithBot (WithTop ℤ)) ∧
    IsNef F y μ ∧ 0 < r ∧ 1 ≤ a ∧ (m : ℚ) = a * r ∧ 1 ≤ c₁ ∧
    σ ∈ secOver F y (stepL k₀ μ a m - (c₁ : ℤ) • baseDeg k₀) ∧ σ ≠ 0

end StepObjects

def FiniteSections.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    IsNoetherianRing S → IsModelWithBase S y k₀ → ∀ β : K → ℤ,
      Module.Finite S (secOver S y β) ∧
      (∀ c₁ : ℤ, Module.Finite (ReciprocityTheory.ChartRestriction.G.Geo.coneRing S (blockVec y k₀)) (twistSum S y k₀ β c₁)) ∧
      ∀ (S' : Type) [CommRing S'] [Algebra S S'] [Algebra S' Ω] [IsScalarTower S S' Ω]
        (M : Submonoid S) [IsLocalization M S'],
        secOver S' y β = Submodule.span S' (secOver S y β : Set Ω)

def FiniteTwists.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
    (γ β : K → ℤ) (n : ℕ) (η : Fin n → Ω),
    IsNoetherianRing S → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ j, η j ∈ secOver S y β) →
    GeneratesOver S y β η → Module.Finite (genRing S η) (powerSum S y γ β η)

def Domination.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)]
    (K₀ : Type) [Fintype K₀] [DecidableEq K₀] (ι₀ : K₀ → Type) [∀ k, Fintype (ι₀ k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y₁ : (Σ k, ι₁ k) → Ω) (y₀ : (Σ k, ι₀ k) → Ω) (k₀ : K₀),
    IsNoetherianRing S → (∀ k, ∃ i, y₁ ⟨k, i⟩ ≠ 0) → IsModelWithBase S y₀ k₀ →
    Dominates S y₁ y₀ →
    (∀ (F : Type) [Field F] [Algebra S F] [Algebra F Ω] [IsScalarTower S F Ω] [IsFractionRing S F],
      SameModel F y₁ y₀ →
      ∃ m : S, m ∈ nonZeroDivisors S ∧ ∀ β : K₀ → ℤ,
        ∀ s ∈ secOver S (joinVec y₁ y₀) (pullDeg β), algebraMap S Ω m * s ∈ secOver S y₀ β) ∧
    (IsBirational S y₁ → IsBirational S y₀ → IsNormalModel S y₀ →
      ∀ β : K₀ → ℤ, secOver S (joinVec y₁ y₀) (pullDeg β) = secOver S y₀ β) ∧
    (IsBirational S y₁ → IsBirational S y₀ →
      ∃ (c : ℕ) (κ : Ω), κ ∈ secOver S y₀ (c • baseDeg k₀) ∧ κ ≠ 0 ∧
        ∀ β : K₀ → ℤ, ∀ s ∈ secOver S (joinVec y₁ y₀) (pullDeg β),
          κ * s ∈ secOver S y₀ (β + c • baseDeg k₀))

def SurjectiveClosed.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω]
    (y : (Σ k, ι k) → Ω) (k₀ : K) (J' : Ideal (MRingOver S ι)) (hJ : mIdealOver S y ≤ J'),
    IsNoetherianRing S → IsModelWithBase S y k₀ → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal J' →
    ∀ β : K → ℤ, ∃ c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c →
      ∀ z'' ∈ cechZc ι (quotPart S J') (β + c • baseDeg k₀) 0,
        ∃ z ∈ cechZc ι (quotPart S (mIdealOver S y)) (β + c • baseDeg k₀) 0,
          cechMap S ι (Submodule.factor hJ) 0 z = z''

def Restriction.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) (K' : Type) (ι' : K' → Type)
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω),
    SameModel S y y' →
    ∀ (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c)) [p.IsPrime], (∀ k, y ⟨k, c k⟩ ≠ 0) →
      modelPts S (modVec S y c p) =
        {z' | ∃ z ∈ modelPts S y, z ≤ locIn (chartRingOver S y c) p ∧
          z' = Subring.closure (resImage S y c p z)} ∧
      (∀ β : K → ℤ, ∀ s ∈ secOver S y β,
        residue S y c p (s * ∏ k, y ⟨k, c k⟩ ^ (-β k)) ∈ secOver S (modVec S y c p) β) ∧
      ∀ (c' : ∀ k, ι' k) (p' : Ideal (chartRingOver S y' c')) [p'.IsPrime],
        (∀ k, y' ⟨k, c' k⟩ ≠ 0) →
        locIn (chartRingOver S y' c') p' = locIn (chartRingOver S y c) p →
        ∃ φ : ResField S y c p ≃ₐ[S] ResField S y' c' p',
          (∀ z ∈ modelPts S y, z ≤ locIn (chartRingOver S y c) p →
            φ '' resImage S y c p z = resImage S y' c' p' z) ∧
          SameModel S (fun q => φ (modVec S y c p q)) (modVec S y' c' p')

def HilbertPoint.Statement : Prop :=
  ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] (Ω : Type) [Field Ω] [Algebra F Ω] (x' : κ → Ω),
    (∃ i, x' i ≠ 0) →
    relDim (mIdealOver F (oneBlock x')) = ((0 : ℕ) : WithBot (WithTop ℤ)) →
    (∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      Module.finrank F (secMOver F (oneBlock x') (fun _ => n)) =
        resDeg (mIdealOver F (oneBlock x'))) ∧
    0 < intNum F (mIdealOver F (oneBlock x')) (![] : Fin 0 → Unit → ℤ) ∧
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      secOver F (oneBlock x') (fun _ => (n : ℤ)) = secMOver F (oneBlock x') (fun _ => n)

def HilbertPositive.Statement : Prop :=
  ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] (Ω : Type) [Field Ω] [Algebra F Ω] (x' : κ → Ω)
    (e : ℕ), (∃ i, x' i ≠ 0) → 1 ≤ e →
    relDim (mIdealOver F (oneBlock x')) = ((e : ℕ) : WithBot (WithTop ℤ)) →
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(Module.finrank F (secMOver F (oneBlock x') (fun _ => n)) : ℝ) -
          (intNum F (mIdealOver F (oneBlock x')) (fun _ : Fin e => fun _ : Unit => (1 : ℤ)) : ℝ) *
            (n : ℝ) ^ e / (e.factorial : ℝ)| ≤ C * (n : ℝ) ^ (e - 1)) ∧
    0 < intNum F (mIdealOver F (oneBlock x')) (fun _ : Fin e => fun _ : Unit => (1 : ℤ)) ∧
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      secOver F (oneBlock x') (fun _ => (n : ℤ)) = secMOver F (oneBlock x') (fun _ => n)

def SectionCount.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K)
    (d : ℕ) (ν : K → ℤ) (q : ℕ),
    IsModelWithBase F y k₀ → relDim (mIdealOver F y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) →
    VeryAmple F y ν → 1 ≤ q →
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      ((intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => ν) : ℝ) -
          ((d + 1 : ℕ) : ℝ) * (intNum F (mIdealOver F y)
            (Fin.snoc (α := fun _ => K → ℤ) (fun _ : Fin d => ν) (q • baseDeg k₀)) : ℝ)) *
          (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) - C * (n : ℝ) ^ d ≤
        (Module.finrank F (secOver F y (n • (ν - q • baseDeg k₀))) : ℝ)

def SectionExists.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K)
    (d : ℕ) (μ : K → ℤ) (t s' : ℚ),
    IsModelWithBase F y k₀ → relDim (mIdealOver F y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) →
    IsNef F y μ → 0 < s' → s' < t / (d + 1) → MultipleVeryAmple F y μ (baseDeg k₀) t →
    ∃ (a : ℕ) (m : ℤ) (c₁ : ℕ), 1 ≤ a ∧ (m : ℚ) = a * (t - s') ∧ 1 ≤ c₁ ∧
      ∃ σ ∈ secOver F y (stepL k₀ μ a m - (c₁ : ℤ) • baseDeg k₀), σ ≠ 0

def KAt (d : ℕ) : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    IsModelWithBase F y k₀ → relDim (mIdealOver F y) = ((d : ℕ) : WithBot (WithTop ℤ)) →
    ∀ μ : K → ℤ, IsNef F y μ → ∀ t : ℚ, 0 < t → MultipleVeryAmple F y μ (baseDeg k₀) t

def StepTwo.Statement : Prop :=
  ∀ d : ℕ, (∀ d' < d, KAt d') →
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (k₀ : K) (μ : K → ℤ) (r : ℚ) (a : ℕ) (m : ℤ) (c₁ : ℕ) (σ : Ω),
    IsStepData F y k₀ d μ r a m c₁ σ →
    ∀ (G : Type) [AddCommGroup G] [Module (MRingOver F ι) G] [Module F G]
      [IsScalarTower F (MRingOver F ι) G] (𝓖 : (K → ℤ) → Submodule F G),
      Module.Finite (MRingOver F ι) G → IsMGraded F ι 𝓖 →
      (∀ g ∈ divIdeal F y (stepL k₀ μ a m - (c₁ : ℤ) • baseDeg k₀) σ, ∀ v : G, g • v = 0) →
      ∃ c₀ : ℕ, ∀ b c : ℕ, c₀ ≤ c →
        Subsingleton (cechHc ι 𝓖 (b • stepL k₀ μ a m + c • baseDeg k₀) 1)

def ClaimVanish.Statement : Prop :=
  ∀ d : ℕ, (∀ d' < d, KAt d') →
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (k₀ : K) (μ : K → ℤ) (r : ℚ) (a : ℕ) (m : ℤ) (c₁ : ℕ) (σ : Ω),
    IsStepData F y k₀ d μ r a m c₁ σ →
    ∃ c₀ : ℕ, ∀ b c : ℕ, c₀ ≤ c →
      Subsingleton (cechHc ι (quotPart F (mIdealOver F y)) (b • stepL k₀ μ a m + c • baseDeg k₀) 1)

def StepThree.Statement : Prop :=
  ∀ d : ℕ, (∀ d' < d, KAt d') →
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (k₀ : K) (μ : K → ℤ) (r : ℚ) (a : ℕ) (m : ℤ) (c₁ : ℕ) (σ : Ω),
    IsStepData F y k₀ d μ r a m c₁ σ →
    ∃ c₂ : ℕ, ∀ b : ℕ, 1 ≤ b → IsGenerated F y (b • stepL k₀ μ a m + c₂ • baseDeg k₀)

def VeryAmpleNefPlusAmple.Statement : Prop :=
  ∀ d : ℕ, KAt d

def NefPlusAmple.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω)
    (η μ : K → ℤ) (ε : ℚ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → IsAmpleByFiniteMap F y η → IsNef F y μ → 0 < ε →
    MultipleVeryAmple F y μ η ε

def NefProductNonneg.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (d : ℕ)
    (μs : Fin d → K → ℤ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → relDim (mIdealOver F y) = ((d : ℕ) : WithBot (WithTop ℤ)) →
    (∀ j, IsNef F y (μs j)) → 0 ≤ intNum F (mIdealOver F y) μs

def NefGeneric.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ)
    (β : K → ℤ),
    IsModelOver P d → IsNefIdeal (IsLocalRing.ResidueField O) (specialIdeal P) β →
    IsNefIdeal (FractionRing O) (genFib P) β

section Examples

variable (F : Type) [Field F]

abbrev pnIdx (N : ℕ) : Unit → Type := fun _ => Fin (N + 1)

abbrev pnField (N : ℕ) : Type := FractionRing (MvPolynomial (Σ k, pnIdx N k) F)

def pnPt (N : ℕ) : (Σ k, pnIdx N k) → pnField F N :=
  fun p => algebraMap (MvPolynomial (Σ k, pnIdx N k) F) (pnField F N) (X p)

theorem pnPt_ne_zero (N : ℕ) (p : Σ k, pnIdx N k) : pnPt F N p ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Σ k, pnIdx N k) F)
    (pnField F N))).mpr (MvPolynomial.X_ne_zero p)

theorem mIdealOver_pnPt (N : ℕ) : mIdealOver F (pnPt F N) = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Ideal.mem_bot]
  have hcomp : ((MvPolynomial.aeval (R := pnField F N) (fun _ : Unit => (1 : pnField F N))).restrictScalars F).comp
      (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.mConeMapOver F (pnPt F N)) =
      IsScalarTower.toAlgHom F (MvPolynomial (Σ k, pnIdx N k) F) (pnField F N) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.mConeMapOver, pnPt]
  have h1 := AlgHom.congr_fun hcomp f
  have hf' : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.mConeMapOver F (pnPt F N) f = 0 := hf
  rw [AlgHom.comp_apply, hf', map_zero] at h1
  exact (IsFractionRing.injective _ (pnField F N)) (by rw [IsScalarTower.toAlgHom_apply] at h1; rw [← h1, map_zero])

theorem relDim_pnPt (N : ℕ) :
    relDim (mIdealOver F (pnPt F N)) = ((N : ℕ) : WithBot (WithTop ℤ)) := by
  rw [mIdealOver_pnPt]
  exact GroundTheory.Heights₂.Heights.FieldNumbers.relDim_projectiveSpace N

theorem isModelWithBase_pnPt (N : ℕ) : IsModelWithBase F (pnPt F N) () :=
  ⟨fun _ => ⟨0, pnPt_ne_zero F N _⟩, rfl⟩

theorem pnPt_mem_secOver (N : ℕ) (j : Fin (N + 1)) :
    pnPt F N ⟨(), j⟩ ∈ secOver F (pnPt F N) (baseDeg ()) := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]
  intro c _
  have e : pnPt F N ⟨(), j⟩ * ∏ k, pnPt F N ⟨k, c k⟩ ^ (-baseDeg () k) =
      pnPt F N ⟨(), j⟩ / pnPt F N ⟨(), c ()⟩ := by
    simp [baseDeg, div_eq_mul_inv]
  rw [e]
  exact Algebra.subset_adjoin ⟨⟨(), j⟩, rfl⟩

theorem pnPt_generates (N : ℕ) :
    GeneratesOver F (pnPt F N) (baseDeg ()) (fun j : Fin (N + 1) => pnPt F N ⟨(), j⟩) := by
  intro c hc
  refine ⟨fun j => if j = c () then 1 else 0, fun j => ?_, ?_⟩
  · show (if j = c () then (1 : pnField F N) else 0) ∈ _
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · simp [baseDeg, Finset.sum_ite_eq']
    exact mul_inv_cancel₀ (hc ())

theorem veryAmple_pnPt (N : ℕ) : VeryAmple F (pnPt F N) (baseDeg ()) :=
  ⟨N + 1, fun j => pnPt F N ⟨(), j⟩, pnPt_mem_secOver F N, pnPt_generates F N, rfl⟩

theorem isNef_zero {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) : IsNef F y (0 : K → ℤ) := by
  intro W _ _ _
  rw [(GroundTheory.Heights₂.Heights.FieldNumbers.IntNumZeroSlot.full F K ι W).1 1 ![0] 0 rfl]

theorem isNefIdeal_zero {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) : IsNefIdeal F P (0 : K → ℤ) := by
  intro W _ _ _
  rw [(GroundTheory.Heights₂.Heights.FieldNumbers.IntNumZeroSlot.full F K ι W).1 1 ![0] 0 rfl]

theorem dominates_self {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {K : Type}
    {ι : K → Type} (y : (Σ k, ι k) → Ω) : Dominates S y y :=
  fun z hz => ⟨z, hz, le_rfl, fun _ _ h => h⟩

def ptOne : (Σ _ : Unit, Fin 1) → F := fun _ => 1

theorem isField_subalgebra_self (A : Subalgebra F F) : IsField A where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_comm := mul_comm
  mul_inv_cancel {a} ha := by
    refine ⟨⟨(a : F)⁻¹, by simpa using A.algebraMap_mem (a : F)⁻¹⟩, Subtype.ext ?_⟩
    have : (a : F) ≠ 0 := fun h => ha (Subtype.ext h)
    simp [this]

theorem isBirational_ptOne : IsBirational F (ptOne F) := by
  intro c _
  rw [eq_top_iff]
  intro u _
  exact Subfield.subset_closure (by simpa using (chartRingOver F (ptOne F) c).algebraMap_mem u)

theorem isNormalModel_ptOne : IsNormalModel F (ptOne F) := by
  intro c _
  let _ : Field (chartRingOver F (ptOne F) c) := (isField_subalgebra_self F _).toField
  exact Field.instIsIntegrallyClosed _

theorem isModelWithBase_ptOne : IsModelWithBase F (ptOne F) () :=
  ⟨fun _ => ⟨0, one_ne_zero⟩, rfl⟩

theorem FiniteSections.hypotheses_example :
    IsNoetherianRing F ∧ IsModelWithBase F (pnPt F 1) () ∧
      IsLocalization (⊥ : Submonoid F) F :=
  ⟨inferInstance, isModelWithBase_pnPt F 1, IsLocalization.self bot_le⟩

theorem FiniteTwists.hypotheses_example :
    IsNoetherianRing F ∧ (∀ k, ∃ i, pnPt F 1 ⟨k, i⟩ ≠ 0) ∧
      (∀ j, pnPt F 1 ⟨(), j⟩ ∈ secOver F (pnPt F 1) (baseDeg ())) ∧
      GeneratesOver F (pnPt F 1) (baseDeg ()) (fun j : Fin 2 => pnPt F 1 ⟨(), j⟩) :=
  ⟨inferInstance, fun _ => ⟨0, pnPt_ne_zero F 1 _⟩, pnPt_mem_secOver F 1, pnPt_generates F 1⟩

theorem Domination.hypotheses_example :
    (IsNoetherianRing F ∧ (∀ k, ∃ i, pnPt F 1 ⟨k, i⟩ ≠ 0) ∧ IsModelWithBase F (pnPt F 1) () ∧
      Dominates F (pnPt F 1) (pnPt F 1) ∧ IsFractionRing F F ∧ SameModel F (pnPt F 1) (pnPt F 1)) ∧
    (IsNoetherianRing F ∧ (∀ k, ∃ i, ptOne F ⟨k, i⟩ ≠ 0) ∧ IsModelWithBase F (ptOne F) () ∧
      Dominates F (ptOne F) (ptOne F) ∧ IsBirational F (ptOne F) ∧ IsNormalModel F (ptOne F)) :=
  ⟨⟨inferInstance, fun _ => ⟨0, pnPt_ne_zero F 1 _⟩, isModelWithBase_pnPt F 1, dominates_self _,
      IsFractionRing.self_iff_nonZeroDivisors_le_isUnit.mpr
        (fun x hx => show IsUnit x from isUnit_iff_ne_zero.mpr (nonZeroDivisors.ne_zero hx)), rfl⟩,
    ⟨inferInstance, fun _ => ⟨0, one_ne_zero⟩, isModelWithBase_ptOne F, dominates_self _,
      isBirational_ptOne F, isNormalModel_ptOne F⟩⟩

theorem SurjectiveClosed.hypotheses_example :
    IsNoetherianRing F ∧ IsModelWithBase F (pnPt F 1) () ∧
      ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal (mIdealOver F (pnPt F 1)) ∧
      mIdealOver F (pnPt F 1) ≤ mIdealOver F (pnPt F 1) := by
  refine ⟨inferInstance, isModelWithBase_pnPt F 1, ?_, le_rfl⟩
  rw [mIdealOver_pnPt]
  exact ⟨∅, fun _ h => absurd h (Set.notMem_empty _), by rw [Ideal.span_empty]⟩

theorem Restriction.hypotheses_example :
    SameModel F (pnPt F 1) (pnPt F 1) ∧ (∀ k, pnPt F 1 ⟨k, (fun _ => 0 : ∀ k, pnIdx 1 k) k⟩ ≠ 0) ∧
      (⊥ : Ideal (chartRingOver F (pnPt F 1) (fun _ => 0))).IsPrime ∧
      locIn (chartRingOver F (pnPt F 1) (fun _ => 0)) ⊥ =
        locIn (chartRingOver F (pnPt F 1) (fun _ => 0)) ⊥ :=
  ⟨rfl, fun _ => pnPt_ne_zero F 1 _, Ideal.isPrime_bot, rfl⟩

theorem HilbertPoint.hypotheses_example :
    (∃ i, (fun j : Fin 1 => pnPt F 0 ⟨(), j⟩) i ≠ 0) ∧
      relDim (mIdealOver F (oneBlock (fun j : Fin 1 => pnPt F 0 ⟨(), j⟩))) =
        ((0 : ℕ) : WithBot (WithTop ℤ)) :=
  ⟨⟨0, pnPt_ne_zero F 0 _⟩, relDim_pnPt F 0⟩

theorem HilbertPositive.hypotheses_example :
    (∃ i, (fun j : Fin 2 => pnPt F 1 ⟨(), j⟩) i ≠ 0) ∧ 1 ≤ 1 ∧
      relDim (mIdealOver F (oneBlock (fun j : Fin 2 => pnPt F 1 ⟨(), j⟩))) =
        ((1 : ℕ) : WithBot (WithTop ℤ)) :=
  ⟨⟨0, pnPt_ne_zero F 1 _⟩, le_rfl, relDim_pnPt F 1⟩

theorem SectionCount.hypotheses_example :
    IsModelWithBase F (pnPt F 1) () ∧
      relDim (mIdealOver F (pnPt F 1)) = ((0 + 1 : ℕ) : WithBot (WithTop ℤ)) ∧
      VeryAmple F (pnPt F 1) (baseDeg ()) ∧ 1 ≤ 1 :=
  ⟨isModelWithBase_pnPt F 1, relDim_pnPt F 1, veryAmple_pnPt F 1, le_rfl⟩

theorem multipleVeryAmple_pnPt :
    MultipleVeryAmple F (pnPt F 1) (0 : Unit → ℤ) (baseDeg ()) 1 :=
  ⟨1, 1, le_rfl, by norm_num, by simpa using veryAmple_pnPt F 1⟩

theorem SectionExists.hypotheses_example :
    IsModelWithBase F (pnPt F 1) () ∧
      relDim (mIdealOver F (pnPt F 1)) = ((0 + 1 : ℕ) : WithBot (WithTop ℤ)) ∧
      IsNef F (pnPt F 1) 0 ∧ (0 : ℚ) < 1 / 2 ∧ (1 / 2 : ℚ) < 1 / ((0 : ℕ) + 1) ∧
      MultipleVeryAmple F (pnPt F 1) (0 : Unit → ℤ) (baseDeg ()) 1 :=
  ⟨isModelWithBase_pnPt F 1, relDim_pnPt F 1, isNef_zero F _, by norm_num, by norm_num,
    multipleVeryAmple_pnPt F⟩

theorem isStepData_example :
    IsStepData F (pnPt F 1) () 1 0 (1 / 2) 2 1 1 1 := by
  refine ⟨isModelWithBase_pnPt F 1, relDim_pnPt F 1, isNef_zero F _, by norm_num, by norm_num,
    by norm_num, le_rfl, ?_, one_ne_zero⟩
  have e : stepL () (0 : Unit → ℤ) 2 1 - ((1 : ℕ) : ℤ) • baseDeg () = 0 := by
    funext k
    simp [stepL, baseDeg]
  rw [e]
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]
  intro c _
  simp

theorem VeryAmpleNefPlusAmple.hypotheses_example :
    IsModelWithBase F (pnPt F 1) () ∧
      relDim (mIdealOver F (pnPt F 1)) = ((1 : ℕ) : WithBot (WithTop ℤ)) ∧
      IsNef F (pnPt F 1) 0 ∧ (0 : ℚ) < 1 :=
  ⟨isModelWithBase_pnPt F 1, relDim_pnPt F 1, isNef_zero F _, one_pos⟩

theorem isAmpleByFiniteMap_pnPt (N : ℕ) : IsAmpleByFiniteMap F (pnPt F N) (baseDeg ()) := by
  refine ⟨1, N + 1, fun j => pnPt F N ⟨(), j⟩, le_rfl, ?_, ?_, ?_⟩
  · simpa using pnPt_mem_secOver F N
  · simpa using pnPt_generates F N
  · intro j _
    refine ⟨1, ![1], fun _ => by simp, ?_⟩
    intro s hs
    have hs' : s ∈ chartRingOver F (joinVec (pnPt F N) (oneBlock fun j => pnPt F N ⟨(), j⟩))
        (joinChart (fun _ => j) (fun _ : Unit => j)) := by
      unfold preimRing at hs
      exact Algebra.mem_iInf.mp (Algebra.mem_iInf.mp hs (fun _ => j)) (fun _ => pnPt_ne_zero F N _)
    have hle : chartRingOver F (joinVec (pnPt F N) (oneBlock fun j => pnPt F N ⟨(), j⟩))
        (joinChart (fun _ => j) (fun _ : Unit => j)) ≤
        ReciprocityTheory.ChartRestriction.G.Geo.chartRing F (fun j => pnPt F N ⟨(), j⟩) j := by
      apply Algebra.adjoin_le
      rintro _ ⟨⟨k | k, i⟩, rfl⟩
      · exact Algebra.subset_adjoin ⟨i, rfl⟩
      · exact Algebra.subset_adjoin ⟨i, rfl⟩
    have hs'' := hle hs'
    have h1 : (1 : pnField F N) ∈ Submodule.span
        (ReciprocityTheory.ChartRestriction.G.Geo.chartRing F (fun j => pnPt F N ⟨(), j⟩) j) (Set.range ![(1 : pnField F N)]) :=
      Submodule.subset_span ⟨0, rfl⟩
    have := Submodule.smul_mem _ (⟨s, hs''⟩ : ReciprocityTheory.ChartRestriction.G.Geo.chartRing F (fun j => pnPt F N ⟨(), j⟩) j) h1
    simpa [Subalgebra.smul_def] using this

theorem NefPlusAmple.hypotheses_example :
    (∀ k, ∃ i, pnPt F 1 ⟨k, i⟩ ≠ 0) ∧ IsAmpleByFiniteMap F (pnPt F 1) (baseDeg ()) ∧
      IsNef F (pnPt F 1) 0 ∧ (0 : ℚ) < 1 :=
  ⟨fun _ => ⟨0, pnPt_ne_zero F 1 _⟩, isAmpleByFiniteMap_pnPt F 1, isNef_zero F _, one_pos⟩

theorem NefProductNonneg.hypotheses_example :
    (∀ k, ∃ i, pnPt F 1 ⟨k, i⟩ ≠ 0) ∧
      relDim (mIdealOver F (pnPt F 1)) = ((1 : ℕ) : WithBot (WithTop ℤ)) ∧
      ∀ j, IsNef F (pnPt F 1) ((![0] : Fin 1 → Unit → ℤ) j) := by
  refine ⟨fun _ => ⟨0, pnPt_ne_zero F 1 _⟩, relDim_pnPt F 1, fun j => ?_⟩
  rw [Subsingleton.elim j 0]
  exact isNef_zero F _

end Examples

theorem NefGeneric.hypotheses_example :
    IsModelOver (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) (PowerSeries ℚ))) 1 ∧
      IsNefIdeal (IsLocalRing.ResidueField (PowerSeries ℚ))
        (specialIdeal (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) (PowerSeries ℚ)))) 0 :=
  ⟨GroundTheory.Heights₂.Heights.NumbersDVR.isModelOver_projectiveSpace 1, isNefIdeal_zero _ _⟩

section Fit

variable (F : Type) [Field F]

example (h : FiniteSections.Statement) :=
  h F Unit (pnIdx 1) (pnField F 1) (pnPt F 1) () inferInstance (isModelWithBase_pnPt F 1) (baseDeg ())

example (h : FiniteTwists.Statement) :=
  h F Unit (pnIdx 1) (pnField F 1) (pnPt F 1) 0 (baseDeg ()) 2 (fun j => pnPt F 1 ⟨(), j⟩)
    inferInstance (fun _ => ⟨0, pnPt_ne_zero F 1 _⟩) (pnPt_mem_secOver F 1) (pnPt_generates F 1)

example (h : Domination.Statement) :=
  haveI : IsFractionRing F F := (Domination.hypotheses_example F).1.2.2.2.2.1
  And.intro ((h F Unit (pnIdx 1) Unit (pnIdx 1) (pnField F 1) (pnPt F 1) (pnPt F 1) () inferInstance
    (fun _ => ⟨0, pnPt_ne_zero F 1 _⟩) (isModelWithBase_pnPt F 1) (dominates_self _)).1 F rfl)
   ((h F Unit (fun _ => Fin 1) Unit (fun _ => Fin 1) F (ptOne F) (ptOne F) () inferInstance
    (fun _ => ⟨0, one_ne_zero⟩) (isModelWithBase_ptOne F) (dominates_self _)).2.1
      (isBirational_ptOne F) (isBirational_ptOne F) (isNormalModel_ptOne F))

example (h : SurjectiveClosed.Statement) :=
  h F Unit (pnIdx 1) (pnField F 1) (pnPt F 1) () (mIdealOver F (pnPt F 1)) le_rfl inferInstance
    (isModelWithBase_pnPt F 1) (SurjectiveClosed.hypotheses_example F).2.2.1 (baseDeg ())

example (h : Restriction.Statement) :=
  h F Unit (pnIdx 1) Unit (pnIdx 1) (pnField F 1) (pnPt F 1) (pnPt F 1) rfl (fun _ => 0) ⊥
    (fun _ => pnPt_ne_zero F 1 _)

example (h : HilbertPoint.Statement) :=
  h F (Fin 1) (pnField F 0) (fun j => pnPt F 0 ⟨(), j⟩) ⟨0, pnPt_ne_zero F 0 _⟩ (relDim_pnPt F 0)

example (h : HilbertPositive.Statement) :=
  h F (Fin 2) (pnField F 1) (fun j => pnPt F 1 ⟨(), j⟩) 1 ⟨0, pnPt_ne_zero F 1 _⟩ le_rfl
    (relDim_pnPt F 1)

example (h : SectionCount.Statement) :=
  h F Unit (pnIdx 1) (pnField F 1) (pnPt F 1) () 0 (baseDeg ()) 1 (isModelWithBase_pnPt F 1)
    (relDim_pnPt F 1) (veryAmple_pnPt F 1) le_rfl

example (h : SectionExists.Statement) :=
  h F Unit (pnIdx 1) (pnField F 1) (pnPt F 1) () 0 0 1 (1 / 2) (isModelWithBase_pnPt F 1)
    (relDim_pnPt F 1) (isNef_zero F _) (by norm_num) (by norm_num) (multipleVeryAmple_pnPt F)

example (h : VeryAmpleNefPlusAmple.Statement) :=
  h 1 F Unit (pnIdx 1) (pnField F 1) (pnPt F 1) () (isModelWithBase_pnPt F 1) (relDim_pnPt F 1) 0
    (isNef_zero F _) 1 one_pos

example (h : StepTwo.Statement) (hK : ∀ d' < 1, KAt d') :=
  h 1 hK F Unit (pnIdx 1) (pnField F 1) (pnPt F 1) () 0 (1 / 2) 2 1 1 1 (isStepData_example F)

example (h : ClaimVanish.Statement) (hK : ∀ d' < 1, KAt d') :=
  h 1 hK F Unit (pnIdx 1) (pnField F 1) (pnPt F 1) () 0 (1 / 2) 2 1 1 1 (isStepData_example F)

example (h : StepThree.Statement) (hK : ∀ d' < 1, KAt d') :=
  h 1 hK F Unit (pnIdx 1) (pnField F 1) (pnPt F 1) () 0 (1 / 2) 2 1 1 1 (isStepData_example F)

example (h : NefPlusAmple.Statement) :=
  h F Unit (pnIdx 1) (pnField F 1) (pnPt F 1) (baseDeg ()) 0 1 (fun _ => ⟨0, pnPt_ne_zero F 1 _⟩)
    (isAmpleByFiniteMap_pnPt F 1) (isNef_zero F _) one_pos

example (h : NefProductNonneg.Statement) :=
  h F Unit (pnIdx 1) (pnField F 1) (pnPt F 1) 1 ![0] (fun _ => ⟨0, pnPt_ne_zero F 1 _⟩)
    (relDim_pnPt F 1) (NefProductNonneg.hypotheses_example F).2.2

example (h : NefGeneric.Statement) :=
  h (PowerSeries ℚ) Unit (fun _ => Fin 2) ⊥ 1 0 NefGeneric.hypotheses_example.1
    NefGeneric.hypotheses_example.2

end Fit

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2
