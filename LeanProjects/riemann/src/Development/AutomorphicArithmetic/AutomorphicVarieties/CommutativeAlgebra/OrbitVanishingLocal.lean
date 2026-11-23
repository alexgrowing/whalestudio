import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

noncomputable section

open IsLocalRing MvPowerSeries

namespace UpperTheory.V.Alg

structure IsNVal (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    (v : K → ℝ) : Prop where
  mul : ∀ x y, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y
  add : ∀ x y, x ≠ 0 → y ≠ 0 → x + y ≠ 0 → min (v x) (v y) ≤ v (x + y)
  base : ∀ c : O, c ≠ 0 → v (algebraMap O K c) = ((IsDiscreteValuationRing.addVal O c).toNat : ℝ)

abbrev tz {K : Type} [CommRing K] (t : Kˣ) : Multiplicative ℤ →* Kˣ := zpowersHom Kˣ t

section Data

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]

structure IsWRing [IsLocalRing O] (x : A →ₐ[O] O) : Prop where
  co : IsCO O (𝒜 0)
  gen : ∃ s : Finset A, (∀ z ∈ s, z ∈ 𝒜 (-2) ∨ z ∈ 𝒜 (-1) ∨ z ∈ 𝒜 1 ∨ z ∈ 𝒜 2) ∧
    Algebra.adjoin O ((𝒜 0 : Set A) ∪ s) = ⊤
  fixed : ∀ j, j ≠ 0 → ∀ f ∈ 𝒜 j, x f = 0

variable {K : Type} [Field K] [Algebra O K]

def OnS (I : Ideal A) (ξ : A →ₐ[O] K) : Prop := ∀ f ∈ I, ξ f = 0

def NegZero (ξ : A →ₐ[O] K) : Prop := ∀ j < 0, ∀ f ∈ 𝒜 j, ξ f = 0

def PosZero (ξ : A →ₐ[O] K) : Prop := ∀ j > 0, ∀ f ∈ 𝒜 j, ξ f = 0

def TwoSigned (ξ : A →ₐ[O] K) : Prop := ¬ NegZero 𝒜 ξ ∧ ¬ PosZero 𝒜 ξ

def Same0 (ξ ξ' : A →ₐ[O] K) : Prop := ∀ b ∈ 𝒜 0, ξ b = ξ' b

def SameOrbit (ξ ξ' : A →ₐ[O] K) : Prop := ∃ t : Kˣ, ξ' = act 𝒜 (tz t) ξ

def M2 (I : Ideal A) : Prop := ((𝒜 0).map (Ideal.Quotient.mkₐ O I).toLinearMap).FG

variable (K) in

def M3 (x : A →ₐ[O] O) (I : Ideal A) : Prop :=
  ∀ x₁ : A →ₐ[O] K, OnS I x₁ → NegZero 𝒜 x₁ → PosZero 𝒜 x₁ → x₁ ≠ (Algebra.ofId O K).comp x →
    (¬ ∃ ξ : A →ₐ[O] K, OnS I ξ ∧ NegZero 𝒜 ξ ∧ ¬ PosZero 𝒜 ξ ∧ Same0 𝒜 ξ x₁) ∨
    (¬ ∃ ξ : A →ₐ[O] K, OnS I ξ ∧ PosZero 𝒜 ξ ∧ ¬ NegZero 𝒜 ξ ∧ Same0 𝒜 ξ x₁)

variable (K) in

def M4 (I : Ideal A) : Prop :=
  ∀ ξ : A →ₐ[O] K, OnS I ξ → TwoSigned 𝒜 ξ → ∀ D ∈ PtDer ξ K, ∀ D' ∈ PtDer ξ K, (∀ f ∈ I, D f = 0) →
    (∀ f ∈ I, D' f = 0) → ∃ c c' : K, (c ≠ 0 ∨ c' ≠ 0) ∧ c • D + c' • D' = 0

variable (K) in

def OrbitVanishingLocal (I : Ideal A) : Prop :=
  ∀ ξ : A →ₐ[O] K, OnS I ξ → TwoSigned 𝒜 ξ → ∀ f : TensorProduct O K A,
    (∀ t : Kˣ, Algebra.TensorProduct.lift (AlgHom.id O K) (act 𝒜 (tz t) ξ) (fun _ _ => Commute.all _ _) f = 0) →
    ∃ g : TensorProduct O K A, Algebra.TensorProduct.lift (AlgHom.id O K) ξ (fun _ _ => Commute.all _ _) g ≠ 0 ∧
      g * f ∈ I.map (Algebra.TensorProduct.includeRight : A →ₐ[O] TensorProduct O K A)

variable (K) in

def M5 (x : A →ₐ[O] O) (I : Ideal A) (a : A) : Prop :=
  a ∈ 𝒜 0 ∧ x a = 0 ∧ ∀ ξ : A →ₐ[O] K, OnS I ξ → TwoSigned 𝒜 ξ → ξ a ≠ 0

def Covers (I : Ideal A) (T : Finset (A →ₐ[O] K)) : Prop :=
  (∀ ξ ∈ T, OnS I ξ ∧ TwoSigned 𝒜 ξ) ∧ ∀ ξ, OnS I ξ → TwoSigned 𝒜 ξ → ∃ ξ' ∈ T, SameOrbit 𝒜 ξ' ξ

end Data

structure IsChart {O A X τ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [AddCommGroup X]
    (𝒜 : X → Submodule O A) (x : A →ₐ[O] O) (wt : τ → X) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) : Prop where
  graded : ∀ j, ∀ f ∈ 𝒜 j, φ f ∈ wtPart (FractionRing O) wt j
  const : ∀ f, constantCoeff (φ f) = algebraMap O (FractionRing O) (x f)
  onto : ∀ i, ∃ f : A, coeff (Finsupp.single i 1) (φ f) ≠ 0 ∧ ∀ i', i' ≠ i → coeff (Finsupp.single i' 1) (φ f) = 0
  inj : ∀ f, x f = 0 → (∀ i, coeff (Finsupp.single i 1) (φ f) = 0) → f ∈ satSq x

def SmoothPt {O A X : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [AddCommGroup X]
    (𝒜 : X → Submodule O A) (x : A →ₐ[O] O) (n : X → ℕ) : Prop :=
  ∃ (τ : Type) (_ : Fintype τ) (wt : τ → X) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)),
    IsChart 𝒜 x wt φ ∧ ∀ j, Nat.card {i // wt i = j} = n j

structure Eqns {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) (x : A →ₐ[O] O)
    (r s r' s' m : ℕ) where
  F : Fin (r + 1) → A
  G : Fin s → A
  E : Fin r' → A
  E' : Fin s' → A
  Z : Fin m → A
  hF : ∀ i, F i ∈ 𝒜 (-1)
  hG : ∀ i, G i ∈ 𝒜 (-2)
  hE : ∀ i, E i ∈ 𝒜 1
  hE' : ∀ i, E' i ∈ 𝒜 2
  hZ : ∀ i, Z i ∈ 𝒜 0 ∧ x (Z i) = 0

def Eqns.ideal {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {𝒜 : ℤ → Submodule O A} {x : A →ₐ[O] O}
    {r s r' s' m : ℕ} (Q : Eqns 𝒜 x r s r' s' m) : Ideal A :=
  Ideal.span (Set.range Q.F ∪ Set.range Q.G ∪ Set.range Q.E ∪ Set.range Q.E' ∪ Set.range Q.Z)

def mDims (r s r' s' m : ℕ) (j : ℤ) : ℕ :=
  if j = -1 then r else if j = -2 then s else if j = 1 then r' + 1 else if j = 2 then s' + 1 else
    if j = 0 then m else 0

def M1 {O A : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] {𝒜 : ℤ → Submodule O A} {x : A →ₐ[O] O}
    {r s r' s' m : ℕ} (Q : Eqns 𝒜 x r s r' s' m) : Prop :=
  1 ≤ r ∧ SmoothPt 𝒜 x (mDims r s r' s' m) ∧ SpansCot x 𝒜 (-1) Q.F ∧ SpansCot x 𝒜 (-2) Q.G ∧ SpansCot x 𝒜 0 Q.Z

def LemmaM : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ), IsNVal O K v →
  ∀ (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (x : A →ₐ[O] O), IsWRing 𝒜 x →
  ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m) (a : A),
    M1 Q → M2 𝒜 Q.ideal → M3 𝒜 K x Q.ideal → M4 𝒜 K Q.ideal → M5 𝒜 K x Q.ideal a →
    (∃ T : Finset (A →ₐ[O] K), Covers 𝒜 Q.ideal T) ∧ cotLen x 𝒜 (-1) Q.F ≠ ⊤ ∧
    ∀ T : Finset (A →ₐ[O] K), Covers 𝒜 Q.ideal T → ((cotLen x 𝒜 (-1) Q.F).toNat : ℝ) ≤ 2 * ∑ ξ ∈ T, v (ξ a)

def LemmaM' : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    (A X : Type) [CommRing A] [Algebra O A] [AddCommGroup X] [DecidableEq X] (𝒜 : X → Submodule O A) [GradedAlgebra 𝒜]
    (x : A →ₐ[O] O) (j : X), (∀ f ∈ 𝒜 j, x f = 0) →
  ∀ (ι : Type) (F : ι → A), (∀ i, F i ∈ 𝒜 j) →
  ∀ (c : O), c ≠ 0 → ∀ (M : Type) [AddCommGroup M] [Module O M] (D : M →+ (A →ₗ[O] O ⧸ Ideal.span {c})),
    Function.Injective D → (∀ μ i, D μ (F i) = 0) →
    (∀ μ, ∃ D' ∈ PtDer x O, HasWt 𝒜 j D' ∧ ∀ f, D μ f = Ideal.Quotient.mk _ (D' f)) →
    Module.length O M ≤ cotLen x 𝒜 j F

end UpperTheory.V.Alg
