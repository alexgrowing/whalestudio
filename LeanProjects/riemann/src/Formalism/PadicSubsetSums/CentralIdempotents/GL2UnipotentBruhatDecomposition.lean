import Formalism.PadicSubsetSums.CentralIdempotents.ArchimedeanComponents

noncomputable section

namespace Formalism.IrreducibleCountingLemmas.WindowSums

open Polynomial TensorProduct

def OrdTwoAdic : Prop :=
  ∀ (k a : ℕ) (y y' : ℤ), 2 ≤ a → a ≤ k → Odd y' → y = 1 + 2 ^ a * y' →
    orderOf ((y : ZMod (2 ^ k))) = 2 ^ (k - a)

def RecipSigns : Prop :=
  ∀ (q d : ℕ) [Fact q.Prime] [Fact d.Prime], q % 4 = 3 → d % 4 = 3 → q ≠ d →
    legendreSym q (-(d : ℤ)) = 1 → legendreSym q (d : ℤ) = -1 ∧ legendreSym d (q : ℤ) = 1

def DecompDFrob : Prop :=
  ∀ (H : Type) [AddCommGroup H] (h : H),
    AddSubgroup.closure ({((0, 1), 0), ((1, 0), h)} : Set ((ZMod 2 × ZMod 2) × H)) =
      AddSubgroup.closure ({((0, 1), 0), ((1, 1), h)} : Set ((ZMod 2 × ZMod 2) × H))

def DecompQFull : Prop :=
  ∀ (H : Type) [AddCommGroup H] (h : H), AddSubgroup.closure ({h} : Set H) = ⊤ →
    ∀ g : (ZMod 2 × ZMod 2) × H,
      g ∈ AddSubgroup.closure ({((1, 0), 0), ((0, 0), h)} : Set ((ZMod 2 × ZMod 2) × H)) ↔
        g.1.2 = 0

def SplitUnitary : Prop :=
  ∀ (k V₁ V₂ : Type) [Field k] [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
    [FiniteDimensional k V₁] [FiniteDimensional k V₂] (B : V₁ →ₗ[k] V₂ →ₗ[k] k),
    Function.Injective B → Function.Injective B.flip →
    ∀ g₁ : V₁ ≃ₗ[k] V₁, ∃! g₂ : V₂ ≃ₗ[k] V₂, ∀ x y, B (g₁ x) (g₂ y) = B x y

def InvRescale : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (s : ℕ) (ω : O), IsPrimitiveRoot ω s → 1 ≤ s →
    ∀ f : PowerSeries O, PowerSeries.rescale ω f = f ↔ ∀ k, ¬ s ∣ k → PowerSeries.coeff k f = 0

def brk (l : ℕ) [Fact l.Prime] (ω : ℤ_[l]) : PowerSeries ℤ_[l] :=
  PowerSeries.binomialSeries ℤ_[l] ω - 1

def piP (l : ℕ) [Fact l.Prime] (s : ℕ) : PowerSeries ℤ_[l] :=
  ∏ ω ∈ Polynomial.nthRootsFinset s (1 : ℤ_[l]), brk l ω

def DictConcrete : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e s : ℕ), e * s = l - 1 → ∀ (u : ℤ_[l]) (q : PowerSeries ℤ_[l]),
    PowerSeries.X * q = brk l (l : ℤ_[l]) →
    (Polynomial.nthRootsFinset s (1 : ℤ_[l])).card = s ∧
    (∃ ε : (PowerSeries ℤ_[l])ˣ, piP l s = (ε : PowerSeries ℤ_[l]) * PowerSeries.X ^ s) ∧
    (∃ ε : (PowerSeries ℤ_[l])ˣ,
      PowerSeries.subst (brk l (l : ℤ_[l])) (piP l s) = (ε : PowerSeries ℤ_[l]) * piP l s * q ^ s) ∧
    (piP l s) ^ 2 ∣ PowerSeries.subst (brk l u) (piP l s) - PowerSeries.C (u ^ s) * piP l s

def DictUnitInv : Prop :=
  ∀ (A₁ G : Type) [CommRing A₁] [Group G] [Fintype G] [MulSemiringAction G A₁]
    (p E : A₁) (φ : A₁ →+* A₁) (ε : A₁ˣ) (s : ℕ),
    (∀ x y : A₁, p * x = p * y → x = y) → (∀ x y : A₁, E * x = E * y → x = y) →
    (∀ g : G, ∃ v : A₁ˣ, g • p = p * v) →
    (∀ (g : G) (x : A₁), φ (g • x) = g • φ x) → (∀ g : G, g • E = E) →
    φ (∏ g : G, g • p) = ε * (∏ g : G, g • p) * E ^ s →
    (∀ g : G, g • (ε : A₁) = ε) ∧ (∀ g : G, g • ((ε⁻¹ : A₁ˣ) : A₁) = ((ε⁻¹ : A₁ˣ) : A₁))

def EisensteinDisc2 : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (l a b ϖ ϖ' : O),
    l ∈ IsLocalRing.maximalIdeal O → IsUnit (2 : O) → IsUnit b →
    ϖ + ϖ' = -(l * a) → ϖ * ϖ' = l * b →
    ∃ ε : O, IsUnit ε ∧ (ϖ - ϖ') ^ 2 = l * ε

def NormSqrt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l % 4 = 3 → 3 < l → ∀ (F : Type) [Field F] (ζ : F),
    IsPrimitiveRoot ζ l →
    (∏ a ∈ (Finset.univ.filter fun a : (ZMod l)ˣ => IsSquare a), (ζ ^ (a : ZMod l).val - 1)) ^ 2 =
      -(l : F)

def EigenAverage : Prop :=
  ∀ (R M G : Type) [CommRing R] [AddCommGroup M] [Module R M] [Group G] [Fintype G]
    (ρ : G →* (M →ₗ[R] M)) (χ : G →* Rˣ) (x : M) (h : G),
    ρ h (∑ g : G, (((χ g)⁻¹ : Rˣ) : R) • ρ g x) = ((χ h : Rˣ) : R) • ∑ g : G, (((χ g)⁻¹ : Rˣ) : R) • ρ g x

def InvariantBasis : Prop :=
  ∀ (A₁ N G : Type) [CommRing A₁] [IsLocalRing A₁] [AddCommGroup N] [Module A₁ N] [Group G]
    [Fintype G] [MulSemiringAction G A₁] [DistribMulAction G N] (p : A₁) (d : ℕ)
    (b : Module.Basis (Fin d) A₁ N),
    (∀ (g : G) (a : A₁) (n : N), g • (a • n) = (g • a) • (g • n)) →
    p ∈ IsLocalRing.maximalIdeal A₁ → IsUnit ((Fintype.card G : ℕ) : A₁) →
    (∀ (g : G) (n : N), ∃ n', g • n - n = p • n') →
    ∃ b' : Module.Basis (Fin d) A₁ N, (∀ (g : G) (j : Fin d), g • b' j = b' j) ∧
      (∀ j, ∃ n', b' j - b j = p • n') ∧
      ∀ n : N, (∀ g : G, g • n = n) ↔ ∀ (j : Fin d) (g : G), g • (b'.repr n j) = b'.repr n j

def InvariantsExact : Prop :=
  ∀ (R M M' G : Type) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [Group G] [Fintype G] (ρ : G →* (M →ₗ[R] M)) (ρ' : G →* (M' →ₗ[R] M')) (f : M →ₗ[R] M'),
    IsUnit ((Fintype.card G : ℕ) : R) → (∀ g x, f (ρ g x) = ρ' g (f x)) → Function.Surjective f →
    ∀ y, (∀ g, ρ' g y = y) → ∃ x, (∀ g, ρ g x = x) ∧ f x = y

def GammaRoot : Prop :=
  ∀ (A ι : Type) [CommRing A] [Fintype ι] [DecidableEq ι] (γ : A →+* A) (p g₁ : A) (ϖ : ι → A),
    (∀ τ, γ (ϖ τ) = ϖ τ) → γ p - p = p * (∏ τ, (p - ϖ τ)) * g₁ → p ∈ (⊥ : Ideal A).jacobson →
    ∀ τ, ∃ ε : Aˣ, γ (p - ϖ τ) = (p - ϖ τ) * ε ∧
      (ε : A) = 1 + g₁ * p * ∏ τ' ∈ Finset.univ.erase τ, (p - ϖ τ')

def GradedAction : Prop :=
  ∀ (A X : Type) [CommRing A] [AddCommGroup X] [Module A X] (γA : A →+* A) (γ : X →+ X)
    (p w c : A), (∀ (a : A) (x : X), γ (a • x) = γA a • γ x) → γA p = p * w → p ∣ w - c →
    (∀ x : X, ∃ x', γ x - x = p • x') →
    ∀ (y : ℕ) (x : X), ∃ x', γ (p ^ y • x) - c ^ y • (p ^ y • x) = p ^ (y + 1) • x'

def GradedDual : Prop :=
  ∀ (A X : Type) [CommRing A] [AddCommGroup X] [Module A X] (γA : A →+* A) (γ : X ≃+ X)
    (p w : A), (∀ (a : A) (x : X), γ (a • x) = γA a • γ x) → γA p = p * w →
    (∀ a : A, p ∣ γA a - a) → (∀ x : X, ∃ x', γ x - x = p • x') →
    ∀ (f : X →ₗ[A] A) (x : X), p ∣ γA (f (γ.symm x)) - f x

def SatCoprime : Prop :=
  ∀ (A K : Type) [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] [Field K] [Algebra A K]
    [IsFractionRing A K] (g₁ g₂ : A) (f : K), g₁ ≠ 0 → g₂ ≠ 0 → IsRelPrime g₁ g₂ →
    (∃ a : A, algebraMap A K a = algebraMap A K g₁ * f) →
    (∃ b : A, algebraMap A K b = algebraMap A K g₂ * f) → ∃ c : A, algebraMap A K c = f

def SatCoprimeDvd : Prop :=
  ∀ (A K : Type) [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] [Field K] [Algebra A K]
    [IsFractionRing A K] (g₁ g₂ p : A) (f : K), g₁ ≠ 0 → g₂ ≠ 0 → IsRelPrime g₁ g₂ →
    IsRelPrime p g₂ → (∃ a : A, algebraMap A K a = algebraMap A K g₁ * f) →
    (∃ b : A, algebraMap A K (p * b) = algebraMap A K g₂ * f) →
    ∃ c : A, algebraMap A K (p * c) = f

def HerrClass : Prop :=
  ∀ (D : Type) [AddCommGroup D] (φ γ : D →+ D) (B : AddSubgroup D),
    (∀ x, φ (γ x) = γ (φ x)) → (∀ x ∈ B, φ x ∈ B) → (∀ x ∈ B, γ x ∈ B) →
    (∀ b ∈ B, ∃! x, x ∈ B ∧ φ x - x = b) →
    (∀ w, γ w - w ∈ B → ∃! z, z ∈ B ∧ φ z - z = γ w - w) ∧
    (∀ m, γ m - m ∈ B → γ (φ m - m) - (φ m - m) ∈ B ∧
      ∀ z ∈ B, φ z - z = γ (φ m - m) - (φ m - m) → z = γ m - m) ∧
    (∀ w ∈ B, ∀ z ∈ B, φ z - z = γ w - w → ∃ x ∈ B, φ x - x = w ∧ γ x - x = z) ∧
    (∀ w, γ w - w ∈ B → γ (φ w) - φ w ∈ B ∧
      ∀ z ∈ B, ∀ z' ∈ B, φ z - z = γ w - w → φ z' - z' = γ (φ w) - φ w → z' - z = γ w - w)

def InvariantLift : Prop :=
  ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (γ : Module.End R V)
    (B₁ BM : Submodule R V) (d : R), BM ≤ B₁ →
    (∀ x ∈ B₁, γ x - x ∈ BM → x ∈ BM) → (∀ z ∈ B₁, ∃ k ∈ B₁, d • z - (γ k - k) ∈ BM) →
    (∀ w : V, γ w - w ∈ B₁ → ∃ w', γ w' - w' ∈ BM ∧ w' - d • w ∈ B₁) ∧
    (∀ w' w'' : V, γ w' - w' ∈ BM → γ w'' - w'' ∈ BM → w' - w'' ∈ B₁ → w' - w'' ∈ BM)

def InvTruncConst : Prop :=
  ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (γ ϖ : Module.End R V) (c : ℕ → R),
    Function.Injective ϖ →
    (∀ (i : ℕ) (x : V), ∃ y, γ ((ϖ ^ i) x) - c i • (ϖ ^ i) x = (ϖ ^ (i + 1)) y) →
    (∀ (i : ℕ), 1 ≤ i → ∀ x y : V, (c i - 1) • x = ϖ y → ∃ x', x = ϖ x') →
    ∀ (k : ℕ) (x₀ w r : V), γ x₀ = x₀ → γ (x₀ + ϖ w) - (x₀ + ϖ w) = (ϖ ^ k) r →
      ∃ r', ϖ w = (ϖ ^ k) r'

def MatrixScalarComm : Prop :=
  ∀ (R n : Type) [CommRing R] [Fintype n] [DecidableEq n] (α β : Matrix n n R) (d : R),
    (∀ x : R, d * x = 0 → x = 0) → β * α = d • (1 : Matrix n n R) → α * β = d • (1 : Matrix n n R)

def FrameMatrix : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (γA : A →ₐ[O] A) (p w : A) (c : O)
    (d M : ℕ) (G : Matrix (Fin d) (Fin d) A), 1 ≤ M →
    (∀ a b : A, p * a = p * b → a = b) → γA p = p * w → p ∣ w - algebraMap O A c →
    (∀ a : A, p ∣ γA a - a) →
    (∀ y : ℕ, 1 ≤ y → ∀ a b : A, (c ^ y - 1) • a = p * b → p ∣ a) →
    IsUnit G.det → (∀ i j, p ∣ (G - 1) i j) →
    ∃ H H' : Matrix (Fin d) (Fin d) A,
      (∀ i j, p ^ M ∣ (G * H.map γA - H) i j) ∧
      (∀ i j, p ∣ (H - (∏ y ∈ Finset.Icc 1 (M - 1), (c ^ y - 1)) •
        (1 : Matrix (Fin d) (Fin d) A)) i j) ∧
      (∀ i j, p ^ M ∣ (H' * G - H'.map γA) i j) ∧
      (∀ i j, p ∣ (H' - (∏ y ∈ Finset.Icc 1 (M - 1), (c ^ y - 1)) •
        (1 : Matrix (Fin d) (Fin d) A)) i j) ∧
      (∀ i j, p ^ M ∣ (H' * H - ((∏ y ∈ Finset.Icc 1 (M - 1), (c ^ y - 1)) ^ 2) •
        (1 : Matrix (Fin d) (Fin d) A)) i j) ∧
      (∀ i j, p ^ M ∣ (H * H' - ((∏ y ∈ Finset.Icc 1 (M - 1), (c ^ y - 1)) ^ 2) •
        (1 : Matrix (Fin d) (Fin d) A)) i j)

def FrameFunctorial : Prop :=
  ∀ (A X₁ X₂ Y₁ Y₂ : Type) [CommRing A] [AddCommGroup X₁] [Module A X₁] [AddCommGroup X₂]
    [Module A X₂] [AddCommGroup Y₁] [Module A Y₁] [AddCommGroup Y₂] [Module A Y₂]
    (α₁ : X₁ →ₗ[A] Y₁) (β₁ : Y₁ →ₗ[A] X₁) (α₂ : X₂ →ₗ[A] Y₂) (β₂ : Y₂ →ₗ[A] X₂)
    (pX : X₁ →ₗ[A] X₂) (pY : Y₁ →ₗ[A] Y₂) (d : A),
    (∀ y, α₁ (β₁ y) = d • y) → (∀ x, β₂ (α₂ x) = d • x) → (∀ x, α₂ (pX x) = pY (α₁ x)) →
    (∀ x : X₂, d • x = 0 → x = 0) → ∀ y, β₂ (pY y) = pX (β₁ y)

def ModelTorsionFree : Prop :=
  ∀ (A F : Type) [CommRing A] [AddCommGroup F] [Module A F] (ϖ p : A) (NL : Submodule A F),
    (∀ x : F, ϖ • x = 0 → x = 0) → (∀ x y : F, p • y = ϖ • x → ∃ y', y = ϖ • y') →
    (∀ y : F, ϖ • y ∈ NL → y ∈ NL) →
    ∀ x : F, (∃ y ∈ NL, ϖ • x = p • y) → ∃ y ∈ NL, x = p • y

def SplitCocycle : Prop :=
  ∀ (D : Type) [AddCommGroup D] (φ γ : D →+ D) (B : AddSubgroup D),
    (∀ x, φ (γ x) = γ (φ x)) → (∀ x ∈ B, φ x ∈ B) → (∀ x ∈ B, φ x - x = 0 → x = 0) →
    ∀ xb, γ xb - xb ∈ B →
      γ (φ xb) - φ xb ∈ B ∧ γ (φ xb - xb) - (φ xb - xb) ∈ B ∧
      ∀ z ∈ B, φ z - z = γ (φ xb - xb) - (φ xb - xb) →
        φ (φ xb) - φ xb - (φ xb - xb) = φ (φ xb - xb) - (φ xb - xb) ∧
        γ (φ xb) - φ xb - z = γ (φ xb - xb) - (φ xb - xb)

def TorsionGen : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (r : ℕ)
    (Z : Submodule O (Fin r → (K ⧸ LinearMap.range (Algebra.linearMap O K))))
    (Q : Type) [AddCommGroup Q] [Module O Q] [Module.Finite O Q] (f : Z →ₗ[O] Q),
    Function.Surjective f → ∃ s : Finset Q, s.card ≤ r ∧ Submodule.span O (s : Set Q) = ⊤

def DecompLattice : Prop :=
  ∀ (O L ι : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [AddCommGroup L] [Module O L]
    [Module.Free O L] [Module.Finite O L] (UP DOWN : Finset ι) (Cc Ff : ι → Submodule O L) (m : ℕ),
    (∀ τ ∈ UP, (∀ (a : O) (x : L), a ≠ 0 → a • x ∈ Cc τ → x ∈ Cc τ) ∧
      Module.finrank O (L ⧸ Cc τ) ≤ m) →
    (∀ τ ∈ DOWN, Module.finrank O (Ff τ) ≤ m) →
    ∃ L'' Lr : Submodule O L, IsCompl L'' Lr ∧ Module.finrank O Lr ≤ (UP.card + DOWN.card) * m ∧
      (∀ τ ∈ UP, L'' ≤ Cc τ) ∧ ∀ τ ∈ DOWN, Ff τ ≤ Lr

def WindowKummer : Prop :=
  ∀ (l j S : ℕ), l.Prime →
    ∑ i ∈ Finset.Icc (j + 1) (j + S), padicValNat l i =
      padicValNat l S.factorial + padicValNat l ((j + S).choose S) ∧
    padicValNat l ((j + S).choose S) ≤ Nat.log l (j + S)

def KappaBoundK : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ u : ℤ_[l]ˣ, ((u : ℤ_[l]) - 1).valuation = 1 →
    ∀ (e S h' : ℕ) (b : Fin e → ℕ) (up : Fin e → Bool), (∀ τ, 1 ≤ b τ ∧ b τ + S ≤ h') →
      (∏ i ∈ Finset.univ.biUnion (fun τ : Fin e =>
            if up τ then Finset.Ico (-(b τ : ℤ) - S) (-(b τ : ℤ))
            else Finset.Ico (b τ : ℤ) ((b τ : ℤ) + S)),
          (1 - ((u ^ i : ℤ_[l]ˣ) : ℤ_[l]))).valuation ≤
        e * (S + padicValNat l S.factorial + Nat.log l h')

def WindowKill : Prop :=
  ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (γ : Module.End R V) (c : ℤ → R)
    (Om I : Finset ℤ) (x : ℤ → V), (∀ i ∈ I, γ (x i) = c i • x i) →
    aeval γ (∏ j ∈ Om, (X - C (c j))) (∑ i ∈ I, x i) =
      ∑ i ∈ I \ Om, (∏ j ∈ Om, (c i - c j)) • x i

def InvariantsDegreeZero : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (γ : Module.End K V) (c : ℤ → K)
    (I : Finset ℤ) (x : ℤ → V), Set.InjOn c (insert 0 (I : Set ℤ)) → c 0 = 1 →
    (∀ i ∈ I, γ (x i) = c i • x i) → γ (∑ i ∈ I, x i) = ∑ i ∈ I, x i → ∀ i ∈ I, i ≠ 0 → x i = 0

def MixedB : Prop :=
  ∀ (O L₁ L₂ : Type) [CommRing O] [AddCommGroup L₁] [Module O L₁] [AddCommGroup L₂] [Module O L₂]
    (p : L₁ →ₗ[O] L₂) (Fil : ℤ → Submodule O L₁) (g : ℕ → L₁) (δ d : O) (ell : L₂)
    (bU B S η h' : ℕ), Antitone Fil → (∀ k : ℕ, g k ∈ Fil ((bU : ℤ) + S - k)) →
    (∀ k < 3 * h', p (g k) = (d * ((X ^ S * (X - C δ) ^ (B + η) : O[X]).coeff k)) • ell) →
    B + 2 * η < bU → bU + S ≤ h' → ∃ ell' ∈ Fil ((η : ℤ) + 1), p ell' = d • ell

def YcBound : Prop :=
  ∀ (l bU B η h' : ℕ), l.Prime → 1 ≤ B → B ≤ bU → bU ≤ B + 2 * η → bU ≤ h' →
    (bU - B + 2) / 2 + Nat.log l bU ≤ ⌈(η : ℝ) + 1 / 2 + Real.logb l h'⌉₊

def AssemblyU : Prop :=
  ∀ (O I₁ I₂ IL : Type) [CommRing O] [AddCommGroup I₁] [Module O I₁] [AddCommGroup I₂] [Module O I₂]
    [AddCommGroup IL] [Module O IL] (p : I₁ →ₗ[O] I₂) (α : IL →ₗ[O] I₂) (β : I₂ →ₗ[O] IL)
    (Rr : Submodule O IL) (l P1 : O) (ε : Oˣ) (σ κ κ' y₁ : ℕ),
    (∀ w, α (β w) = l ^ (2 * σ) • w) → P1 = ε * l ^ κ' → κ' ≤ κ →
    (∀ w : I₂, ∃ (k : ℕ) (a : Fin k → IL) (r : IL), r ∈ Rr ∧ P1 • β w = ∑ j, a j + r ∧
      ∀ j, ∃ w₁ : I₁, l ^ y₁ • α (a j) = p w₁) →
    ∀ w : I₂, ∃ (w₁ : I₁) (r : IL), r ∈ Rr ∧ l ^ (2 * σ + κ + y₁) • w = p w₁ + α r

def AssemblyA : Prop :=
  ∀ (O : Type) [CommRing O] (l : ℕ) (G₁ G₂ : Type) [AddCommGroup G₁] [Module O G₁]
    [AddCommGroup G₂] [Module O G₂] (p : G₁ →ₗ[O] G₂) (ι : Type) [Fintype ι] (I₁ I₂ : ι → Type)
    [∀ c, AddCommGroup (I₁ c)] [∀ c, Module O (I₁ c)] [∀ c, AddCommGroup (I₂ c)]
    [∀ c, Module O (I₂ c)] (pI : ∀ c, I₁ c →ₗ[O] I₂ c) (rh₁ : ∀ c, I₁ c →ₗ[O] G₁)
    (rh₂ : ∀ c, I₂ c →ₗ[O] G₂) (Rr : ∀ c, Submodule O (I₂ c)) (a y₂ e' g g₀ : ℕ),
    (∀ c x, rh₂ c (pI c x) = p (rh₁ c x)) →
    (∀ κ : G₂, ∃ w : ∀ c, I₂ c, (l ^ a : ℕ) • κ = ∑ c, rh₂ c (w c)) →
    (∀ c (w : I₂ c), ∃ (w₁ : I₁ c) (r : I₂ c), r ∈ Rr c ∧ (l ^ y₂ : ℕ) • w = pI c w₁ + r) →
    (∀ κ : G₂, ∃ κ₁ : G₁, (l ^ e' : ℕ) • κ = p κ₁) →
    (∃ s : Finset G₂, s.card ≤ g ∧ Submodule.span O (s : Set G₂) = ⊤) →
    (∀ c, ∃ s : Finset (I₂ c), s.card ≤ g₀ ∧ Submodule.span O (s : Set (I₂ c)) = Rr c) →
    Module.length O (G₂ ⧸ LinearMap.range p) ≤
      ((g : ℕ∞) * ((a + y₂ : ℕ) : ℕ∞) + ((Fintype.card ι * g₀ : ℕ) : ℕ∞) * (e' : ℕ∞)) *
        Module.length O (O ⧸ Ideal.span {(l : O)})

def SizesA : Prop :=
  ∀ (l e s h' S η M σ a ρ κ yc : ℕ), l.Prime → l ≠ 2 → e * s = l - 1 → 1 ≤ h' →
    M = ⌈(4 * h' : ℝ) / s⌉₊ → σ = M - 1 + padicValNat l (M - 1).factorial →
    a = ⌈(2 * e * h' : ℝ) / ((l : ℝ) - 1)⌉₊ → ρ = 2 * a - 1 + padicValNat l (2 * a - 1).factorial →
    κ = e * (S + padicValNat l S.factorial + Nat.log l h') →
    yc = ⌈(η : ℝ) + 1 / 2 + Real.logb l h'⌉₊ →
    1 ≤ M ∧ 4 * h' ≤ s * M ∧ h' + 1 ≤ s * M ∧ 2 * h' ≤ s * a ∧
    (σ : ℝ) ≤ 9 * ((e : ℝ) * h') / l ∧ (ρ : ℝ) ≤ 9 * ((e : ℝ) * h') / l + 3 / 2 ∧
    (κ : ℝ) ≤ (e : ℝ) * (3 * S / 2 + Real.logb l h') ∧
    ((2 * ρ + 4 * σ + κ + max (2 * σ) yc : ℕ) : ℝ) ≤
      72 * ((e : ℝ) * h') / l + 2 * e * S + 2 * e * Real.logb l h' + η + 5

def CompareA : Prop :=
  ∀ (l e h h' S η : ℕ), 3 ≤ l → 1 ≤ e → 1 ≤ h → 1 ≤ h' → h' ≤ h + S →
    72 * ((e : ℝ) * h') / l + 2 * e * S + 2 * e * Real.logb l h' + η + 5 ≤
      80 * ((e : ℝ) * h / l + (e : ℝ) * S + (e : ℝ) * Real.logb l h + 1 + η)

def BracketAPrime : Prop :=
  ∀ (l e h h' S η : ℕ) (c ρ σ κ y : ℝ), 3 ≤ l → 1 ≤ e → 1 ≤ h → 1 ≤ h' → h' ≤ h + S → 0 ≤ c →
    ρ ≤ 9 * ((e * h' : ℕ) : ℝ) / l + 3 → σ ≤ 9 * ((e * h' : ℕ) : ℝ) / l + 3 →
    κ ≤ (e : ℝ) * ((S : ℝ) + (S : ℝ) / ((l : ℝ) - 1) + Real.logb l (h' : ℝ)) →
    y ≤ c * (ρ + σ) + κ + η + 1 + Real.logb l h' →
    y ≤ (18 * c + 4) *
      (((e * h : ℕ) : ℝ) / l + (e : ℝ) * S + (e : ℝ) * Real.logb l h + 1 + η)

def LiftExpSharp : Prop :=
  ∀ (l h : ℕ) (J : Finset ℤ), l.Prime → l ≠ 2 → J ⊆ Finset.Icc (-(h : ℤ)) (2 * h) →
    (0 : ℤ) ∉ J →
    ((2 * (2 * (2 * h) + padicValNat l (2 * (2 * h)).factorial) +
      ((∑ j ∈ J, (1 + padicValInt l j)) + h + padicValNat l h.factorial) : ℕ) : ℝ) ≤
      12 * (h : ℝ) * l / ((l : ℝ) - 1)

def LiftDescend : Prop :=
  ∀ (O G₁ G₂ G₁' G₂' : Type) [CommRing O] [AddCommGroup G₁] [Module O G₁] [AddCommGroup G₂]
    [Module O G₂] [AddCommGroup G₁'] [Module O G₁'] [AddCommGroup G₂'] [Module O G₂']
    (p : G₁ →ₗ[O] G₂) (p' : G₁' →ₗ[O] G₂') (res : G₂ →ₗ[O] G₂') (cor₁ : G₁' →ₗ[O] G₁)
    (cor₂ : G₂' →ₗ[O] G₂) (s c : O), IsUnit s → (∀ x, cor₂ (res x) = s • x) →
    (∀ x, p (cor₁ x) = cor₂ (p' x)) → (∀ y : G₂', ∃ x, p' x = c • y) →
    ∀ κ : G₂, ∃ κ₁ : G₁, p κ₁ = c • κ

def DualTwistJumps : Prop :=
  ∀ (s S η t u : ℤ), 1 ≤ t → 0 ≤ η →
    (s ≤ u ∧ u ≤ s + S → -(s + 1) - S ≤ -u - 1 ∧ -u - 1 ≤ -(s + 1)) ∧
    (-(s + S) ≤ u ∧ u ≤ -s → s - 1 ≤ -u - 1 ∧ -u - 1 ≤ (s - 1) + S) ∧
    (2 * |u| ≤ 2 * η + (t - 1) → |-u - 1| ≤ η + t + 1) ∧
    (0 ≤ u ∧ u ≤ t - 1 → -t ≤ -u - 1 ∧ -u - 1 ≤ -1 ∧ |-u - 1| ≤ η + t + 1)

def ParamsB : Prop :=
  ∀ (η t w'' x k S b : ℝ), 1 ≤ t → t ≤ η → t * η ≤ w'' / x → 5 < x → 1 ≤ k → 0 ≤ S →
    k * S ≤ w'' → w'' < b / 4 →
    (η + t + 1) + (t + 1) / 2 < w'' ∧ b + S + η + t + 2 ≤ 2 * b

def SumLenB : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ι → ℕ) (len : ι → ℝ) (f r m : ℕ)
    (CA CL b l S L η t h' e' lg : ℝ), (∀ w, 1 ≤ n w) → ∑ w, 2 * n w = 2 * f → 0 ≤ CA → 0 ≤ CL →
    0 < l → 0 ≤ S → 0 ≤ η → 1 ≤ t → 0 ≤ h' → h' ≤ 2 * b → 0 ≤ lg → lg ≤ 2 * L → e' ≤ CL * h' →
    (∀ w, len w ≤ CA * (2 * (n w : ℝ) + 1) * r * (2 * h' / l + 2 * S + 2 * lg + 1 + η + t + 1) +
      6 * (n w : ℝ) * m * e') →
    ∑ w, len w ≤ 12 * CA * f * r * (b / l + S + t + η + L) + 12 * CL * f * m * b

def DelVal : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ t : ℕ, t ≤ l →
    ∑ i ∈ Finset.Ioo 0 t, ((1 + (l : ℤ_[l])) ^ i - 1).valuation = t - 1

def LeastExponentLogBound : Prop :=
  ∀ (l n₀ H₀ : ℕ), 2 ≤ l → (1 ≤ n₀ → l ^ (n₀ - 1) * (l - 1) < H₀) →
    (n₀ : ℝ) ≤ 1 + Real.logb l H₀

def CBBound : Prop :=
  ∀ (f r t e : ℕ) (L m₀ cB : ℝ) (ri : ℕ → ℝ), 8 ≤ f → 1 ≤ r → 1 ≤ t → 2 ≤ L → m₀ ≤ 4 + L →
    e + 1 ≤ t → (∀ i, ri i ≤ (f : ℝ) * ((r : ℝ) + t) * (m₀ + L)) →
    cB = (m₀ - 1) + ∑ i ∈ Finset.range (e + 1), (2 + max 1 (ri i)) + e + 4 →
    cB ≤ 10 * t * f * ((r : ℝ) + t) * L ∧
    (t : ℝ) * (2 * f + 8) * cB ≤ 30 * (t : ℝ) ^ 2 * (f : ℝ) ^ 2 * ((r : ℝ) + t) * L

def PairCount : Prop :=
  ∀ (U : Multiset ℤ) (t : ℤ), 1 ≤ t → (∀ u ∈ U, u < 0 ∨ t - 1 < u) →
    (U.filter (· < 0)).card + ((U.map (fun u => t - 1 - u)).filter (· < 0)).card = U.card

def CorB : Prop :=
  ∀ (f r t k m : ℕ) (CA CL b l S L η w'' x : ℝ), 8 ≤ f → 1 ≤ m → r < t → (r : ℝ) < l →
    r ≤ 2 * k → k ≤ t → (t : ℝ) ≤ η → 0 ≤ S → (k : ℝ) * S ≤ w'' → (t : ℝ) * η ≤ w'' / x → 1 ≤ x →
    w'' < b / 4 → 0 ≤ L → L ≤ k → 61 ≤ t * k ^ 2 → η * (t : ℝ) ^ 3 * f * (k : ℝ) ^ 3 ≤ b →
    0 ≤ CA → 0 ≤ CL →
    (r : ℝ) * (b / l + S + t + η + L) ≤ 5 * b ∧
    30 * (t : ℝ) ^ 2 * (f : ℝ) ^ 2 * ((r : ℝ) + t) * L + 4 * ((r : ℝ) + t) * t ≤ f * b ∧
    12 * CA * f * r * (b / l + S + t + η + L) + 12 * CL * f * m * b +
      (30 * (t : ℝ) ^ 2 * (f : ℝ) ^ 2 * ((r : ℝ) + t) * L + 4 * ((r : ℝ) + t) * t) ≤
      (60 * CA + 12 * CL + 1) * f * m * b

def EisensteinSat : Prop :=
  ∀ (O : Type) [CommRing O] (l : O) (e : ℕ) (c : PowerSeries O),
    (∀ a b : O, l * a = l * b → a = b) →
    ∀ x y : PowerSeries O,
      PowerSeries.C l * x = (PowerSeries.X ^ e + PowerSeries.C l * c) * y →
      ∃ z, x = (PowerSeries.X ^ e + PowerSeries.C l * c) * z

def SatModule : Prop :=
  ∀ (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (E l : A),
    (∀ x y : M, E • x = E • y → x = y) →
    (∀ x y : M, l • x = E • y → ∃ z, x = E • z) →
    ∀ (j k : ℕ) (x y : M), l ^ k • x = E ^ j • y → ∃ z, x = E ^ j • z

def PhiEUnit : Prop :=
  ∀ (l : ℕ), l.Prime → ∀ (S : Type) [CommRing S] [IsAdicComplete (Ideal.span {(l : S)}) S]
    (E γ d : S), (l.factorial : S) * γ = E ^ l → γ ^ l = (l : S) * d →
    ∃ c : Sˣ, (E - (l : S)) ^ l + (l : S) = (l : S) * c

def FrobRigid : Prop :=
  ∀ (D V : Type) [AddCommGroup D] [AddCommGroup V] (F : ℕ → AddSubgroup V) (l : ℕ)
    (φ : V →+ V) (φD : D →+ D) (Δ : D →+ V), 2 ≤ l → Antitone F →
    (∀ x, (∀ k, x ∈ F k) → x = 0) → (∀ k, ∀ x ∈ F k, φ x ∈ F (l * k)) →
    Function.Surjective φD → (∀ d, Δ d ∈ F 1) → (∀ d, φ (Δ d) = Δ (φD d)) → ∀ d, Δ d = 0

def FrobFixedZero : Prop :=
  ∀ (O : Type) [CommRing O] (l : ℕ), 2 ≤ l → (∀ a : O, (l : O) * a = a → a = 0) →
    ∀ β : PowerSeries O, β = PowerSeries.C (l : O) * frob l β → β = 0

def FloorFactorialLower : Prop :=
  ∀ (l e i : ℕ), l.Prime → 1 ≤ e → 1 ≤ i →
    (i : ℝ) / ((e : ℝ) * ((l : ℝ) - 1)) - 1 - Real.logb l i ≤
      (padicValNat l (i / e).factorial : ℝ)

def FrobMatrixIntegral : Prop :=
  ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (l n : ℕ), 2 ≤ l →
    ∀ (Y Z B : Matrix (Fin n) (Fin n) F), (∀ i j, ‖Y i j‖ ≤ 1) → (∀ i j, ‖B i j‖ ≤ 1) →
    ((∀ i j, Z i j ^ l = (Y * Z + B) i j) ∨ (∀ i j, Z i j ^ l = (Z * Y + B) i j)) →
    ∀ i j, ‖Z i j‖ ≤ 1

def WittFrobIntegral : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] [IsUltrametricDist F] [CharP F l]
    [PerfectRing F l] (n : ℕ) (Y Z : Matrix (Fin n) (Fin n) (WittVector l F)),
    (∀ i j k, ‖(Y i j).coeff k‖ ≤ 1) →
    (Z.map (⇑(WittVector.frobenius : WittVector l F →+* WittVector l F)) = Y * Z ∨
      Z.map (⇑(WittVector.frobenius : WittVector l F →+* WittVector l F)) = Z * Y) →
    ∀ i j k, ‖(Z i j).coeff k‖ ≤ 1

def TwistedMatrixEquivariance : Prop :=
  ∀ (W : Type) [CommRing W] (φ : W →+* W) (ν ξ : W) (n b : ℕ) (Xm Z : Matrix (Fin n) (Fin n) W),
    φ ν = ξ * ν →
    (Z.map φ = Xm * Z → (ν ^ b • Z).map φ = (ξ ^ b • Xm) * (ν ^ b • Z)) ∧
    (Z.map φ = Z * Xm → (ν ^ b • Z).map φ = (ν ^ b • Z) * (ξ ^ b • Xm))

def TaylorMonomial : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra ℚ A] (μ : A) (n : ℕ),
    (1 + μ) ^ n = ∑ i ∈ Finset.range (n + 1),
      algebraMap ℚ A (1 / (i.factorial : ℚ)) * μ ^ i * (n.descFactorial i : A)

def PDMuExp : Prop :=
  (∀ (l : ℕ), 1 ≤ l → ∀ (R : Type) [CommRing R] (ξ ν a γ : R), ν ^ (l - 1) = ξ + (l : R) * a →
    (l.factorial : R) * γ = ξ ^ l →
    (ξ * ν) ^ (l - 1) = (l : R) * (((l - 1).factorial : R) * γ + a * ξ ^ (l - 1))) ∧
  (∀ (l : ℕ) (R : Type) [CommRing R] (μ β δ : R) (k : ℕ), μ ^ (l - 1) = (l : R) * β →
    β ^ l = (l : R) * δ → μ ^ (l * (l - 1) * k) = (l : R) ^ ((l + 1) * k) * δ ^ k) ∧
  ∀ (l i : ℕ), l.Prime →
    (i : ℝ) / ((l : ℝ) * ((l : ℝ) - 1)) - ((l : ℝ) + 1) ≤
      (((l + 1) * (i / (l * (l - 1))) : ℕ) : ℝ) - (padicValNat l i.factorial : ℝ)

def ValuationIntegerBound : Prop :=
  ∀ (l H : ℕ) (va c₁ : ℤ), 2 ≤ l →
    -(c₁ : ℝ) - 2 * (4 * (H : ℝ)) / ((l : ℝ) - 1) ≤ (va : ℝ) →
    (8 * H + 1 ≤ l → -(c₁ + 1) ≤ va) ∧ (8 * H + 1 < l → -c₁ ≤ va)

def UnitPlusNilp : Prop :=
  ∀ (S : Type) [CommRing S] (l c₀ t : S) (k : ℕ) [IsAdicComplete (Ideal.span {l}) S],
    IsUnit c₀ → l ∣ t ^ k → IsUnit (c₀ + t)

def EulerCoordNeg : Prop :=
  ∀ (K : Type) [Field K] (l : K), l ≠ 0 → ∀ ω : (PowerSeries K)ˣ,
    (PowerSeries.X * (ω : PowerSeries K)) * (PowerSeries.C l - PowerSeries.X) =
      PowerSeries.C l * PowerSeries.X →
    ∀ j : ℕ, (PowerSeries.X - PowerSeries.C l) *
        (PowerSeries.X * PowerSeries.derivative K (((ω⁻¹ : (PowerSeries K)ˣ) : PowerSeries K) ^ j) -
          (j : PowerSeries K) * ((ω⁻¹ : (PowerSeries K)ˣ) : PowerSeries K) ^ j) =
      (PowerSeries.C l * (j : PowerSeries K)) * ((ω⁻¹ : (PowerSeries K)ˣ) : PowerSeries K) ^ j

def NumTV6 : Prop :=
  ∀ (l H η N r' : ℕ), 2 ≤ N → 1 ≤ η → η < H → 4 * r' ≤ N ^ 2 → 40 * (H * N ^ 2 + N ^ 3) < l →
    8 * H + 1 < l ∧ 2 * (H + η + (2 * (N - 1) * r' + 1)) + 2 < l

def TameDegreeCoprime : Prop :=
  ∀ (l : ℕ) (s : Finset ℕ), l.Prime → (∀ x ∈ s, 1 ≤ x ∧ x < l) →
    Nat.Coprime (s.lcm id) l ∧ Nat.Coprime ((l ^ (s.lcm id) - 1) * s.lcm id) l

def OrbitDigit : Prop :=
  ∀ (l a c ρ : ℕ), 1 ≤ l →
    (((fun x : ZMod (l ^ a - 1) => (l : ZMod (l ^ a - 1)) * x)^[ρ]) (c : ZMod (l ^ a - 1)) = c ↔
      (l ^ a - 1) ∣ c * (l ^ ρ - 1))

def FaithfullyFlatImage : Prop :=
  ∀ (O O' M₁ M₂ : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.FaithfullyFlat O O']
    [AddCommGroup M₁] [Module O M₁] [AddCommGroup M₂] [Module O M₂] (f : M₁ →ₗ[O] M₂) (c : M₂),
    ((1 : O') ⊗ₜ[O] c) ∈ LinearMap.range (f.baseChange O') → c ∈ LinearMap.range f

def FrobBasis : Prop :=
  ∀ (O : Type) [CommRing O] (l : ℕ), 1 ≤ l → ∀ f : PowerSeries O,
    ∃! g : Fin l → PowerSeries O, f = ∑ j : Fin l, PowerSeries.X ^ (j : ℕ) * frob l (g j)

def AverageLift : Prop :=
  ∀ (O G M₁ M₂ : Type) [CommRing O] [Group G] [Fintype G] [AddCommGroup M₁] [Module O M₁]
    [AddCommGroup M₂] [Module O M₂] [DistribMulAction G M₁] [DistribMulAction G M₂]
    [SMulCommClass G O M₁] [SMulCommClass G O M₂] (f : M₁ →ₗ[O] M₂),
    IsUnit (Fintype.card G : O) → (∀ (g : G) (x : M₁), f (g • x) = g • f x) →
    ∀ (y : M₂) (z : M₁), (∀ g : G, g • y = y) → f z = y →
      ∃ z' : M₁, (∀ g : G, g • z' = z') ∧ f z' = y

def FrobDeriv : Prop :=
  ∀ (O : Type) [CommRing O] (l : ℕ), 1 ≤ l → ∀ f : PowerSeries O,
    (PowerSeries.X * PowerSeries.derivative O (frob l f) =
      PowerSeries.C (l : O) * frob l (PowerSeries.X * PowerSeries.derivative O f)) ∧
    ∀ ζ : O, PowerSeries.X * PowerSeries.derivative O (PowerSeries.rescale ζ f) =
      PowerSeries.rescale ζ (PowerSeries.X * PowerSeries.derivative O f)

def IsotypicSeries : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (e : ℕ) (ζ : O), IsPrimitiveRoot ζ e →
    ∀ (c : ℕ) (f : PowerSeries O), c < e →
      (PowerSeries.rescale ζ f = PowerSeries.C (ζ ^ c) * f ↔
        ∃ g : PowerSeries O, f = PowerSeries.X ^ c * frob e g)

def WeierstrassQuotFree : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (l : O) (e η : ℕ), l ∈ IsLocalRing.maximalIdeal O → 1 ≤ e →
    Module.Free O (PowerSeries O ⧸ Ideal.span {(PowerSeries.X ^ e + PowerSeries.C l) ^ η}) ∧
    Module.finrank O (PowerSeries O ⧸ Ideal.span {(PowerSeries.X ^ e + PowerSeries.C l) ^ η}) =
      e * η

def DerivPole : Prop :=
  ∀ (B : Type) [CommRing B] (N : Derivation ℤ B B) (v Ei : B) (l e k : ℕ),
    (v + (l : B)) * Ei = 1 → N v = (e : B) * v →
    N (v * Ei ^ k) = (e : B) * v * Ei ^ (k + 1) * ((v + (l : B)) - (k : B) * v)

def EigenKill : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (T : Module.End K V) (J : Finset K),
    (⨆ μ ∈ J, Module.End.eigenspace T μ) = ⊤ → aeval T (∏ μ ∈ J, (X - C μ)) = 0

def SemisimpleImage : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (T : Module.End K V) (R : K[X]),
    aeval T (X * R) = 0 → R.eval 0 ≠ 0 →
    (∀ w ∈ LinearMap.range T, aeval T R w = 0) ∧
    ∀ W : Submodule K V, (∀ x ∈ W, T x ∈ W) → LinearMap.range T ⊓ W = W.map T

def LcSolve : Prop :=
  ∀ (O Z : Type) [CommRing O] [AddCommGroup Z] [Module O Z] (Lc 𝓋 : Module.End O Z) (R : O[X])
    (l : O) (η k : ℕ) (w z : Z),
    (∀ x : Z, l • x = 0 → x = 0) → aeval Lc (X * R) = 0 → (∀ x, ∃ x', l ^ η • x = 𝓋 x') →
    l ^ k • w = Lc z →
    aeval Lc R w = 0 ∧ ∃ z', (l ^ η * R.eval 0) • w = Lc (𝓋 z')

def AnnFlatBaseChange : Prop :=
  ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    [AddCommGroup C] [Module A C] [Module.Finite A C],
    Module.annihilator B (TensorProduct A B C) = (Module.annihilator A C).map (algebraMap A B)

def AnnShift : Prop :=
  ∀ (A P : Type) [CommRing A] [AddCommGroup P] [Module A P] (M₂ M' L₂ L' : Submodule A P)
    (E α : A) (H η : ℕ),
    (∀ x ∈ L₂, E ^ η • x ∈ M₂) → (∀ m ∈ M₂, α • m ∈ M') → (∀ m ∈ M', E ^ H • m ∈ L') →
    ∀ x ∈ L₂, (E ^ (H + η) * α) • x ∈ L'

def CokerDegree : Prop :=
  ∀ (O ι : Type) [CommRing O] [Finite ι] (σ : ι → ι) (l e h b : ℕ)
    (aa : ι → Ideal (PowerSeries O)), Function.Bijective σ → 2 ≤ l → 1 ≤ b → h + b ≤ l →
    (∀ τ, ∀ α ∈ aa τ, (PowerSeries.X ^ e + PowerSeries.C (l : O)) ^ h * α ∈
      Ideal.span (frob l '' (aa (σ τ) : Set (PowerSeries O)))) →
    (∀ τ, ∃ s, PowerSeries.X ^ s ∈ aa τ ⊔ Ideal.span {PowerSeries.C ((l : O) ^ b)}) →
    ∀ τ, PowerSeries.X ^ (e * (h + b)) ∈ Ideal.span (frob l ''
      ((aa τ ⊔ Ideal.span {PowerSeries.C ((l : O) ^ b)} : Ideal (PowerSeries O)) :
        Set (PowerSeries O)))

def PDCoeffVal : Prop :=
  ∀ (l i k : ℕ) [Fact l.Prime], k < l → k ≤ i →
    padicValRat l ((i.choose k : ℚ) * (l : ℚ) ^ (i - k) / (i.factorial : ℚ)) =
      ((i - k : ℕ) : ℤ) - (padicValNat l (i - k).factorial : ℤ) ∧
    0 ≤ padicValRat l ((i.choose k : ℚ) * (l : ℚ) ^ (i - k) / (i.factorial : ℚ))

def FiltProdSparse : Prop :=
  ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (T : Module.End R V)
    (F : ℕ → Submodule R V) (c : ℕ → R) (Dg : Finset ℕ) (k a : ℕ),
    (∀ i, k ≤ i → i < k + a → ∀ x ∈ F i, T x - c i • x ∈ F (i + 1)) →
    (∀ i, k ≤ i → i < k + a → i ∉ Dg → F i ≤ F (i + 1)) →
    ∀ x ∈ F k, aeval T (∏ i ∈ Dg ∩ Finset.Ico k (k + a), (X - C (c i))) x ∈ F (k + a)

def ExtBound : Prop :=
  ∀ (A P : Type) [CommRing A] [AddCommGroup P] [Module A P] (M L : Submodule A P) (E : A)
    (x y : P) (H η : ℕ), E ^ η • y ∈ M → (∀ m ∈ M, E ^ H • m ∈ L) →
    E ^ (H + η) • x ∈ L ⊔ Submodule.span A {x + y} ∧
    E ^ η • (x + y) ∈ M ⊔ Submodule.span A {x}

def GLIdemIntegral : Prop :=
  ∀ (g r f : ℕ) [Fact g.Prime] (K : Type) [Field K] [CharZero K]
    (e : MonoidAlgebra K (Fin f → Matrix.GeneralLinearGroup (Fin r) (ZMod g))),
    e * e = e → (∀ y, e * y = y * e) →
    ∃ m : ℕ, ¬ g ∣ m ∧
      ∀ x, IsIntegral ℤ ((m : K) * (g : K) ^ (f * (r * (r - 1) / 2)) * e.coeff x)

def CutPassage : Prop :=
  ∀ (O V : Type) [CommRing O] [AddCommGroup V] [Module O V] (pr y : Module.End O V)
    (Mt : Submodule O V), pr ∘ₗ pr = pr → y ∘ₗ pr = y → pr ∘ₗ y = y → (∀ x ∈ Mt, y x ∈ Mt) →
    (Mt.map pr).map y = Mt.map y ∧ Mt.map y ≤ Mt ⊓ LinearMap.range pr ∧
    Mt ⊓ LinearMap.range pr ≤ Mt.map pr ∧
    Module.length O (↥(Mt.map pr) ⧸ (Mt ⊓ LinearMap.range pr).comap (Mt.map pr).subtype) ≤
      Module.length O (↥(Mt.map pr) ⧸ ((Mt.map pr).map y).comap (Mt.map pr).subtype)

def DelValNat : Prop :=
  ∀ (g t : ℕ), g.Prime → 1 ≤ t → t ≤ g →
    ∑ i ∈ Finset.Ico 1 t, (1 + padicValNat g i) = t - 1

def JumpRange : Prop :=
  ∀ (b S η c₀ u : ℤ), 0 ≤ b → 0 ≤ S → 0 ≤ η → 0 ≤ c₀ →
    (((0 ≤ u ∧ u ≤ 2 * c₀) ∨ |u - c₀| ≤ η + 1 ∨ (0 < u - c₀ ∧ u - c₀ ≤ b + S + η + 1)) →
      -(η + (2 * c₀ + 1) + 1) ≤ u ∧ u ≤ b + S + η + (2 * c₀ + 1)) ∧
    (((0 ≤ u ∧ u ≤ 2 * c₀) ∨ |u - c₀| ≤ η + 1 ∨ (0 < c₀ - u ∧ c₀ - u ≤ b + S + η + 1)) →
      -(η + (2 * c₀ + 1) + 1) ≤ -u - 1 ∧ -u - 1 ≤ b + S + η + (2 * c₀ + 1))

def LocalCount : Prop :=
  ∀ (O X : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [AddCommGroup X] [Module O X]
    [Module.Finite O X] (l a b e' : ℕ) (s : Finset X),
    s.card ≤ a → Submodule.torsion O X ≤ Submodule.span O (s : Set X) →
    Module.finrank O (X ⧸ Submodule.torsion O X) ≤ b →
    (∃ s' : Finset X, s'.card ≤ a + b ∧ Submodule.span O (s' : Set X) = ⊤) ∧
    Module.length O (X ⧸ (Ideal.span {(l : O) ^ e'} • ⊤ : Submodule O X)) ≤
      ((a + b : ℕ) : ℕ∞) * (e' : ℕ∞) * Module.length O (O ⧸ Ideal.span {(l : O)})

def GL2UnipotentBruhatDecomposition : Prop :=
  ∀ (F : Type) [Field F] (x : F), x ≠ 0 →
    (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) F) =
      !![1, 0; x⁻¹, 1] * !![0, x; -x⁻¹, 0] * !![1, 0; x⁻¹, 1]

def IwahoriUnit : Prop :=
  ∀ (Hk : Type) [Ring Hk] (q : ℕ) (T : Hk), IsUnit (q : Hk) →
    T * T = (q : Hk) + ((q : Hk) - 1) * T → IsUnit T

def IsMaxSeg (μ : ℤ → ℕ) (h : ℕ) (c d : ℤ) : Prop :=
  c ≤ d ∧ (∀ x, c ≤ x → x ≤ d → h ≤ μ x) ∧ μ (c - 1) < h ∧ μ (d + 1) < h

def LevelSegmentsUnlinked : Prop :=
  ∀ (μ : ℤ → ℕ) (h h' : ℕ) (c d c' d' : ℤ), IsMaxSeg μ h c d → IsMaxSeg μ h' c' d' →
    (c ≤ c' ∧ d' ≤ d) ∨ (c' ≤ c ∧ d ≤ d') ∨ d + 1 < c' ∨ d' + 1 < c

end Formalism.IrreducibleCountingLemmas.WindowSums
