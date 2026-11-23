import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.IsHerm

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace UpperTheory.ConvolutionTheory.G3

def Tw {G : Type} [Group G] (θ : G →* G) (x y : G) : Prop := ∃ g, y = g⁻¹ * x * θ g

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

def gpol (δ : GL (Fin n) E) : E[X] := (δ * thE E n δ).val.charpoly

def lpol (w : Pl E) (y : GLw n w) : (w.adicCompletion E)[X] := (nrmL n w y).val.charpoly

abbrev Fv (w : Pl E) : Type := (w.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)

def Idx (w : Pl E) (φ : GLw a w × GLw b w → ℂ) : Prop :=
  ∀ δ x : GLw a w × GLw b w, (rStab fun k : (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) =>
    φ ((x * k)⁻¹ * δ * (thL a w).prodMap (thL b w) (x * k))).index ≠ 0

def orbP (S : Set (Pl E)) (φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (c : TwCl (thE E a) × TwCl (thE E b)) : ℂ :=
  ∏ᶠ w ∈ S, twOrb ((thL a w).prodMap (thL b w)) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b))
    (locEl a w c.1.rep, locEl b w c.2.rep) (φ w)

def LocConj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (δ g : GL (Fin n) E), Tw (thL n w) (locEl n w δ) (locEl n w (g⁻¹ * δ * thE E n g))

def IntUniq : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (δ : GL (Fin n) E), (gpol δ).Separable → ∀ᶠ w : Pl E in cofinite,
    locEl n w δ ∈ GlobalTheory.LFun.KGL w n ∧ ∀ y ∈ GlobalTheory.LFun.KGL w n, lpol w y = atPl w (gpol δ) →
      ∃ k ∈ GlobalTheory.LFun.KGL w n, y = k⁻¹ * locEl n w δ * thL n w k

def CptInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (δ : GL (Fin n) E), (gpol δ).Separable → ∀ᶠ w : Pl E in cofinite,
    cptPart (twCent (thL n w) (locEl n w δ)) = twCent (thL n w) (locEl n w δ) ⊓ GlobalTheory.LFun.KGL w n

def OrbUnit : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K : Subgroup G) (δ : G), (∀ k ∈ K, θ k ∈ K) → δ ∈ K →
    (∀ y ∈ K, Tw θ δ y → ∃ k ∈ K, y = k⁻¹ * δ * θ k) → cptPart (twCent θ δ) = twCent θ δ ⊓ K →
    twOrb θ K δ ((K : Set G).indicator 1) = 1

def OrbZero : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ),
    (∀ y, Tw θ δ y → f y = 0) → twOrb θ K δ f = 0

def UnitAe : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (a b : ℕ) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E), (gpol δ₁).Separable → (gpol δ₂).Separable → ∀ᶠ w : Pl E in cofinite,
    ∀ (y₁ : GLw a w) (y₂ : GLw b w), lpol w y₁ = atPl w (gpol δ₁) → lpol w y₂ = atPl w (gpol δ₂) →
      twOrb ((thL a w).prodMap (thL b w)) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) (y₁, y₂)
        ((((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) : Subgroup _) : Set _).indicator 1) =
        if Tw (thL a w) (locEl a w δ₁) y₁ ∧ Tw (thL b w) (locEl b w δ₂) y₂ then 1 else 0

def Transl : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∃ u : GL (Fin n) E, (∀ g, thE E n g = u * UpperTheory.ConvolutionTheory.D.th (IsCMField.complexConj E) g * u⁻¹) ∧
    u * UpperTheory.ConvolutionTheory.D.th (IsCMField.complexConj E) u = 1 ∧ ∀ w : Pl E, ¬ IsSplitAt w → ∀ g : GLw n w,
      (thL n w g).val = u.val.map (algebraMap E _) * ((g⁻¹ : GLw n w).val.map (cj w))ᵀ * (u⁻¹ : GL (Fin n) E).val.map (algebraMap E _)

def PlaceIso : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E),
    (¬ IsSplitAt w → ∃ e : Fv w ⊗[maximalRealSubfield E] E ≃+* w.adicCompletion E,
      (∀ x : E, e (1 ⊗ₜ x) = algebraMap E _ x) ∧ ∀ z, e (UpperTheory.ConvolutionTheory.D.ext (Fv w) (IsCMField.complexConj E) z) = cj w (e z)) ∧
    (IsSplitAt w → ∀ (A : Type) [CommRing A] [Algebra (maximalRealSubfield E) A] (x : Fv w ⊗[maximalRealSubfield E] A),
      UpperTheory.ConvolutionTheory.D.IsNm (maximalRealSubfield E) E x)

def ModelEll : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n →
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra (maximalRealSubfield E) A) (b : Module.Basis (Fin n) (maximalRealSubfield E) A)
      (g : (E ⊗[maximalRealSubfield E] A)ˣ), UpperTheory.ConvolutionTheory.D.IsReg (IsCMField.complexConj E) b g ∧ UpperTheory.ConvolutionTheory.D.cp (UpperTheory.ConvolutionTheory.D.matU b g) = P ∧
      ∃ (K : Fin (nfac P) → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, NumberField (K i)) (_ : ∀ i, Algebra (maximalRealSubfield E) (K i)),
        Nonempty (A ≃ₐ[maximalRealSubfield E] ∀ i, K i) ∧ ∀ i, IsTotallyReal (K i)

def Param : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (A : Type) [CommRing A] [Algebra (maximalRealSubfield E) A] (b : Module.Basis (Fin n) (maximalRealSubfield E) A)
    (g : (E ⊗[maximalRealSubfield E] A)ˣ), UpperTheory.ConvolutionTheory.D.IsReg (IsCMField.complexConj E) b g → ∀ P, UpperTheory.ConvolutionTheory.D.cp (UpperTheory.ConvolutionTheory.D.matU b g) = P →
    ∃ (D : Aˣ → GL (Fin n) E) (Dw : ∀ w : Pl E, (Fv w ⊗[maximalRealSubfield E] A)ˣ → GLw n w),
      (∀ x, gpol (D x) = P) ∧ (∀ δ, gpol δ = P → ∃ x, Tw (thE E n) (D x) δ) ∧
      (∀ x x', Tw (thE E n) (D x) (D x') ↔ UpperTheory.ConvolutionTheory.D.IsNm (maximalRealSubfield E) E (x' / x).val) ∧
      ∀ w, (∀ y, lpol w y = atPl w P → ∃ x, Tw (thL n w) (Dw w x) y) ∧
        (∀ x x', Tw (thL n w) (Dw w x) (Dw w x') ↔ UpperTheory.ConvolutionTheory.D.IsNm (maximalRealSubfield E) E (x' / x).val) ∧
        ∀ x, Tw (thL n w) (Dw w (Units.map (Algebra.TensorProduct.includeRight (R := maximalRealSubfield E)).toRingHom.toMonoidHom x))
          (locEl n w (D x))

def NormCount : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Type) [CommRing A] [Algebra (maximalRealSubfield E) A] (m : ℕ)
    (K : Fin m → Type) [∀ i, Field (K i)] [∀ i, NumberField (K i)] [∀ i, Algebra (maximalRealSubfield E) (K i)]
    (_ : A ≃ₐ[maximalRealSubfield E] ∀ i, K i), (∀ i, IsTotallyReal (K i)) →
    ∀ x : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), (v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] A)ˣ,
    {v | ¬ UpperTheory.ConvolutionTheory.D.IsNm (maximalRealSubfield E) E (x v).val}.Finite →
    ∃ T : Finset Aˣ, T.card * 2 ^ m = 2 ^ (Module.finrank (maximalRealSubfield E) A * Fintype.card (InfinitePlace E)) ∧
      (∀ a ∈ T, ∀ a' ∈ T, UpperTheory.ConvolutionTheory.D.IsNm (maximalRealSubfield E) E (a' / a).val → a = a') ∧
      ∀ a : Aˣ, (∀ v, UpperTheory.ConvolutionTheory.D.IsNm (maximalRealSubfield E) E ((x v).val * (1 ⊗ₜ (a⁻¹ : Aˣ).val))) ↔
        ∃ t ∈ T, UpperTheory.ConvolutionTheory.D.IsNm (maximalRealSubfield E) E (a / t).val

def Fibre : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ δ₀ : GL (Fin n) E, gpol δ₀ ∈ Ell E n → ∀ y : ∀ w : Pl E, GLw n w,
    (∀ w ∈ S, lpol w (y w) = atPl w (gpol δ₀)) → {w | w ∈ S ∧ ¬ Tw (thL n w) (locEl n w δ₀) (y w)}.Finite →
    {c : TwCl (thE E n) | gpol c.rep = gpol δ₀ ∧ ∀ w ∈ S, Tw (thL n w) (locEl n w c.rep) (y w)}.ncard * 2 ^ nfac (gpol δ₀) =
      2 ^ (n * Fintype.card (InfinitePlace E))

def LocAe : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (δ δ' : GL (Fin n) E), (gpol δ).Separable → gpol δ' = gpol δ →
    ∀ᶠ w : Pl E in cofinite, Tw (thL n w) (locEl n w δ) (locEl n w δ')

def MassKap : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (δ : GL (Fin n) E), gpol δ ∈ Ell E n →
    mass (thF E n) (ratF E n).range (ratF E n δ) = kap (gpol δ) * 2 ^ nfac (gpol δ)

def PolFin : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ C : ∀ w : Pl E, Set (GLw n w), (∀ w, IsCompact (C w)) →
    (∀ᶠ w in cofinite, C w ⊆ GlobalTheory.LFun.KGL w n) → {P | P ∈ Ell E n ∧ ∀ w ∈ S, ∃ y ∈ C w, lpol w y = atPl w P}.Finite

def StPairs : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (a b : ℕ) (w : Pl E) (Q₁ Q₂ : (w.adicCompletion E)[X]) (φ : GLw a w × GLw b w → ℂ), Idx w φ →
    stTw2 a b w Q₁ Q₂ φ = ∑ᶠ c ∈ {c : TwCl (thL a w) × TwCl (thL b w) | lpol w c.1.rep = Q₁ ∧ lpol w c.2.rep = Q₂},
      twOrb ((thL a w).prodMap (thL b w)) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) (c.1.rep, c.2.rep) φ

def Euler : Prop :=
  ∀ (W : Type) (S : Set W) (X : W → Type) (Y : ∀ w, Set (X w)) (o : ∀ w, X w) (F : ∀ w, X w → ℂ) (C : Type) (Z : Set C)
    (p : C → ∀ w, X w) (N : ℕ), N ≠ 0 → (∀ w ∈ S, (Y w).Finite ∧ o w ∈ Y w) →
    {w | w ∈ S ∧ ¬ ∀ x ∈ Y w, F w x = if x = o w then 1 else 0}.Finite →
    (∀ c ∈ Z, (∀ w ∈ S, p c w ∈ Y w) ∧ {w | w ∈ S ∧ p c w ≠ o w}.Finite) →
    (∀ x : ∀ w, X w, (∀ w ∈ S, x w ∈ Y w) → {w | w ∈ S ∧ x w ≠ o w}.Finite → {c | c ∈ Z ∧ ∀ w ∈ S, p c w = x w}.ncard = N) →
    (Z ∩ Function.support fun c => ∏ᶠ w ∈ S, F w (p c w)).Finite ∧
      ∑ᶠ c ∈ Z, ∏ᶠ w ∈ S, F w (p c w) = N * ∏ᶠ w ∈ S, ∑ᶠ x ∈ Y w, F w x

def PairId : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (a b : ℕ) (S : Set (Pl E)), IsSection S → ∀ φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ, (∀ w, Idx w (φ w)) →
    (∀ᶠ w in cofinite, φ w = ((((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) : Subgroup _) : Set _).indicator 1)) →
    ∀ P₁ ∈ Ell E a, ∀ P₂ ∈ Ell E b,
    ({c : TwCl (thE E a) × TwCl (thE E b) | gpol c.1.rep = P₁ ∧ gpol c.2.rep = P₂} ∩ Function.support (orbP S φ)).Finite ∧
      (∑ᶠ c ∈ {c : TwCl (thE E a) × TwCl (thE E b) | gpol c.1.rep = P₁ ∧ gpol c.2.rep = P₂}, orbP S φ c) * 2 ^ nfac P₁ * 2 ^ nfac P₂ =
        2 ^ ((a + b) * Fintype.card (InfinitePlace E)) * ∏ᶠ w ∈ S, stTw2 a b w (atPl w P₁) (atPl w P₂) (φ w)

def PairSupp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (a b : ℕ) (S : Set (Pl E)) (φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ),
    (∀ᶠ w in cofinite, φ w = ((((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) : Subgroup _) : Set _).indicator 1)) →
    ∀ c : TwCl (thE E a) × TwCl (thE E b), (gpol c.1.rep).Separable → (gpol c.2.rep).Separable → orbP S φ c ≠ 0 →
    ∀ w ∈ S, ∃ y, φ w y ≠ 0 ∧ lpol w y.1 = atPl w (gpol c.1.rep) ∧ lpol w y.2 = atPl w (gpol c.2.rep)

def TestIdx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (a b : ℕ) (w : Pl E) (K₁ : Subgroup (GLw a w)) (K₂ : Subgroup (GLw b w))
    (φ : GLw a w × GLw b w → ℂ), IsLevel (thL a w) (GlobalTheory.LFun.KGL w a) K₁ → IsLevel (thL b w) (GlobalTheory.LFun.KGL w b) K₂ →
    IsHecke (K₁.prod K₂) φ → Idx w φ

end UpperTheory.ConvolutionTheory.G3
