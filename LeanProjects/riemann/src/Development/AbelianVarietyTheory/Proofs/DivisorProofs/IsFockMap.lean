import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RealLift

section OnePlace

variable {P Q R S : ℕ}

def IsLift (x t : ℚ) (M : GKMod R S) (pr : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] M.V) : Prop :=
  Function.Surjective pr ∧ (∀ X f, pr (fockAct1 P Q R S X f) = ((x : ℂ) * X.trace) • pr f) ∧
    ∀ Y f, M.act Y (pr f) = pr (fockAct2 P Q R S Y f) + ((t : ℂ) * Y.trace) • pr f

def Num (P Q P' Q' R S : ℕ) (κ : ℤ) : Prop :=
  R = P + Q' ∧ S = Q + P' ∧ S < P ∧ S < Q' ∧ Even (R + S) ∧ Even κ ∧ ((R + S : ℕ) : ℤ) < κ

def lam (P Q R S : ℕ) (κ : ℤ) : Ix R S → ℚ
  | .inl i => if (i : ℕ) < P then (κ : ℚ) / 2 - cPair R S + cPair P Q else cPair P Q
  | .inr j => if (j : ℕ) < Q then (κ : ℚ) / 2 + cPair R S - cPair P Q else -cPair P Q

def casK (μ : Ix R S → ℚ) : ℚ :=
  ∑ a, μ a ^ 2 + (∑ i : Fin R, μ (.inl i) * ((R : ℚ) - 1 - 2 * (i : ℕ))) + ∑ j : Fin S, μ (.inr j) * ((S : ℚ) - 1 - 2 * (j : ℕ))

def addRoot (μ : Ix R S → ℚ) (a b : Ix R S) : Ix R S → ℚ :=
  fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)

def Steep (M : GKMod R S) (Λ : Ix R S → ℚ) : Prop :=
  ∀ a b, ¬ sameBlock a b → ∀ w, IsHW M.act (addRoot Λ a b) w → casK Λ + ((R + S : ℕ) : ℚ) < casK (addRoot Λ a b)

def GenBy (M : GKMod R S) (Λ : Ix R S → ℚ) : Prop := ∃ v, IsHW M.act Λ v ∧ genSub M.act {v} = ⊤

def IsQuot (M N : GKMod R S) (π : M.V →ₗ[ℂ] N.V) : Prop :=
  Function.Surjective π ∧ ∀ Y v, π (M.act Y v) = N.act Y (π v)

def ScalarEnd (M : GKMod R S) : Prop :=
  ∀ T : M.V →ₗ[ℂ] M.V, (∀ Z, T ∘ₗ M.act Z = M.act Z ∘ₗ T) → ∃ c : ℂ, T = c • LinearMap.id

def HasForm (P Q R S : ℕ) (x : ℚ) : Prop :=
  ∃ l : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] ℂ, l ≠ 0 ∧ ∀ X f, l (fockAct1 P Q R S X f) = (x : ℂ) * X.trace * l f

def IsHarmVec (x : ℚ) (μ : Ix R S → ℚ) (f : Formalism.BasicNotions.TH.Pol P Q R S) : Prop :=
  f ∈ harm2 P Q R S ∧ (∀ X, IsKC X → fockAct1 P Q R S X f = ((x : ℂ) * X.trace) • f) ∧ IsHW (fockAct2 P Q R S) μ f

def heisOp (c : Matrix (Ix P Q) (Ix R S) ℂ) : Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S) :=
  ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) • ∑ l : Ln P Q R S,
    (c l.1 l.2 • raiB l - (lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 * star (c l.1 l.2)) • lowB l)

def IsFrame {α : Type} [Fintype α] [DecidableEq α] (M : Matrix α α ℂ) (A : Matrix α (Ix P Q) ℂ) : Prop :=
  Aᵀ * M * A.map star = Jm P Q ∧ ∃ A' : Matrix (Ix P Q) α ℂ, A * A' = 1

end OnePlace

def MultOne : Prop :=
  ∀ (R S : ℕ) (M : GKMod R S) (Λ : Ix R S → ℚ) (v : M.V), IsHW M.act Λ v → genSub M.act {v} = ⊤ → Steep M Λ →
    ∀ w ∈ hwSub M.act Λ, ∃ c : ℂ, w = c • v

def FormEx : Prop :=
  ∀ (P Q R S : ℕ) (x : ℚ) (k k' : ℕ), P ≤ R → Q ≤ S → 0 < k → 0 < k' → x - cPair R S = k → x + cPair R S = k' →
    HasForm P Q R S x

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

def atPl (w : ι) (L : Module.End ℂ (V w)) : Module.End ℂ (⨂[ℂ] i, V i) :=
  PiTensorProduct.map (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w L)

def sumPl (L : ∀ w, Module.End ℂ (V w)) : Module.End ℂ (⨂[ℂ] i, V i) := ∑ w, atPl w (L w)

end Tensor

def LocFin {V : Type} [AddCommGroup V] [Module ℂ V] (L : Module.End ℂ V) : Prop :=
  ∀ v, ∃ N : Submodule ℂ V, FiniteDimensional ℂ N ∧ v ∈ N ∧ ∀ y ∈ N, L y ∈ N

def IsExp {V : Type} [AddCommGroup V] [Module ℂ V] (L U : Module.End ℂ V) : Prop :=
  ∀ (v : V) (l : V →ₗ[ℂ] ℂ), HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * l ((L ^ n) v)) (l (U v))

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {P Q R S : ℕ}

variable (F) in

abbrev Tens (P Q R S : ℕ) : Type := ⨂[ℂ] _ : InfinitePlace F, Formalism.BasicNotions.TH.Pol P Q R S

def SD (T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (f f₁ : SInf F κ) : Prop :=
  ∀ g ∈ SB (κ → Af F), ∀ l ∈ (adeleClass F).adm κ, HasDerivAt (fun t => l (T t (pureA F f g))) (l (pureA F f₁ g)) 0

def SA (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (f f₁ : SInf F κ) : Prop :=
  ∀ g ∈ SB (κ → Af F), T (pureA F f g) = pureA F f₁ g

def Framed (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (a b : ℂ)
    (A : InfinitePlace F → Matrix α (Ix P Q) ℂ) (C : InfinitePlace F → Matrix β (Ix R S) ℂ) : Prop :=
  a * b = Complex.I ∧ (∀ w, IsFrame (a • JA.map (piInf (τ w))) (A w)) ∧ ∀ w, IsFrame (b • JB.map (piInf (τ w))) (C w)

def IsFockMap (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {JA : Matrix α α (AE F E)}
    {JB : Matrix β β (AE F E)} (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (A : InfinitePlace F → Matrix α (Ix P Q) ℂ) (C : InfinitePlace F → Matrix β (Ix R S) ℂ)
    (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ) : Prop :=
  Function.Injective Φ ∧ ∀ u : Matrix α β (AE F E), At (evI F) u → ∀ c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ,
    (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
      ∀ T, SD (fun t => d.rho ψ (realAd F t • u)) (Φ T) (Φ (sumPl (fun w => heisOp (c w)) T))

variable (σ) in

def RLines (J : Matrix β β (AE F E)) : Set (Multiplicative ℝ →* UG (cA σ) J) :=
  {γ | Continuous γ ∧ ∀ t, At (evI F) (((γ t).1 : Matrix β β (AE F E)) - 1)}

def IsGen (τ : ∀ w : InfinitePlace F, EmbOver E w) {J : Matrix β β (AE F E)} (C : InfinitePlace F → Matrix β (Ix R S) ℂ)
    (γ : Multiplicative ℝ →* UG (cA σ) J) (Y : InfinitePlace F → Mat R S) : Prop :=
  ∀ (t : ℝ) w, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w =
    C w * NormedSpace.exp (t • Y w)

def ActsBy (τ : ∀ w : InfinitePlace F, EmbOver E w) {J : Matrix β β (AE F E)} {r s : ℕ}
    (C : InfinitePlace F → Matrix β (Ix r s) ℂ) (om : UG (cA σ) J →* Module.End ℂ ((κ → AF F) → ℂ))
    (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ) (act : Mat r s →ₗ[ℂ] Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))
    (c : InfinitePlace F → ℂ) : Prop :=
  ∀ γ ∈ RLines σ J, ∀ Y, IsGen τ C γ Y → ∀ T, SD (fun t => om (γ (Multiplicative.ofAdd t))) (Φ T)
    (Φ (sumPl (fun w => act (Y w) + (c w * (Y w).trace) • 1) T))

end Adelic

def ActsLaws : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (f f₁ f₂ : SInf F κ),
    (∀ T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ, (∀ t, T t 0 = 0) → SD T f f₁ → ActsD (evI F) T f f₁) ∧
    (∀ T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ, T 0 = 0 → SA T f f₁ → Acts (evI F) T f f₁) ∧
    (∀ T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ, ActsD (evI F) T f f₁ → ActsD (evI F) T f f₂ → f₁ = f₂) ∧
    (∀ T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ, Acts (evI F) T f f₁ → Acts (evI F) T f f₂ → f₁ = f₂) ∧
    ∀ T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ, SD T f f₁ → SD T f f₂ → f₁ = f₂

def DerEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ), IsStd ψ →
    ∃ D : Matrix α β (AE F E) → (SInf F κ →L[ℂ] SInf F κ), ∀ u, At (evI F) u → ∀ f,
      SD (fun t => d.rho ψ (realAd F t • u)) f (D u f) ∧ ∀ x, D u f x =
        fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x

def FockEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → IsStd ψ → Framed τ JA JB a b A C →
    ∃ Φ, IsFockMap ψ τ d A C Φ

def VacLine : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ → ∀ (f₀ : SInf F κ) (ε : InfinitePlace F → ℤˣ),
    (∀ u u' : Matrix α β (AE F E), At (evI F) u → At (evI F) u' → ∀ c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ,
      (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
      (∀ w, u'.map (piInf (τ w)) = A w * ((((ε w : ℤ) : ℂ) * Complex.I) • (Jm P Q * c w * Jm R S)) * (C w)ᵀ) →
      ∀ f f' : SInf F κ, SD (fun t => d.rho ψ (realAd F t • u)) f₀ f → SD (fun t => d.rho ψ (realAd F t • u')) f₀ f' →
        f' = Complex.I • f) →
    ∃ z : ℂ, f₀ = z • Φ (PiTensorProduct.tprod ℂ fun _ => 1)

def GenEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∀ γ ∈ RLines σ J, ∃ Y, (∀ w, Y w ∈ upq R S) ∧ IsGen τ C γ Y

def LineEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∀ Y : InfinitePlace F → Mat R S, (∀ w, Y w ∈ upq R S) → ∃ γ ∈ RLines σ J, IsGen τ C γ Y

def LieScalar : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ)
    (om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)), IsCMExt F E σ → IsStd ψ →
    Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ → IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om →
    ∃ c, ActsBy τ C om Φ (fockAct2 P Q R S) c

def LieSecond : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ)
    (om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)) (χ : Chr F E) (m : InfinitePlace F → ℤ), IsCMExt F E σ → IsStd ψ →
    Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ → IsUWeilB (cA σ) (adeleClass F) ψ (-1) JA JB d χ om → HasExp τ χ m →
    ActsBy τ C om Φ (fockAct2 P Q R S) fun w => (m w : ℂ) / 2

def LieFirst : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (d' : Darboux (symp (R := AF F) (cA σ) (-1) JB JA) κ) (a b : ℂ)
    (A : InfinitePlace F → Matrix α (Ix P Q) ℂ) (C : InfinitePlace F → Matrix β (Ix R S) ℂ)
    (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ) (om : UG (cA σ) JA →* Module.End ℂ ((κ → AF F) → ℂ)) (χ : Chr F E)
    (m : InfinitePlace F → ℤ), IsCMExt F E σ → IsStd ψ → Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ →
    (∀ x : Matrix α β (AE F E), d'.e xᵀ = d.e x) → IsUWeilB (cA σ) (adeleClass F) ψ (-1) JB JA d' χ om → HasExp τ χ m →
    ActsBy τ A om Φ (fockAct1 P Q R S) fun w => (m w : ℂ) / 2

def KLine : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (θ : InfinitePlace F → Matrix β β ℂ), IsCMExt F E σ →
    (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) → (∀ w, θ w * C w = C w * Jm R S) → ∀ k : UG (cA σ) J,
    At (evI F) ((k.1 : Matrix β β (AE F E)) - 1) → (∀ w, Commute ((k.1 : Matrix β β (AE F E)).map (piInf (τ w))) (θ w)) →
    ∃ γ ∈ RLines σ J, ∃ Y, IsGen τ C γ Y ∧ (∀ w, IsKC (Y w)) ∧ γ (Multiplicative.ofAdd 1) = k

def FrameEx : Prop :=
  ∀ (n r s : ℕ) (M θ : Matrix (Fin n) (Fin n) ℂ), HasSig M r s → IsCartan M θ →
    ∃ A : Matrix (Fin n) (Ix r s) ℂ, IsFrame M A ∧ θ * A = A * Jm r s

def PolRange : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d P Q R S : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (A : InfinitePlace F → Matrix (Fin n) (Ix P Q) ℂ) (C : InfinitePlace F → Matrix (Fin d) (Ix R S) ℂ)
    (Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)), IsCMExt F E σ → IsStd ψ →
    Framed τ (incM F X.J) (incM F W.J) 1 Complex.I A C → (∀ w, X.θ w * A w = A w * Jm P Q) →
    (∀ w, W.θ w * C w = C w * Jm R S) → IsFockMap ψ τ M.co A C Φ → LinearMap.range Φ = M.Pol ψ τ

def Parity : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ w, Even (B.mα w - B.mβ w)

theorem lines_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    (X : Spc F E n) : Lines σ X = RLines σ (incM F X.J) := rfl

example : IsFrame (P := 1) (Q := 1) (Jm 1 1) 1 := ⟨by simp [Matrix.map_one], 1, by simp⟩

end GlobalTheory.RealLift

end
