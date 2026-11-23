import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section
namespace GlobalTheory.SymBridge
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

def xPos {κ τ j : ℕ} : XIx (Fin κ) (Fin τ) j → ℕ
  | .inl (.inl i) => i.val
  | .inl (.inr i) => κ + i.val
  | .inr p => κ + j + p.1.val * τ + p.2.val

def zPos {κ τ l j : ℕ} : Ix (Fin κ ⊕ Fin l) (Fin τ) j → ℕ
  | .inl (.inl i) => i.val
  | .inl (.inr i) => κ + i.val
  | .inr p => κ + l + p.1.val * τ + p.2.val

def yPos {A : Type} {c : ℕ} (pos : A → ℕ) (n : ℕ) : A ⊕ Fin c → ℕ := Sum.elim pos fun i => n + i.val

def IsOrd {A : Type} {n : ℕ} (pos : A → ℕ) (e : A ≃ Fin n) : Prop := ∀ a, (e a).val = pos a

section Loc
variable {E K k : Type} [Field E] [NumberField E] [StarRing E] [Field K]
  [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def toLoc (ι : E →+* k) {A B : Type} {a b : ℕ} (e : A ≃ Fin a) (e' : B ≃ Fin b) (x : (Fin b → E) →ₗ[E] (Fin a → E)) :
    Matrix A B k := fun i j => ι (x (Pi.single (e' j) 1) (e i))

structure IsCompl (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ) : Prop where
  int : ∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a
  dense : DenseRange ι
  norm : q = Ideal.absNorm P.asIdeal
  unif : (ϖ : k) = ι (q : E)

structure Comparison₂ (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ)
    (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {s κ : ℕ} (S : SymData k s κ) : Prop where
  compl : IsCompl P q ι S.ϖ
  psi : ∀ a, IntAt P a → (S.ψ (ι (a / (q : E))) : ℂ) = σ₀ (ψ₀ (redP P a))
  chi : ∀ i a (u : kˣ), IntAt P a → IsUnit (redP P a) → (u : k) = ι a → (S.μ (i + 1) u : ℂ) = σ₀ (LocE.unitV (χ i) a)

variable (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ)
  (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {s κ : ℕ} (S : SymData k s κ)

def PhiAgree : Prop :=
  ∀ (τ j c : ℕ) (h : j + c = s) (n' c' n c₂ : ℕ), n' = κ + j * (τ + 1) → n = κ + (j + 1) * (τ + 1) → c' = c + 1 → c₂ = c →
    ∀ (e' : XIx (Fin κ) (Fin τ) j ⊕ Fin (c + 1) ≃ Fin (n' + c')) (e : XIx (Fin κ) (Fin τ) (j + 1) ⊕ Fin c ≃ Fin (n + c₂)),
      IsOrd (yPos xPos n') e' → IsOrd (yPos xPos n) e → ∀ x,
        (S.T (Fin τ)).Phi j c h (toLoc ι e e' x) = σ₀ (LocE.PhiGS q ψ₀ χ κ S.ρ (κ + s + 1) τ (j + 1) c' n' c₂ n x)

def PhiTopAgree : Prop :=
  ∀ (τ n' c' n : ℕ), n' = κ + (s + 1) * (τ + 1) → c' = 0 → n = κ + s + 1 + (s + 2) * τ →
    ∀ (e' : XIx (Fin κ) (Fin τ) (s + 1) ⊕ Fin 0 ≃ Fin (n' + c')) (e : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ≃ Fin (n + 0)),
      IsOrd (yPos xPos n') e' → IsOrd zPos e → ∀ x,
        (S.T (Fin τ)).PhiTop (toLoc ι e e' x) = σ₀ (LocE.PhiGS q ψ₀ χ κ S.ρ (κ + s + 1) τ (s + 2) c' n' 0 n x)

def LevelAgree : Prop :=
  ∀ (τ j c : ℕ) (h : j + c = s + 1) (n c₂ : ℕ), n = κ + j * (τ + 1) → c₂ = c →
    ∀ (e : XIx (Fin κ) (Fin τ) j ⊕ Fin c ≃ Fin (n + c₂)), IsOrd (yPos xPos n) e →
      ∀ (γ : Sp E (n + c₂) ≃ₗ[E] Sp E (n + c₂)) (g : GL (XIx (Fin κ) (Fin τ) j ⊕ Fin c) k), g.val = toLoc ι e e γ.toLinearMap →
        (g ∈ ((S.T (Fin τ)).lev j c h).J ↔ γ ∈ LocE.JGsym P q κ S.ρ (κ + s + 1) τ n c₂) ∧
        ∀ hg : g ∈ ((S.T (Fin τ)).lev j c h).J,
          (((S.T (Fin τ)).lev j c h).lam ⟨g, hg⟩ : ℂ) = σ₀ (LocE.lamGBS q ψ₀ χ κ (κ + s + 1) τ j n c₂ γ.toLinearMap)

end Loc

def SumAgree : Prop :=
  ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K]
    [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ) (σ₀ : K →+* ℂ) (ψ : AddChar k Circle) (ν : Measure k) (psi : E → K),
    IsCompl P q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → HasConductor ψ 1 → IsUnitVol ν →
    (∀ a, IntAt P a → (ψ (ι (a / (q : E))) : ℂ) = σ₀ (psi (a / (q : E)))) →
    ∀ (U' U : Type) [Fintype U'] [DecidableEq U'] [Fintype U] [DecidableEq U] (c n' c' n c₂ A B : ℕ),
      1 ≤ c → c' = c + 1 → c₂ = c → c + 1 ≤ A → 1 ≤ B →
    ∀ (d' : U' ≃ Fin n') (d : U ≃ Fin n) (e' : U' ⊕ Fin (c + 1) ≃ Fin (n' + c')) (e : U ⊕ Fin c ≃ Fin (n + c₂)),
      IsOrd (yPos (fun a => (d' a).val) n') e' → IsOrd (yPos (fun a => (d a).val) n) e →
    ∀ (Φ : Matrix (U ⊕ Fin c) (U' ⊕ Fin (c + 1)) k → ℂ) (ΦE : Loc.SF E K (n' + c') (n + c₂)),
      (∀ x, Φ (toLoc ι e e' x) = σ₀ (ΦE x)) →
      (∀ x, Φ x ≠ 0 → IntM ((typeFrame ϖ (Equiv.refl _)).coords (typeFrame ϖ (Equiv.refl _)) x)) →
      (∀ x y, MaxM ((typeFrame ϖ (Equiv.refl _)).coords (typeFrame ϖ (Equiv.refl _)) y) → Φ (x + y) = Φ x) →
      ∀ x₀, opE ψ ν 1 Φ (toLoc ι d d' x₀) =
        σ₀ (Loc.E1 (n' := n') (c' := c') (n := n) (c := c₂) psi (LocE.valsQ E q A B) (((q : K) ^ B)⁻¹) ΦE x₀)

section Chain
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (ι : X.E →+* k) {s : ℕ} (S : SymData k s R.k)

structure AtType : Prop where
  mem : P.1 ∈ Pr.vGs
  steps : R.m = s + 2
  ok : cst.Ok
  sharp : cst.sharp = true
  deep : R.m ≤ cst.A
  psi0 : ∀ a, IntAt P.1 a → cst.psi P (a / (qOf P.1 : X.E)) = psi0P Ch P.1 (redP P.1 a)
  tie : Comparison₂ P.1 (qOf P.1) ι σ₀ (psi0P Ch P.1) (chiP Ch P.1) S

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k)

def EntryAgree : Prop :=
  ∀ j c (h : j + 1 + c = s) (e' : XIx (Fin R.k) (Fin R.t) j ≃ Fin (R.N j)) (e : XIx (Fin R.k) (Fin R.t) (j + 1) ≃ Fin (R.N (j + 1))),
    IsOrd xPos e' → IsOrd xPos e → ∃ C : ℂ, C ≠ 0 ∧ ∀ x,
      (S.T (Fin R.t)).entry S.ψ ν j c h 1 1 (toLoc ι e e' x) = C * σ₀ (XiAt Ch sel mu cst j P 1 1 x)

def PsiAgree : Prop :=
  ∀ (e' : XIx (Fin R.k) (Fin R.t) s ≃ Fin (R.N s)) (e : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))),
    IsOrd xPos e' → IsOrd xPos e → ∃ C : ℂ, C ≠ 0 ∧ ∀ x₀ y',
      (S.T (Fin R.t)).Psi 1 (toLoc ι e e' x₀) (fun a => ι (y' (e a))) = C * σ₀ (PsiAt Ch sel mu cst s P 1 x₀ y')

def TopAgree : Prop :=
  ∀ (e' : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1)))
    (e : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) ⊕ Unit ≃ Fin (R.N R.m)),
    IsOrd xPos e' → IsOrd (Sum.elim zPos fun _ => R.N R.m - 1) e → ∃ C : ℂ, C ≠ 0 ∧
      ∀ (y : HomE X.E (R.N (s + 1)) (R.N R.m)) (y' : Sp X.E (R.N (s + 1))), (∀ l, IntAt P.1 ((qOf P.1 : X.E) * y' l)) →
        (S.T (Fin R.t)).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk fun a => ι (y' (e' a))) (toLoc ι e e' y) =
          C * σ₀ (PhiTop Ch mu cst.sharp s P.1 (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1)))) *
            ftY sel mu cst P (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y) y')

end Chain

def MatchAtType : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu)
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ)
    (S : SymData k s R.k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → AtType Ch sel mu cst σ₀ P ι S →
      EntryAgree Ch sel mu cst σ₀ P ι S ν ∧ PsiAgree Ch sel mu cst σ₀ P ι S ∧ TopAgree Ch sel mu cst σ₀ P ι S ν

end GlobalTheory.SymBridge
