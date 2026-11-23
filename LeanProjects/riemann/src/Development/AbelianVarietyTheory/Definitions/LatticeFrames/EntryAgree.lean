import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section
namespace GlobalTheory.TwBridge
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymBridge

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k)

structure TwData (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] where
  ϖ : kˣ
  unif : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ
  ψ : AddChar k Circle
  cont : Continuous ψ
  cond : HasConductor ψ 1
  δ : kˣ →* ℂˣ
  tame : IsTame δ
  η : ℕ → kˣ →* ℂˣ
  unr : ∀ j, IsUnram (η j)
  sg : ℂ

variable (s : ℕ) (W : TwData k)

abbrev TwData.T (R : Ranks) : Chain k s (XIx (Fin R.k) (Fin R.t)) (Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2)) :=
  twistChain s (Fin R.t) (Fin R.k) W.δ W.tame W.η

structure AtTwist : Prop where
  nmem : P.1 ∉ Pr.vGs
  steps : R.m = s + 2
  compl : IsCompl P.1 (qOf P.1) ι W.ϖ
  psi : ∀ a, IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * a) → (W.ψ (ι a) : ℂ) = σ₀ (cst.psi P a)
  del : ∀ a (u : kˣ), IntAt P.1 a → IsUnit (redP P.1 a) → (u : k) = ι a →
    (W.δ u : ℂ) = (σ₀ (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) a))⁻¹
  mu : ∀ i, i < R.m → ((W.η (i + 1) * W.δ) W.ϖ : ℂ) = σ₀ (cst.muq (i + 1) P)
  sq : σ₀ (cst.sq P) = W.sg * (Real.sqrt (qOf P.1) : ℂ)

def IsOrdY {j c : ℕ} (e : XIx (Fin R.k) (Fin R.t) j ⊕ Fin c ≃ Fin (R.N j + cOf R j)) : Prop := IsOrd (yPos xPos (R.N j)) e

def IsGL {j c : ℕ} (γ : AutY X R j) (g : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin c) k) : Prop :=
  ∃ e : XIx (Fin R.k) (Fin R.t) j ⊕ Fin c ≃ Fin (R.N j + cOf R j), IsOrdY e ∧ g.val = toLoc ι e e γ.toLinearMap

def sgn {j : ℕ} (γ : AutY X R j) (n : ℕ) : ℂ := W.sg ^ (LocE.vP P.1 (qOf P.1) ((LinearEquiv.det γ : X.Eˣ) : X.E) * n)

def PhiAgree : Prop :=
  (∀ j c (h : j + c = s) (e' : XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1) ≃ Fin (R.N j + cOf R j))
    (e : XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin c ≃ Fin (R.N (j + 1) + cOf R (j + 1))), IsOrdY e' → IsOrdY e → ∀ x,
      (W.T s R).Phi j c h (toLoc ι e e' x) = σ₀ (PhiAt Ch mu cst.sharp j P.1 x)) ∧
  ∀ (e' : XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0 ≃ Fin (R.N (s + 1) + cOf R (s + 1)))
    (e : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) ≃ Fin (R.N R.m - 1 + 0)), IsOrdY e' → IsOrd zPos e → ∀ x,
      (W.T s R).PhiTop (toLoc ι e e' x) = σ₀ (PhiTop Ch mu cst.sharp s P.1 x)

def LevelAgree : Prop :=
  ∀ j c (h : j + c = s + 1) (γ : AutY X R j) g, IsGL ι γ g →
    (g ∈ ((W.T s R).lev j c h).J ↔ γ ∈ Jat (Pr := Pr) cst.sharp j P.1) ∧
    (∀ hg : g ∈ ((W.T s R).lev j c h).J,
      (((W.T s R).lev j c h).lam ⟨g, hg⟩ : ℂ) = σ₀ (lamRow Ch mu cst.sharp j P.1 γ.toLinearMap)) ∧
    (1 ≤ c → ∀ (γ' : AutY X R j) g', IsGL ι γ' g' →
      (SameDC (Pr := Pr) cst.sharp j P.1 γ γ' ↔ DoubleCoset.mk (GlobalTheory.RootEx.R k _ c 1) ((W.T s R).lev j c h).J g =
        DoubleCoset.mk (GlobalTheory.RootEx.R k _ c 1) ((W.T s R).lev j c h).J g'))

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k)

def VolAgree : Prop :=
  ∀ j c (h : j + (c + 1) = s + 1) (γ : AutY X R j) g, IsGL ι γ g →
    ((volNat ν 1 (Cgrp ((W.T s R).lev j (c + 1) h).J g) : ℝ) : ℂ) = σ₀ (Loc.volN X.K (Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) γ)
      (Loc.N1 X.E (R.N j) (cOf R j) ⊓ stabL X.E _ (lamYat (Pr := Pr) j P.1))) ∧
    (prCat (Pr := Pr) cst.sharp j P.1 γ ≤ GLint X.E (R.N j) P.1 →
      ∀ m : Measure (GL (XIx (Fin R.k) (Fin R.t) j) k), m.IsHaarMeasure → m (KO k (XIx (Fin R.k) (Fin R.t) j)) = 1 →
        (m (prX (Cgrp ((W.T s R).lev j (c + 1) h).J g))).toReal⁻¹ =
          ((prCat (Pr := Pr) cst.sharp j P.1 γ).relIndex (GLint X.E (R.N j) P.1) : ℝ))

def SumAgree : Prop :=
  ∀ j c (h : j + 1 + c = s) (a : AutY X R j) (b : AutY X R (j + 1)) g g', IsGL ι a g → IsGL ι b g' →
    (∀ x ∈ lamYat (Pr := Pr) (R := R) j P.1, a⁻¹ x ∈ lamYat (Pr := Pr) (R := R) j P.1 ∧
      ((qOf P.1 : X.E) ^ j) • a x ∈ lamYat (Pr := Pr) (R := R) j P.1) →
    (∀ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1, b⁻¹ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1 ∧
      ((qOf P.1 : X.E) ^ (j + 1)) • b x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1) →
    2 * (R.m - 1) + 1 ≤ cst.D P → ∃ A₀ B₀ : ℕ, ∀ A' B', A₀ ≤ A' → B₀ ≤ B' →
      ∀ (e' : XIx (Fin R.k) (Fin R.t) j ≃ Fin (R.N j)) (e : XIx (Fin R.k) (Fin R.t) (j + 1) ≃ Fin (R.N (j + 1))),
        IsOrd xPos e' → IsOrd xPos e → ∀ x,
          GlobalTheory.StepData.flat W.ψ ν ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega)) g g' (toLoc ι e e' x) =
            sgn sel mu P W a (R.N (j + 1) + cOf R (j + 1)) * sgn sel mu P W b (R.N j + cOf R j) *
              σ₀ (E1at Ch sel mu { cst with A := A', B := B' } j P a b x)

variable (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

def IdxProd : Prop :=
  ∀ j (b b' : L.β j) (P : rowSG Pr sel mu), SameDC (Pr := Pr) cst.sharp j P.1 (L.h j b P) (L.h j b' P) → L.h j b P = L.h j b' P

def EntryAgree : Prop :=
  ∀ j c (h : j + 1 + c = s) (al : L.β j) (be : L.β (j + 1)) g g', IsGL ι (L.h j al P) g → IsGL ι (L.h (j + 1) be P) g' →
    ∀ (e' : XIx (Fin R.k) (Fin R.t) j ≃ Fin (R.N j)) (e : XIx (Fin R.k) (Fin R.t) (j + 1) ≃ Fin (R.N (j + 1))),
      IsOrd xPos e' → IsOrd xPos e → ∀ x,
        (W.T s R).entry W.ψ ν j c h g g' (toLoc ι e e' x) =
          sgn sel mu P W (L.h j al P) (R.N (j + 1) + cOf R (j + 1)) * sgn sel mu P W (L.h (j + 1) be P) (R.N j + cOf R j) *
            σ₀ (XiAt Ch sel mu cst j P (L.h j al P) (L.h (j + 1) be P) x)

def LastAgree : Prop :=
  (∀ (al : L.β s) g, IsGL ι (L.h s al P) g →
    (∀ x₀ y, ((W.T s R).Psi g x₀ y ≠ 0 → y ∈ box _ (W.ϖ ^ cst.M)⁻¹) ∧
      ∀ z ∈ box _ (W.ϖ ^ cst.M), (W.T s R).Psi g x₀ (y + z) = (W.T s R).Psi g x₀ y) ∧
    ∀ (e' : XIx (Fin R.k) (Fin R.t) s ≃ Fin (R.N s)) (e : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))),
      IsOrd xPos e' → IsOrd xPos e → ∀ x₀ y',
        (W.T s R).Psi g (toLoc ι e e' x₀) (fun a => ι (y' (e a))) =
          sgn sel mu P W (L.h s al P) (R.N (s + 1) + cOf R (s + 1)) * σ₀ (PsiAt Ch sel mu cst s P (L.h s al P) x₀ y')) ∧
  ∀ (e' : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1)))
    (e : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) ⊕ Unit ≃ Fin (R.N R.m)),
    IsOrd xPos e' → IsOrd (Sum.elim zPos fun _ => R.N R.m - 1) e →
      ∀ (y : HomE X.E (R.N (s + 1)) (R.N R.m)) (y' : Sp X.E (R.N (s + 1))),
        (∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y' l)) →
        (W.T s R).xiTop (box _ (W.ϖ ^ cst.M)) W.ψ ν (-1) (Submodule.Quotient.mk fun a => ι (y' (e' a))) (toLoc ι e e' y) =
          σ₀ (PhiTop Ch mu cst.sharp s P.1 (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1)))) *
            ftY sel mu cst P (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y) y')

def RepsAgree : Prop :=
  (∀ j, j ≤ s → Nonempty (L.β j)) → (W.T s R).IsRepSystem (fun j _ _ => {g | ∃ b : L.β j, IsGL ι (L.h j b P) g}) W.ψ ν

def IdxIsProd : Prop :=
  ∀ j, j ≤ s → ∀ hh : rowSG Pr sel mu → AutY X R j, (∀ P, ∃ b : L.β j, L.h j b P = hh P) → ∃! b : L.β j, ∀ P, L.h j b P = hh P

end GlobalTheory.TwBridge
