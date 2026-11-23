import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

open MeasureTheory ValuativeRel Matrix NumberField IsDedekindDomain

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix
open GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SymChain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV

def ordX (R : Ranks) (j : ℕ) : XIx (Fin R.k) (Fin R.t) j ≃ Fin (R.N j) :=
  ((finSumFinEquiv.sumCongr finProdFinEquiv).trans finSumFinEquiv).trans
    (finCongr (by unfold Ranks.N; ring))

def ordZ (R : Ranks) (s : ℕ) (hm : R.m = s + 2) :
    Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) ≃ Fin (R.N R.m - 1 + 0) :=
  ((finSumFinEquiv.sumCongr finProdFinEquiv).trans finSumFinEquiv).trans
    (finCongr (by
      have : R.N R.m = R.k + (s + 1) + (s + 2) * R.t + 1 := by unfold Ranks.N; rw [hm]; ring
      omega))

theorem ordX_d (R : Ranks) (j : ℕ) (i : Fin j) (l : Fin R.t) :
    (ordX R j (.inr (i, l))).val = R.k + j + (l.val + R.t * i.val) := rfl

section Points
variable {E k : Type} [Field E] [Field k] (ι : E →+* k) {a b : ℕ} {I J : Type}

def locMat (e : I ≃ Fin b) (e' : J ≃ Fin a) (x : (Fin a → E) →ₗ[E] (Fin b → E)) : Matrix I J k :=
  Matrix.of fun r s => ι (x (Pi.single (e' s) 1) (e r))

def locVec (e : I ≃ Fin b) (y : Fin b → E) : I → k := fun r => ι (y (e r))

def locRow (e' : J ≃ Fin a) (η : (Fin a → E) →ₗ[E] E) : J → k := fun s => ι (η (Pi.single (e' s) 1))

end Points

def IsCompletionAt {E k : Type} [Field E] [NumberField E] [Field k] [ValuativeRel k] [TopologicalSpace k]
    (P : HeightOneSpectrum (𝓞 E)) (ι : E →+* k) : Prop :=
  DenseRange ι ∧ ∀ a : E, P.valuation E a ≤ 1 ↔ ι a ∈ 𝒪[k]

section Match
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) (σ₀ : X.K →+* ℂ)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k)
  {s : ℕ} (S : SymData k s R.k)

def Tied : Prop :=
  (S.ϖ : k) = ι (qOf P.1 : X.E) ∧
  (∀ a : X.E, IntAt P.1 ((qOf P.1 : X.E) * a) → (S.ψ (ι a) : ℂ) = σ₀ (cst.psi P a)) ∧
  (∀ a : X.E, IntAt P.1 a → cst.psi P (a / (qOf P.1 : X.E)) = psi0P Ch P.1 (redP P.1 a)) ∧
  ∀ i, i < R.m → ∀ (a : X.Eˣ) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ), IntAt P.1 (a : X.E) →
    (c : 𝓞 X.E ⧸ P.1.asIdeal) = redP P.1 (a : X.E) →
      ((S.μ (i + 1) (Units.map ι.toMonoidHom a) : ℂˣ) : ℂ) = σ₀ ((chiP Ch P.1 i c : X.Kˣ) : X.K)

def Deep (s : ℕ) : Prop :=
  ∀ A' B', cst.A ≤ A' → cst.B ≤ B' → ∀ i, i < s →
    E1at Ch sel mu { cst with A := A', B := B' } i P 1 1 = E1at Ch sel mu cst i P 1 1

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k)

def MatchEntries : Prop :=
  ∀ (j c : ℕ) (h : j + 1 + c = s), ∃ C : ℂ, C ≠ 0 ∧ ∀ x : HomE X.E (R.N j) (R.N (j + 1)),
    (S.T (Fin R.t)).entry S.ψ ν j c h 1 1 (locMat ι (ordX R (j + 1)) (ordX R j) x) =
      C * σ₀ (XiAt Ch sel mu cst j P 1 1 x)

def MatchPsi : Prop :=
  ∃ C : ℂ, C ≠ 0 ∧ ∀ (x₀ : HomE X.E (R.N s) (R.N (s + 1))) (y' : Sp X.E (R.N (s + 1))),
    (S.T (Fin R.t)).Psi 1 (locMat ι (ordX R (s + 1)) (ordX R s) x₀) (locVec ι (ordX R (s + 1)) y') =
      C * σ₀ (PsiAt Ch sel mu cst s P 1 x₀ y')

def MatchTop (hm : R.m = s + 2) : Prop :=
  ∃ C : ℂ, C ≠ 0 ∧ ∀ y' : Sp X.E (R.N (s + 1)), (∀ l, IntAt P.1 ((qOf P.1 : X.E) * y' l)) →
    ∀ (x' : HomE X.E (R.N (s + 1)) (R.N R.m - 1 + 0)) (η : Sp X.E (R.N (s + 1)) →ₗ[X.E] X.E),
      (S.T (Fin R.t)).xiTop (box (XIx (Fin R.k) (Fin R.t) (s + 1)) (1 : kˣ)) S.ψ ν (-1)
          (Submodule.Quotient.mk (locVec ι (ordX R (s + 1)) y'))
          (fromRows (locMat ι (ordZ R s hm) (ordX R (s + 1)) x')
            (Matrix.of fun (_ : Unit) => locRow ι (ordX R (s + 1)) η)) =
        C * σ₀ (PhiTop Ch mu cst.sharp s P.1 (x' ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1)))) *
          ftY sel mu cst P η y')

end Match

def Statement : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ)
    (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) (σ₀ : X.K →+* ℂ)
    (s : ℕ) (hm : R.m = s + 2), P.1 ∈ Pr.vGs → cst.sharp = true → Deep Ch sel mu cst P s →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
  ∀ ι : X.E →+* k, IsCompletionAt P.1 ι →
  ∀ S : SymData k s R.k, Tied Ch sel mu cst P σ₀ ι S →
    MatchEntries Ch sel mu cst P σ₀ ι S ν ∧ MatchPsi Ch sel mu cst P σ₀ ι S ∧ MatchTop Ch sel mu cst P σ₀ ι S ν hm

example {E k : Type} [Field E] [Field k] (ι : E →+* k) {a : ℕ} {J : Type} [Fintype J] (e : J ≃ Fin a)
    (η : (Fin a → E) →ₗ[E] E) (y : Fin a → E) : locRow ι e η ⬝ᵥ locVec ι e y = ι (η y) := by
  rw [LinearMap.pi_apply_eq_sum_univ η y, map_sum, ← e.sum_comp]
  refine Finset.sum_congr rfl fun s _ => ?_
  have : (fun j => if e s = j then (1 : E) else 0) = Pi.single (e s) 1 := by
    funext j; simp [Pi.single_apply, eq_comm]
  simp [locRow, locVec, this, mul_comm]

example : epsSg = -1 := rfl

end GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix
