import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.CharTied

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointHilbertLifts

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host Neutral.B1
open scoped Matrix

section Adelic

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

abbrev Ad : Type := FiniteAdeleRing (𝓞 H.E) H.E

def AdConj (x y : Ad H) : Prop :=
  (x, y) ∈ closure (Set.range fun a : H.E => (algebraMap H.E (Ad H) a, algebraMap H.E (Ad H) (H.conj a)))

def IsUnitaryAd {N : ℕ} (g : GL (Fin N) (Ad H)) : Prop :=
  ∀ a b, AdConj H ((g : Matrix (Fin N) (Fin N) (Ad H)) a b) (((g⁻¹ : GL (Fin N) (Ad H)) : Matrix (Fin N) (Fin N) (Ad H)) b a)

def IsHilbLift (x : Ideles H.E) (d : Ad H) : Prop :=
  IsFinIdele x ∧ ∃ xb : Ad H, AdConj H (x : AdeleRing (𝓞 H.E) H.E).2 xb ∧ (x : AdeleRing (𝓞 H.E) H.E).2 = d * xb

def IsTildeVal (μ χ : HChar H.E) (a n : ℤ) (d : Ad H) (z : ℂ) : Prop :=
  ∃ x : Ideles H.E, IsHilbLift H x d ∧ z = (((μ.1 x) ^ a * (χ.1 x) ^ n : ℂˣ) : ℂ)

def StabAt (l : ℕ) {N : ℕ} (M : Matrix (Fin N) (Fin N) (Ad H)) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 H.E), OverP H l v →
    (∀ a b, M a b v ∈ v.adicCompletionIntegers H.E) ∧ Valued.v (M.det v) = 1

def IsBasisAt (l : ℕ) {N : ℕ} (g : GL (Fin N) (Ad H)) (b : Matrix (Fin N) (Fin N) H.E) : Prop :=
  StabAt H l (((g⁻¹ : GL (Fin N) (Ad H)) : Matrix (Fin N) (Fin N) (Ad H)) * b.map (algebraMap H.E (Ad H)))

end Adelic

section abelian₂

variable {l : ℕ} [Fact l.Prime] (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[l])

def IntAt (z : ℂ) : Prop := ∃ h : z ∈ algebraicClosure ℚ ℂ, ‖lam ⟨z, h⟩‖ ≤ 1

def UnitAt (z : ℂ) : Prop := ∃ h : z ∈ algebraicClosure ℚ ℂ, ‖lam ⟨z, h⟩‖ = 1

def IsLatFrame {R : Ranks} (H : Formalism.BasicNotions.Host R) (φ : H.E →+* ℂ) {N : ℕ} (g : GL (Fin N) (Ad H))
    (y : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∃ (b : Matrix (Fin N) (Fin N) H.E) (k : Matrix (Fin N) (Fin N) ℂ),
    IsBasisAt H l g b ∧ (∀ a a', IntAt lam (k a a')) ∧ UnitAt lam k.det ∧ y = b.map φ * k

end abelian₂

def LamOver (D : D7) (w : D.what₂.places.Pl) [Fact (D.what₂.places.resChar w).Prime]
    (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w]) : Prop :=
  ∀ x : D.what₂.LL, IntAt lam (D.what₂.embLL x) ↔ 0 ≤ D.what₂.places.val w x

abbrev Reps (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) : Type :=
  ∀ i, (D.chTw u μ).cls i → GL (Fin (D.R.N i)) (Ad D.host)

abbrev Frames (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) : Type :=
  ∀ i, (D.chTw u μ).Y i → D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ

def RepTie (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) (g : Reps D u μ) : Prop :=
  ∀ i, i ≤ D.R.m → ∀ c, IsUnitaryAd D.host (g i c)

def RhoTie (D : D7) (C : CharFrame D) {nch : NChoice D} (Tp : TupTied D C nch) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (g : Reps D u μ) : Prop :=
  ∀ (i : ℕ) (hi : i < D.R.m),
    (∀ c, IsTildeVal D.host (Tp.tup μ ⟨i, hi⟩) C.chiPsi (-1) (-((D.R.N (i + 1) / 2 : ℕ) : ℤ))
      (g i c : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) (Ad D.host)).det ((D.chTw u μ).rhoDet i c)) ∧
    (∀ c', IsTildeVal D.host (Tp.tup μ ⟨i, hi⟩) C.chiPsi 1 ((D.R.N i / 2 : ℕ) : ℤ)
      (g (i + 1) c' : Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) (Ad D.host)).det ((D.chTw u μ).rhoDet' i c'))

def FrameTie (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) (fr : Frames D u μ) : Prop :=
  ∀ i, i ≤ D.R.m →
    Function.Injective (fr i) ∧ (∀ M, M ∈ Set.range (fr i) ↔ ∀ τ, (M τ).det ≠ 0) ∧
      ∀ y τ, (D.chTw u μ).de i y τ = (fr i y τ).det

def PrimeToLevels (D : D7) {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (l : ℕ) : Prop :=
  l ≠ (D.mem u).A.T ∧ (∀ k, l ≠ D.host.g k) ∧ ∀ v, OverP D.host l v → (Tp.xi μ).UnrAt v

def eps (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) : ℂ :=
  (D.chTw u μ).rhoDet i c * (D.chTw u μ).rhoDet' i c'

def epsFr (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1))
    (y : (D.chTw u μ).Y i) (y' : (D.chTw u μ).Y (i + 1)) : ℂ :=
  eps D u μ i c c' * (∏ τ, (D.chTw u μ).de i y τ ^ (D.chTw u μ).sSharp i τ) *
    (∏ τ, (D.chTw u μ).de (i + 1) y' τ ^ (D.chTw u μ).sDiv i τ)⁻¹

def UnUnit_at (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (g : Reps D u μ) (fr : Frames D u μ) : Prop :=
  RepTie D u μ g → RhoTie D C Tp u μ g → FrameTie D u μ fr →
  ∀ (w : D.what₂.places.Pl) [Fact (D.what₂.places.resChar w).Prime]
    (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w]), LamOver D w lam →
    PrimeToLevels D Tp u μ (D.what₂.places.resChar w) →
    ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1))
      (y : (D.chTw u μ).Y i) (y' : (D.chTw u μ).Y (i + 1)),
      (∀ τ, IsLatFrame lam D.host (embTau D τ) (g i c) (fr i y τ)) →
      (∀ τ, IsLatFrame lam D.host (embTau D τ) (g (i + 1) c') (fr (i + 1) y' τ)) →
      UnitAt lam (epsFr D u μ i c c' y y')

def UnUnitBase_at (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (g : Reps D u μ) : Prop :=
  RepTie D u μ g → RhoTie D C Tp u μ g →
  ∀ (w : D.what₂.places.Pl) [Fact (D.what₂.places.resChar w).Prime]
    (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w]), LamOver D w lam →
    PrimeToLevels D Tp u μ (D.what₂.places.resChar w) →
    ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
      StabAt D.host (D.what₂.places.resChar w)
        (((g i c)⁻¹ : GL (Fin (D.R.N i)) (Ad D.host)) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) (Ad D.host)) →
      StabAt D.host (D.what₂.places.resChar w)
        (((g (i + 1) c')⁻¹ : GL (Fin (D.R.N (i + 1))) (Ad D.host)) :
          Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) (Ad D.host)) →
      UnitAt lam (eps D u μ i c c')

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointHilbertLifts
