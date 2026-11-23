import Formalism.LocalToGlobal.CharacterGerms.CoefficientIdentitySelfConjugate
import Formalism.LocalToGlobal.CharacterGerms.RowTiePHStabSelf
import Formalism.LocalToGlobal.CharacterGerms.MaximalOfValuationGeOne

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def pairSubst {τ : Type} (a b : κ → MvPowerSeries τ C) : Fin 2 × κ → MvPowerSeries τ C :=
  fun q => if q.1 = 0 then a q.2 else b q.2

def hAt (X : RawChart C d I κ) {τ : Type} (a b : κ → MvPowerSeries τ C) : MvPowerSeries τ C :=
  MvPowerSeries.subst (pairSubst a b) X.h

def IsPt (V : VF C) {τ : Type} (a : κ → MvPowerSeries τ C) : Prop :=
  ∀ i, MvPowerSeries.constantCoeff (a i) = 0 ∧ IntS V (a i)

def BiInt (X : RawChart C d I κ) (V : VF C) : Prop :=
  ∀ (τ : Type) [Finite τ] (n : ℕ) (a : ℕ → κ → MvPowerSeries τ C) (s c : κ → MvPowerSeries τ C),
    (∀ k, IsPt V (a k)) → IsPt V s → IsPt V c →
    (∀ i, MvPowerSeries.subst s (X.lg i) = ∑ k ∈ Finset.range n, MvPowerSeries.subst (a k) (X.lg i)) →
    IntS V (mvExp (∑ k ∈ Finset.range n, hAt X (a k) c - hAt X s c)) ∧
      IntS V (mvExp (∑ k ∈ Finset.range n, hAt X c (a k) - hAt X c s))

structure Basic (X : RawChart C d I κ) (V : VF C) : Prop where
  lg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0
  exlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = (MvPowerSeries.X i : MvPowerSeries κ C)
  lin : ∀ i (μ : κ →₀ ℕ), μ.degree ≤ 1 →
    MvPowerSeries.coeff μ (X.lg i) = MvPowerSeries.coeff μ (MvPowerSeries.X i : MvPowerSeries κ C)
  axis0 : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → MvPowerSeries.coeff e X.h = 0
  axis1 : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 1) → MvPowerSeries.coeff e X.h = 0
  uint : ∀ g c i, V.Ge 0 (X.u g c i)
  hmis : ∀ (g : Fin 2) (c : I g) (q : JJ I g), X.ty g c ≠ X.ty (1 - g) q →
    V.Ge 0 (X.sg1 (X.u g c) (X.u (1 - g) q))

def NormRel (X : RawChart C d I κ) (l n : ℕ) (ζ : C) (γ δ : κ → PowerSeries C) : Prop :=
  ∀ i, PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (alongCv δ (X.lg i)) =
    ∑ k ∈ Finset.range l, PowerSeries.rescale (ζ ^ k) (alongCv γ (X.lg i))

def phi (X : RawChart C d I κ) (l : ℕ) (ζ : C) (γ δ : κ → PowerSeries C) (v : κ → C) : PowerSeries C :=
  PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (l ^ 2)) (alongCv δ (X.sg v)) -
    ∑ k ∈ Finset.range l, PowerSeries.rescale (ζ ^ k) (alongCv γ (X.sg v))

def StepA (X : RawChart C d I κ) (V : VF C) (H : ∀ g, X.CartHyp V g) : Prop :=
  ∀ ζ : C, IsPrimitiveRoot ζ V.l → ∀ (g : Fin 2) (a : ZMod d) (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C),
    (RawChart.cart (H g)).Good a w x → (∀ c, V.MM ((RawChart.cart (H g)).V2 x c)) →
    ∃ γ δ : κ → PowerSeries C, IsCv V γ ∧ IsCv V δ ∧ NormRel X V.l (V.l ^ 2) ζ γ δ ∧
      (∀ i, V.MM (PowerSeries.coeff 1 (δ i))) ∧
      ∀ q : JJ I g, V.Ge 0 ((RawChart.cart (H g)).c0' x q) ∧
        V.MM (PowerSeries.coeff V.l (phi X V.l ζ γ δ (X.u (1 - g) q)) - (RawChart.cart (H g)).c0' x q) ∧
        V.MM (PowerSeries.coeff (V.l ^ 2) (phi X V.l ζ γ δ (X.u (1 - g) q)) - (V.l : C) * x 2 (Sum.inr q))

def StepB (X : RawChart C d I κ) (V : VF C) : Prop :=
  ∀ ζ : C, IsPrimitiveRoot ζ V.l → ∀ (g : Fin 2) (q : JJ I g),
    ∃ (z ε : κ → PowerSeries C) (m : JJ I g → C), IsCv V z ∧ IsCv V ε ∧ NormRel X V.l V.l ζ z ε ∧
      (∀ i, PowerSeries.coeff 1 (z i) = X.u (1 - g) q i) ∧
      (∀ i, PowerSeries.coeff 1 (ε i) = ∑ q' : JJ I g, m q' * X.u (1 - g) q' i) ∧ ∀ q', V.Ge 0 (m q')

def LemC (X : RawChart C d I κ) (V : VF C) : Prop :=
  ∀ ζ : C, IsPrimitiveRoot ζ V.l → ∀ γ δ z ε : κ → PowerSeries C, IsCv V γ → IsCv V δ → IsCv V z → IsCv V ε →
    NormRel X V.l (V.l ^ 2) ζ γ δ → NormRel X V.l V.l ζ z ε → (∀ i, V.MM (PowerSeries.coeff 1 (δ i))) →
    V.MM (PowerSeries.coeff V.l (phi X V.l ζ γ δ fun i => PowerSeries.coeff 1 (z i)) ^ V.l -
      PowerSeries.coeff (V.l ^ 2) (phi X V.l ζ γ δ fun i => PowerSeries.coeff 1 (ε i)))

end SelfConjCharts

def GoodCurveClosed : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ), SelfConjCharts.Basic X V → ∀ H : ∀ g, X.CartHyp V g, SelfConjCharts.StepA X V H

def OtherGroupCurvesClosed : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ), SelfConjCharts.Basic X V → (∀ g, X.CartHyp V g) → SelfConjCharts.StepB X V

def MixedCoefficientClosed : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ), SelfConjCharts.Basic X V → SelfConjCharts.BiInt X V → SelfConjCharts.LemC X V

def BiadditiveOnColumns : Prop := AllSelf fun _ _ V _ _ _ _ X => SelfConjCharts.BiInt X V

end Formalism.L2.FormalSeriesBounds
