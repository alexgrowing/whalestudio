import Mathlib
import Formalism.LocalRingCardinality.DataErr

noncomputable section

open scoped BigOperators
open Classical
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G

namespace PI.EntAtD

instance instFactRes (D : D7) (w : D.what₂.places.Pl) : Fact (D.what₂.places.resChar w).Prime :=
  ⟨D.what₂.places.resChar_prime w⟩

abbrev Pl (D : D7) : Type := Bool × HH D

def expS (K : Type*) [Field K] [CharZero K] {τ : Type*} (f : MvPowerSeries τ K) : MvPowerSeries τ K :=
  PowerSeries.subst f (PowerSeries.exp K)

section Kmap

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ)

abbrev XZ (Lt : Type) (N0 N1 : ℕ) : Type := (Lt × ℕ × Fin N0) ⊕ (Lt × Fin N0 × Fin N1)

def minorXZ (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) : MvPolynomial (XZ Lt N0 N1) ℤ :=
  Matrix.det (Matrix.of fun i k : Fin p => ∑ a : Fin N0,
    MvPolynomial.X (Sum.inl (s, (i : ℕ), a)) * MvPolynomial.X (Sum.inr (s, a, I k)))

def ColChoice (nu : Lt → YoungDiagram) : Type :=
  ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N1

def Gxz (nu : Lt → YoungDiagram) (I : ColChoice N1 nu) : MvPolynomial (XZ Lt N0 N1) ℤ :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), minorXZ N0 N1 s ((nu s).colLen c) (I s c)

def applyAt0 (l : ℕ) [Fact l.Prime] (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] :=
  ∑ μ ∈ P.support, MvPolynomial.monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).1
    (((MvPolynomial.coeff μ P : ℤ) : ℂ_[l]) *
      ((Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun _ n => (n.factorial : ℂ_[l])) *
      MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp μ).2 Th)

def KvalGe (l : ℕ) [Fact l.Prime] (nu : Lt → YoungDiagram)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (B : ℝ) : Prop :=
  ∀ (I : ColChoice N1 nu) (m : Lt × ℕ × Fin N0 →₀ ℕ),
    ‖MvPolynomial.coeff m (applyAt0 N0 N1 l Th (Gxz N0 N1 nu I))‖ ≤ (l : ℝ) ^ (-B)

end Kmap

def ShapeD (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (Th : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]) : Prop :=
  ∃ S : ℂ_[p], ‖S‖ ≤ (p : ℝ) ^ ((1 : ℝ) / 2) ∧ ∃ ut : HH D → ℂ_[p], (∀ t, ‖ut t‖ ≤ 1) ∧
    ∃ sg' : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p],
      (∀ m, ‖(m.prod fun _ n => (n.factorial : ℂ_[p])) * MvPowerSeries.coeff m sg'‖ ≤ 1) ∧
      Th = expS ℂ_[p] (-(S • ∑ t : HH D, ut t • ∑ a : Fin N0, ∑ b : Fin N1,
        (MvPowerSeries.X ((false, t), a, b) * MvPowerSeries.X ((true, t), a, b) :
          MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]))) * sg'

def LevelFree {D : D7} (Dx : DivX D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) : Prop :=
  D.what₂.places.resChar w ≠ (D.mem u).A.T ∧ D.what₂.places.resChar w ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) ∧
    D.what₂.places.resChar w ∉ Dx.Qp μ

def EntAtD : Prop :=
  ∀ (D : D7) (Dx : DivX D) (nu : D.what₂.Word → ℕ → Pl D → YoungDiagram),
    (∀ u i, i < D.R.m → ∀ z r, (((nu u i z).rowLen r : ℕ) : ℝ) =
      if r < D.R.N i then DV.nuRow D u (i + 1) (tauPl D z) r else 0) →
    (∀ u i z, (nu u i z).colLen 0 ≤ D.R.N i) →
    ∀ (Th : ∀ u μ (w : D.what₂.places.Pl) (i : ℕ), (D.chTw u μ).cls i → (D.chTw u μ).cls (i + 1) →
      MvPowerSeries (Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[D.what₂.places.resChar w]),
    (∀ u μ (w : D.what₂.places.Pl), LevelFree Dx u μ w → D.host.cls (D.what₂.places.resChar w) = PrimeClass.ramD →
      ∀ i < D.R.m, ∀ L L', ShapeD D (D.what₂.places.resChar w) (Th u μ w i L L')) →
    ∀ u μ (w : D.what₂.places.Pl), LevelFree Dx u μ w → D.host.cls (D.what₂.places.resChar w) = PrimeClass.ramD →
      ∀ i < D.R.m, ∀ (L : (D.chTw u μ).cls i) (L' : (D.chTw u μ).cls (i + 1)),
        KvalGe (D.R.N i) (D.R.N (i + 1)) (D.what₂.places.resChar w) (nu u i) (Th u μ w i L L')
          (-((∑ t : HH D, ctD D u (i + 1) t) / 2))

end PI.EntAtD
