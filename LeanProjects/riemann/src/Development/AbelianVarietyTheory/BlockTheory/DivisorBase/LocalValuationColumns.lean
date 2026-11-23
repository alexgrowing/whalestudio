import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns

open NumberField IsDedekindDomain MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

abbrev Col (cx : Lt1 Dw → ℕ) : Type := Σ f : {f : Lt1 Dw // cx f ≠ 0}, Fin (rk f.1)

abbrev Let (cx : Lt1 Dw → ℕ) : Type := Σ b : Col cx, Fin (rk b.1.1)

def polyH (C : Type) [Field C] (cx : Lt1 Dw → ℕ) : MvPolynomial (Let cx) C :=
  ∏ f : {f : Lt1 Dw // cx f ≠ 0}, MvPolynomial.rename (fun ℓ : (Σ _ : Fin (rk f.1), Fin (rk f.1)) =>
    (⟨⟨f, ℓ.1⟩, ℓ.2⟩ : Let cx)) (detPow C (rk f.1) (cx f.1))

def blockCols (cx : Lt1 Dw → ℕ) : ℕ := ∑ f : {f : Lt1 Dw // cx f ≠ 0}, 2 * rk f.1

variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

section Chart

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (Ch : IntegralChartA3 Xo c T io y)
  {p : ℕ} [Fact p.Prime] (X : ValExt T p) (cx : Lt1 Dw → ℕ) {n : ℕ}
  (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V)

def expH : (Σ _ : Col cx, Fin (chD Ch.ch)) → MvPowerSeries (Let cx) X.C :=
  expAlong (fun _ : Col cx => fgl Ch X) (fun b => frame Ch X b.1.1)

def colPt : Fin n × Fin (chD Ch.ch) → MvPowerSeries (Let cx) X.C := fun q =>
  subst (fun e : Fin (chD Ch.ch) => ∑ ℓ : Let cx,
    (jX X (B ℓ.1.1.1 ℓ.1.2 q.1) * frame Ch X ℓ.1.1.1 ℓ.2 e) • (MvPowerSeries.X ℓ : MvPowerSeries (Let cx) X.C))
    (expOf (fgl Ch X) q.2)

def nuH_vp : EReal := depth (fun _ : Col cx => fgl Ch X) (fun b => frame Ch X b.1.1) (polyH X.C cx)

def nabX (k : ℕ) (g : PS X.C n (chD Ch.ch)) : X.C :=
  letI := io.toAlgebra
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  letI : Algebra ℚ X.C := DivisionRing.toRatAlgebra
  nabValN Ch.ch.B X.C (MvPowerSeries.map X.ιF Ch.ch.h) H.w0 k g (fun ℓ : LtN Dw n => ℓ.2.2)
    (fun ℓ => lieVec Ch X ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map X.ιF (polyT B cx))

def nuLocX_vp (k : ℕ) : EReal :=
  ⨅ g : {g : PS X.C n (chD Ch.ch) // MvIsInt (vX_vp X) g}, toE (vX_vp X (nabX Ch X cx B k g.1))

def Restricts (g : PS X.C n (chD Ch.ch)) (f : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) X.C) : Prop :=
  subst (colPt Ch X cx B) g = subst (expH Ch X cx) f

def Trivial : Prop :=
  (∀ g, MvIsInt (vX_vp X) g → ∃ f, MvIsInt (vX_vp X) f ∧ Restricts Ch X cx B g f) ∧
  (∀ f, MvIsInt (vX_vp X) f → ∃ g, MvIsInt (vX_vp X) g ∧ Restricts Ch X cx B g f) ∧
  ∃ U : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) X.C, MvIsInt (vX_vp X) U ∧ constantCoeff U = 1 ∧
    ∀ (k : ℕ) g f, Restricts Ch X cx B g f →
      nabX Ch X cx B k g = derivAt0 (polyH X.C cx) (subst (expH Ch X cx) (f * U ^ k))

def DepthEq : Prop :=
  nuH_vp Ch X cx = nuP p y cx ∧
  (∀ k : ℕ, nuLocX_vp Ch X cx B k = nuP p y cx) ∧
  (∀ k e : ℕ, vV T.V (p : T.Fr) = e → nuLocOf Ch e k (polyT B cx) = nuP p y cx) ∧
  0 ≤ nuP p y cx

end Chart

variable (Dw c) in

def ColsExist (p : ℕ) (la : PointsOfFlagModel.abelian₂ p c) : Prop :=
  ∀ (cx : Lt1 Dw → ℕ) (n : ℕ), blockCols cx ≤ n →
    ∃ x : ℕ → ∀ f : Lt1 Dw, Fin (rk f) → Fin n → 𝓞 E,
      ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e →
        ∃ B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V, IsCols c T io p cx B ∧
          ∀ (N : ℕ) (f : Lt1 Dw) (b : Fin (rk f)) (j : Fin n), ∃ z : T.V,
            io (embK c f.1 (x N f b j)) = algebraMap T.V T.Fr (B f b j + (p : T.V) ^ N * z)

variable (Dw c) in

def ColsHarmonic (p : ℕ) (la : PointsOfFlagModel.abelian₂ p c) : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ), (∀ τ, Antitone fun i => a (τ, i)) →
      ∀ (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), IsCols c T io p (gap Dw a) B →
        polyT B (gap Dw a) ∈ FFV (Dw := Dw) T a n

variable (Xo c) in

def LocalDepth (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e →
    ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ) (n : ℕ)
      (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), IsCols c T io p cx B →
      Trivial Ch X cx B ∧ DepthEq Ch X cx B

variable (Xo c) in

def ChoiceOfP : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) → ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c),
    ColsExist Dw c p la ∧ ColsHarmonic Dw c p la ∧ LocalDepth Xo c p la

example {p : ℕ} [Fact p.Prime] {la : PointsOfFlagModel.abelian₂ p c} (h : LocalDepth Xo c p la) {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ}
    (ho : OverLa la.1 T.V io e) {y : IntFr Xo c T io} (Ch : IntegralChartA3 Xo c T io y) {a : (E →+* ℂ) × ℕ → ℕ}
    (ha : ∀ τ, Antitone fun i => a (τ, i)) {n : ℕ} {B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V}
    (hB : IsCols c T io p (gap Dw a) B) (k ep : ℕ) (hp : vV T.V (p : T.Fr) = ep) :
    nuLocC Ch ep k a n ≤ nuP p y (gap Dw a) := by
  obtain ⟨X⟩ := nonempty_valExt_of_overLa (p := p) la ho
  rw [← (h T io e ho y Ch X _ n B hB).2.2.2.1 k ep hp]
  exact nuLocC_le_nuLocOf Ch ep k ha hB

omit [StarRing (𝓞 E)] in

example (C : Type) [Field C] : polyH (Dw := Dw) C (fun _ => 0) = 1 := by
  have : IsEmpty {f : Lt1 Dw // (fun _ => 0 : Lt1 Dw → ℕ) f ≠ 0} := ⟨fun f => f.2 rfl⟩
  simp [polyH]

end GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns
