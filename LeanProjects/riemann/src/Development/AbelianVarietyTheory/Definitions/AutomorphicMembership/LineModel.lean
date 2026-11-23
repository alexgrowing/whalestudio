import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM

namespace GlobalTheory.ShFam.Pad

structure FinLB (X : Scheme.{0}) : Type where
  n : ℕ
  U : Fin n → X.Opens
  g : ∀ i k, Γ(X, U i ⊓ U k)ˣ
  isLB : LB.IsLB ⟨Fin n, U, g⟩

abbrev FinLB.lb {X : Scheme.{0}} (L : FinLB X) : LB X := ⟨Fin L.n, L.U, L.g⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

structure LineModel (Z : Mdl Y i₀) (b : Bool) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) (x : Letter Dw) : Type where
  L : FinLB Z.X
  r : ∀ (a : Fin Z.m) (i : Fin L.n), Γ(Z.X, (Z.U a).1 ⊓ L.U i)ˣ
  trans : ∀ (k : Type) [Field k] (w : Sp k ⟶ Z.X) a i i', ⊤ ≤ w ⁻¹ᵁ ((Z.U a).1 ⊓ (L.U i ⊓ L.U i')) →
    valF w _ (r a i').val = valF w _ (L.g i i').val * valF w _ (r a i).val
  chart : ∀ (k : Type) [Field k] a a' i (φ : Γ(Z.X, (Z.U a).1) →+* k) (φ' : Γ(Z.X, (Z.U a').1) →+* k)
    (cf : Fin (Dw.mult x.1) → k), spMap φ ≫ Z.chart a = spMap φ' ≫ Z.chart a' →
    ⊤ ≤ (spMap φ ≫ Z.chart a) ⁻¹ᵁ L.U i → (∀ m, x.2 < m → cf m = 0) →
    IsCombAtG (Y Z.i).t (spMap φ ≫ Z.chart a ≫ Z.π) ((Z.fr a).bc φ x.1) cf ((Z.fr a').bc φ' x.1 x.2) →
    valF (spMap φ ≫ Z.chart a) _ (r a i).val = valF (spMap φ ≫ Z.chart a) _ (r a' i).val * cf x.2
  norm : ∀ (y : Z.Pt) a i (φ : Γ(Z.X, (Z.U a).1) →+* ↥y.C.S), spMap φ ≫ Z.chart a = y.gen → ⊤ ≤ y.z ⁻¹ᵁ L.U i →
    Real.log ‖valF y.gen _ (r a i).val‖ + lnStep (Y Z.i).t (y.gen ≫ Z.π) ((Z.fr a).bc φ) p b st = 0

structure admitted (Y : LocalSystem Xo p W) (i₀ : Idx H p) : Type where
  Z : Mdl Y i₀
  full : ∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ
  n : ℕ
  lvl : Z.i.l.M = i₀.l.M ∧ Z.i.l.Mb = i₀.l.Mb ∧ Z.i.l.A = i₀.l.A * p ^ n
  line : ∀ (b : Bool) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) (x : Letter Dw), letterOf Dw st = some x → LineModel Z b st x

variable {D : D7}

open Classical in

def placeW (D : D7) (p : ℕ) [Fact p.Prime] (la : PlL D p) (jc : DV.KW p →+* ℂ) : ValuationSubring ℂ :=
  Classical.epsilon fun W => (∀ x : D.what₂.LL, D.what₂.embLL x ∈ W ↔ la.1.valuation D.what₂.LL x ≤ 1) ∧
    ∀ a : DV.KW p, jc a ∈ W ↔ a ∈ (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p)).range

abbrev AdmAt {A : Amb D} {N j : ℕ} (S : Sig A N j) (κ : Lv A) {p : ℕ} (hp : p.Prime) {W : ValuationSubring ℂ}
    (hW : (p : ℂ) ∈ W.nonunits) : Type :=
  admitted (S.sys.Y p W hp hW) ⟨κ.l, κ.c, κ.good p hp⟩

def AdmEx {A : Amb D} {N j : ℕ} (S : Sig A N j) (κ : Lv A) : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits) (n : ℕ),
    1 + 1 / ((p : ℝ) - 1) < n → ∃ z : AdmAt S κ hp hW, z.n = n

end GlobalTheory.ShFam.Pad
