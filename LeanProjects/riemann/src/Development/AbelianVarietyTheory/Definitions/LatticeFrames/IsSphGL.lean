import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm

noncomputable section

namespace GlobalTheory.Core.Rk.SWQ

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open Formalism.UG (IsUnifV qV Ov ordL diagJ)
open GlobalTheory.LFun (KGL toCompl IsSplitChart)

section Local

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {m n N : ℕ}

def IntM {ι κ : Type} (x : Matrix ι κ (w.adicCompletion E)) : Prop := ∀ i j, x i j ∈ Ov E w

def PrimM (u : Matrix (Fin m) (Fin n) (w.adicCompletion E)) : Prop :=
  IntM u ∧ ∃ l : Matrix (Fin n) (Fin m) (w.adicCompletion E), IntM l ∧ l * u = 1

def mob (q r : ℕ) : ℂ := (-1) ^ r * (q : ℂ) ^ (r * (r - 1) / 2)

def IsDC (ϖ : w.adicCompletion E) (j : ℕ) (g : GL (Fin n) (w.adicCompletion E)) : Prop :=
  ∃ a ∈ KGL w n, ∃ b ∈ KGL w n, g.1 = a.1 * diagJ n ϖ j * b.1

structure IsMob (ϖ : w.adicCompletion E) (y : Fin N → GL (Fin n) (w.adicCompletion E)) (r : Fin N → ℕ) : Prop where

  le : ∀ i, r i ≤ n

  dc : ∀ i, IsDC ϖ (r i) (y i)⁻¹

  uniq : ∀ j ≤ n, ∀ g : GL (Fin n) (w.adicCompletion E), IsDC ϖ j g⁻¹ → ∃! i, (y i)⁻¹ * g ∈ KGL w n

def blks {R : Type} (x : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  x.submatrix finSumFinEquiv finSumFinEquiv

def dg (y : GL (Fin n) (w.adicCompletion E)) : GL (Fin (n + n)) (w.adicCompletion E) := blkGL finSumFinEquiv (y, 1)

structure IsSphGL (z : ℂˣ) (σ : ℂ) (φ : GL (Fin (n + n)) (w.adicCompletion E) → ℂ) : Prop where

  left : ∀ p : GL (Fin (n + n)) (w.adicCompletion E), (blks p.1).toBlocks₂₁ = 0 → ∀ x,
    φ (p * x) = (z : ℂ) ^ ordL p.1.det *
      (qV E w : ℂ) ^ (-(σ * ((ordL (blks p.1).toBlocks₁₁.det - ordL (blks p.1).toBlocks₂₂.det : ℤ) : ℂ))) * φ x

  right : ∀ κ ∈ KGL w (n + n), ∀ x, φ (x * κ) = φ x

def cOne (q : ℕ) (z : ℂˣ) (σ : ℂ) (r : ℕ) : ℂ := mob q r * (z : ℂ) ^ r * (q : ℂ) ^ (-(σ * r))

def cTwo (q n : ℕ) (z : ℂˣ) (σ : ℂ) (r : ℕ) : ℂ := mob q r * (z : ℂ) ^ r * (q : ℂ) ^ ((σ - n) * r)

def tOne (z : ℂˣ) (σ : ℂ) (y : Fin N → GL (Fin n) (w.adicCompletion E)) (r : Fin N → ℕ)
    (φ : GL (Fin (n + n)) (w.adicCompletion E) → ℂ) : GL (Fin (n + n)) (w.adicCompletion E) → ℂ :=
  fun x => ∑ i, cOne (qV E w) z σ (r i) * φ (x * dg (y i))

variable (w m n) in

abbrev UV : Type := Matrix (Fin m) (Fin n) (w.adicCompletion E) × Matrix (Fin n) (Fin m) (w.adicCompletion E)

def ind (S : UV w m n → Prop) : UV w m n → ℂ := Set.indicator {p | S p} 1

def mv (h : GL (Fin m) (w.adicCompletion E)) (p : UV w m n) : UV w m n := (h.1 * p.1, p.2 * (h⁻¹).1)

variable (w m n) in

def coinv : Submodule ℂ (UV w m n → ℂ) :=
  Submodule.span ℂ {φ | ∃ ξ ∈ WeilM.SB (UV w m n), ∃ h : GL (Fin m) (w.adicCompletion E), φ = ξ ∘ mv h - ξ}

end Local

section Adelic

variable {D : D7} {q : FinPl D} {w : HeightOneSpectrum (𝓞 D.host.E)}

def cw (h : w.under (𝓞 D.host.F) = q) : AE D →+* w.adicCompletion D.host.E := (toCompl h).comp (compFin D.host.F D.host.E q)

def uv (h : w.under (𝓞 D.host.F) = q) (B : HSp D) {n : ℕ} (x : Mx D B.rank n) : UV w B.rank n :=
  (Matrix.map x (cw h), Matrix.map (adj x ⬝ gA B : Mx D n B.rank) (cw h))

def offM (q : FinPl D) {m n : ℕ} (x : Mx D m n) : Mx D m n :=
  x - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleFin q 1)) • x

def offG (V : HSp D) (q : FinPl D) (g : GA D V) : GA D V :=
  g * (emb D.sp.cm.sig V.gram q (proj D.sp.cm.sig V.gram q g))⁻¹

def admat (A : HSp D) (g : GA D (dblSp A)) : Matrix (Fin A.rank ⊕ Fin A.rank) (Fin A.rank ⊕ Fin A.rank) (AE D) :=
  Matrix.fromBlocks ((dblDec A).pX ⬝ (mt (dblSp A) g ⬝ (dblDec A).jX) : Mx D A.rank A.rank)
    ((dblDec A).pX ⬝ (mt (dblSp A) g ⬝ (dblDec A).jY) : Mx D A.rank A.rank) (lowC A g)
    ((dblDec A).pY ⬝ (mt (dblSp A) g ⬝ (dblDec A).jY) : Mx D A.rank A.rank)

structure IsAd (A : HSp D) (h : w.under (𝓞 D.host.F) = q) (e : Gv A q ≃* GL (Fin A.rank) (w.adicCompletion D.host.E))
    (f : Gv (dblSp A) q ≃* GL (Fin (A.rank + A.rank)) (w.adicCompletion D.host.E)) (k : Gv (dblSp A) q) : Prop where

  chart : IsSplitChart D.sp.cm.sig A.gram (frameLat A) h e

  mat : ∀ g : GA D (dblSp A), blks (f (proj D.sp.cm.sig (dblSp A).gram q g)).1 = (admat A g).map (cw h)

  io : ∀ y, f (k * ioAt A q y * k⁻¹) = dg (e y)

  hyp : ∀ g, g ∈ KFin D.sp.cm.sig (dblSp A).gram (frameLat A) q ↔ f (k * g * k⁻¹) ∈ KGL w (A.rank + A.rank)

def yy {A : HSp D} (e : Gv A q ≃* GL (Fin A.rank) (w.adicCompletion D.host.E)) {N : ℕ}
    (y : Fin N → GL (Fin A.rank) (w.adicCompletion D.host.E)) : Fin (N * N) → Gv A q :=
  fun i => e.symm (y i.divNat * y i.modNat)

def cc (χ : (AE D)ˣ →* Circle) (w : HeightOneSpectrum (𝓞 D.host.E)) (a : ℕ) {N : ℕ} (r : Fin N → ℕ) (s : ℂ) :
    Fin (N * N) → ℂ :=
  fun i => cTwo (qV D.host.E w) a (LFun.val (F := D.host.F) χ w)⁻¹ (s + (a : ℂ) / 2) (r i.divNat) *
    cOne (qV D.host.E w) (LFun.val (F := D.host.F) χ w)⁻¹ (s + (a : ℂ) / 2) (r i.modNat)

def ForQ (D : D7) (Q : ∀ (_ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (_ : (AE D)ˣ →* Circle) (_ : WRep (dblSp A) B)
    (_ : GL (Fin A.rank) (AE D)) (_ : Measure (WO A B)) (_ : Set (WO A B)) (_ : Measure (GA D B))
    (_ : Measure (skewA D A.rank)) (_ : WO (dblSp A) B → ℂ) (q : FinPl D) (w : HeightOneSpectrum (𝓞 D.host.E))
    (_ : w.under (𝓞 D.host.F) = q) (_ : Gv A q ≃* GL (Fin A.rank) (w.adicCompletion D.host.E))
    (_ : Gv (dblSp A) q ≃* GL (Fin (A.rank + A.rank)) (w.adicCompletion D.host.E)) (_ : Gv (dblSp A) q) (N : ℕ)
    (_ : Fin N → GL (Fin A.rank) (w.adicCompletion D.host.E)) (_ : Fin N → ℕ), Prop) : Prop :=
  ∀ ψ A B χB omh a ν 𝓨 mH κ 𝓒 f, Dbl ψ A B χB omh a ν 𝓨 mH κ 𝓒 f → ∀ LB q, VacAt ψ A B χB omh LB q f →
    ∀ w h e fc k, IsAd A h e fc k → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ N y r, IsMob ϖ y r →
      Q ψ A B χB omh a ν 𝓨 mH κ f q w h e fc k N y r

end Adelic

example (q : ℕ) (z : ℂˣ) (σ : ℂ) : cOne q z σ 0 = 1 := by simp [cOne, mob]

end GlobalTheory.Core.Rk.SWQ

end
