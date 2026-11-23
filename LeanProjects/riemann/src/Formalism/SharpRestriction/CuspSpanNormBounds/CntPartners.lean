import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
import Formalism.HermitianLattices.StatementMass

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.S.Cnt

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Hyp

variable (D : D7)

def Stand (u u' : D.what₂.Word) : Prop :=
  1 ≤ D.R.rS ∧
  (Tu D u).Prime ∧ (Tu D u').Prime ∧ 3 ≤ Tu D u ∧ 3 ≤ Tu D u' ∧
  SplitsCompletely (E := D.host.E) (Tu D u) ∧ SplitsCompletely (E := D.host.E) (Tu D u') ∧
  (D.host.g 0).Prime ∧ (D.host.g 1).Prime ∧ D.host.g 0 ≠ D.host.g 1 ∧
  (∀ i, SplitsCompletely (E := D.host.E) (D.host.g i)) ∧
  Nat.Coprime (gS D) (Tu D u * Tu D u') ∧ Tu D u ≡ Tu D u' [MOD gS D]

def Hyp0 (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT ∧ StandingNumericalData D C0 ∧ 1 ≤ C0

def Hyp (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  let k : ℝ := D.R.k
  let m : ℝ := D.R.m
  let f : ℝ := D.R.f
  let r : ℝ := D.R.rS
  let L : ℝ := large₂.sc.L
  let T : ℝ := (D.mem u).A.T
  let T' : ℝ := (D.mem u').A.T
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ Stand D u u' ∧
  T' / T ≤ A ∧ T / T' ≤ A ∧
  Cl * (m ^ 6 * L) ≤ k * Real.log k ∧
  Real.log f ^ 2 ≤ A * (m ^ 2 * L) ∧ Real.log f ≤ A * r ^ 2 ∧
  ∀ τ, vand (uS D u' τ) ≤ A ^ D.R.k * vand (uS D u τ) ∧ vand (uS D u τ) ≤ A ^ D.R.k * vand (uS D u' τ)

end Hyp

section AnyLat

variable (K : Type) [Field K] [NumberField K] [StarRing K]

def stdH (j : ℕ) : (Fin j → K) →ₗ⋆[K] (Fin j → K) →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => ∑ i, star (x i) * y i)
    (fun x x' y => by simp [Finset.sum_add_distrib, add_mul])
    (fun c x y => by simp [Finset.mul_sum, mul_assoc, starRingEnd_apply])
    (fun x y y' => by simp [Finset.sum_add_distrib, mul_add])
    (fun c x y => by simp [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring))

def stdLat (j : ℕ) : Submodule (𝓞 K) (Fin j → K) :=
  Submodule.span (𝓞 K) (Set.range (fun i : Fin j => Pi.single i (1 : K)))

def massU (j : ℕ) : ℝ := Formalism.HermitianLatticesTheory.mass (stdH K j) (stdLat K j)

variable {K} {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def IsPosDef (h : V →ₗ⋆[K] V →ₗ[K] K) : Prop :=
  ∀ τ : K →+* ℂ, ∀ x : V, x ≠ 0 → 0 < (τ (h x x)).re

abbrev discMod (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule (𝓞 K) V) : Type :=
  ↥(Formalism.HermitianLatticesTheory.dual h M) ⧸ M.comap (Formalism.HermitianLatticesTheory.dual h M).subtype

def DiscGen (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule (𝓞 K) V) (e : ℕ) : Prop :=
  ∃ s : Finset (discMod h M), s.card ≤ e ∧ Submodule.span (𝓞 K) (s : Set (discMod h M)) = ⊤

def PrimSubs (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (j de : ℕ) : Set (Submodule (𝓞 K) V) :=
  {M₀ | IsPrimitiveSub M₀ L ∧ Module.finrank K (Submodule.span K (M₀ : Set V)) = j ∧ latDetH h M₀ = de}

def cntPrim (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (j de : ℕ) : ℕ∞ := (PrimSubs h L j de).encard

def stabAt (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule (𝓞 K) V) (de : ℕ) : Set (V ≃ₗ[K] V) :=
  {γ | γ ∈ Formalism.HermitianLatticesTheory.isom h ∧ ∀ P : HeightOneSpectrum (𝓞 K), ((de : 𝓞 K) ∈ P.asIdeal) →
    (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap γ M) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M)}

def levelIdx (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule (𝓞 K) V) (de : ℕ) : ℕ :=
  Nat.card (Quot (fun γ₁ γ₂ : stabAt h M de =>
    ∀ x ∈ Formalism.HermitianLatticesTheory.dual h M, ∀ P : HeightOneSpectrum (𝓞 K), ((de : 𝓞 K) ∈ P.asIdeal) →
      (haveI := P.isPrime; γ₁.1.symm (γ₂.1 x) - x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M)))

end AnyLat

section Local

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def pE (p : Ideal (𝓞 F)) : Ideal (𝓞 E) := Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p

def eta₃ (p : Ideal (𝓞 F)) : ℤ :=
  if ∃ P : Ideal (𝓞 E), P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = p ∧
      Formalism.HermitianLatticesTheory.conjIdeal (K := E) P ≠ P then 1 else -1

abbrev PrimesOver (de : ℕ) : Type := {p : Ideal (𝓞 F) // p.IsMaximal ∧ ((de : 𝓞 F)) ∈ p}

def omegaF (de : ℕ) : ℕ := Nat.card (PrimesOver F de)

variable {F E} {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

def eP (h : V →ₗ⋆[E] V →ₗ[E] E) (M : Submodule (𝓞 E) V) (p : Ideal (𝓞 F)) : ℕ :=
  Nat.log (Ideal.absNorm p ^ 2)
    (Nat.card (↥(Formalism.HermitianLatticesTheory.dual h M) ⧸
      (M ⊔ pE F E p • Formalism.HermitianLatticesTheory.dual h M).comap (Formalism.HermitianLatticesTheory.dual h M).subtype))

end Local

def thP (j ep : ℕ) (eta : ℤ) (q : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc (j - ep + 1) j, (1 - (eta : ℝ) ^ i * (q : ℝ) ^ (-(i : ℤ)))

def Hb (b C : ℝ) (m f : ℕ) : ℝ := b ^ (C * (m : ℝ) ^ 2 * f)

def lg2f (f : ℕ) : ℝ := Real.logb 2 (2 * f)

def cF (f : ℕ) : ℝ := 1 + lg2f f

def Xi (mass : ℕ → ℝ) (k f : ℕ) (HH NT C : ℝ) (s : ℕ) : ℝ :=
  if 2 ≤ s ∧ s ≤ k - 2 then mass s * mass (k - s) / mass k
  else if s = k - 1 ∨ s = k then (C * k) ^ (k * f) * (HH * NT) ^ (C * k) else 0

section Num

variable (D : D7)

abbrev GramM : Type := Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E

def RelZ (Z : GramM D) : Prop := ∃ p : Point D.host.E (D.R.rS + 1), IsInCell (ZhatOM Z) p

def absDl (Z : GramM D) (l : ℕ) (τ : D.what₂.Tau) : ℝ :=
  absReal D.host.rdE (embS D τ) D.R.rS l (leadMinorE Z l)

def Gz (T T' : ℝ) (Z : GramM D) (τ : D.what₂.Tau) : ℝ :=
  absDl D Z (D.R.rS + 1) τ ^ 2 - T * T' * absDl D Z D.R.rS τ ^ 2

def sizeZ (b C : ℝ) (Z : GramM D) : ℝ :=
  ∏ τ, ∏ l ∈ Finset.Icc 1 (D.R.rS + 1), max 1 (absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2))

def HHZ (b C : ℝ) (Z : GramM D) : ℝ :=
  (b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ (C * (D.R.m : ℝ)) * sizeZ D b C Z ^ 4

def nV (T T' : ℝ) (Z : GramM D) (τ : D.what₂.Tau) : ℝ :=
  (Real.exp 1 * Real.pi * Gz D T T' Z τ * (gS D : ℝ) ^ (-(D.R.m : ℝ)) /
    (T * D.R.k * D.host.v)) ^ D.R.k

def NT (u : D.what₂.Word) : ℝ := ((D.mem u).A.T : ℝ) ^ D.R.f

def massS (j : ℕ) : ℝ := massU D.host.E j

def XiS (u : D.what₂.Word) (HH C : ℝ) (s : ℕ) : ℝ :=
  Xi (massS D) D.R.k D.R.f HH (NT D u) C s

end Num

section Rows

variable (D : D7)

abbrev LatV : Type := Submodule (𝓞 D.host.E) (hS D).V

abbrev FlagU (u : D.what₂.Word) : Type := LFlag (hS D) D.R.rS ((Tu D u : ℕ) : D.host.E)

def cntCl {α : Type} (X : Set α) (R : α → α → Prop) : ℕ∞ :=
  Set.encard {O : Set α | ∃ a ∈ X, O = {b | b ∈ X ∧ R a b}}

variable (Λ : LatV D)

def TEqv {T T' : D.host.E} (F : LFlag (hS D) D.R.rS T) (F' F'₂ : LFlag (hS D) D.R.rS T') : Prop :=
  ∃ n ∈ NLam Λ F, FrameEqv D n F' F'₂

def IsTermF {T T' : D.host.E} (F : LFlag (hS D) D.R.rS T) (F' : LFlag (hS D) D.R.rS T') : Prop :=
  IsTerm Λ (gS D) F F' ∧ FrameOK D Λ F'

abbrev Trip (T' : D.host.E) : Type :=
  LFlag (hS D) D.R.rS T' × LFlag (hS D) D.R.rS T' × ((hS D).V ≃ₗ[D.host.E] (hS D).V)

def PEqv {T T' : D.host.E} (F : LFlag (hS D) D.R.rS T) (p q : Trip D T') : Prop :=
  ∃ n' ∈ NLam Λ F, ∃ n'' ∈ NLam Λ F, FrameEqv D n' p.1 q.1 ∧ FrameEqv D n'' p.2.1 q.2.1 ∧
    ∀ x ∈ orth (hS D) (Xsp q.1), q.2.2 x - n'' (p.2.2 (n'.symm x)) ∈ Xsp q.2.1

def PairSet {T : D.host.E} (T' : D.host.E) (F : LFlag (hS D) D.R.rS T) (Z' Z'' : GramM D) (s : ℕ) (De : ℝ) :
    Set (Trip D T') :=
  {p | IsTermF D Λ F p.1 ∧ IsTermF D Λ F p.2.1 ∧ IsPair Λ F p.1 p.2.1 p.2.2 (gS D) ∧
    ZEquiv (ZhatL F p.1) Z' ∧ ZEquiv (ZhatL F p.2.1) Z'' ∧ s0 Λ F p.1 p.2.1 p.2.2 D.R.k = s ∧
    latDet (hS D) (Mlat Λ F p.1 p.2.1 p.2.2 (gS D)) * (iIdx Λ (gS D) F p.1 : ℝ) * (iIdx Λ (gS D) F p.2.1 : ℝ) ≤ De}

def cntPairs {T : D.host.E} (T' : D.host.E) (F : LFlag (hS D) D.R.rS T) (Z' Z'' : GramM D) (s : ℕ) (De : ℝ) : ℕ∞ :=
  cntCl (PairSet D Λ T' F Z' Z'' s De) (PEqv D Λ F)

def Partners {T T' : D.host.E} (F : LFlag (hS D) D.R.rS T) (F' : LFlag (hS D) D.R.rS T') (Z : GramM D) :
    Set (LFlag (hS D) D.R.rS T') :=
  {F'' | IsTermF D Λ F F'' ∧ IsGeneric Λ (gS D) F F'' ∧ ZEquiv (ZhatL F F'') Z ∧
    ∃ β, IsPair Λ F F' F'' β (gS D) ∧ s0 Λ F F' F'' β D.R.k = 1}

def cntPartners {T T' : D.host.E} (F : LFlag (hS D) D.R.rS T) (F' : LFlag (hS D) D.R.rS T') (Z : GramM D) : ℕ∞ :=
  cntCl (Partners D Λ F F' Z) (TEqv D Λ F)

def massRows {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (s : Finset (LatV D)) : ℝ := ∑ Λ ∈ s, wRow D F0 Λ

def MeanLe {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (s : Finset (LatV D)) (N : LatV D → ℕ∞) (B : ℝ) : Prop :=
  (∑ Λ ∈ s, ENNReal.ofReal (wRow D F0 Λ) * (N Λ : ℝ≥0∞)) ≤
    (∑ Λ ∈ s, ENNReal.ofReal (wRow D F0 Λ)) * ENNReal.ofReal B

def Wb : Submodule D.host.E (hS D).V :=
  orth (hS D) (Submodule.span D.host.E (Set.range D.sp.hypE ∪ Set.range D.sp.hypF))

structure GaugeVol where
  vol : Submodule D.host.E (hS D).V → ℝ
  volUni : ℕ → ℝ
  vol_uni : ∀ (Y : Submodule D.host.E (hS D).V) (j : ℕ) (e : Fin j → (hS D).V),
    Submodule.span D.host.E (Set.range e) = Y → (∀ a b, (hS D).hT (e a) (e b) = if a = b then 1 else 0) →
    vol Y = volUni j

end Rows

end Formalism.MainNotions.S.Cnt

end
