import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaTW
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin

noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois

namespace UpperTheory.Kd.L

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def IsWit (X : Tower Ω ε) (N l n : ℕ) [Fact l.Prime] (b : X.Fn l) (f : X.Kˣ) : Prop :=
  Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (f : X.K) ∧
    AdicCompletion.eval (idl l) (X.Kl l) n (b ![1, 0]) = X.cls l n f ∧
    ∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) →
      ∃ g : X.K, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ (f : X.K) * X.sl (ofSL δ) f = g ^ (l ^ n)

theorem isThB_iff (X : Tower Ω ε) (A : ValuationSubring Ω) (N l n : ℕ) [Fact l.Prime] (b : X.Fn l) (φ : HahnSeries ℚ Ω) :
    IsThB X A N l n b φ ↔ ∃ f : X.Kˣ, IsWit X N l n b f ∧ IsDl X A l n 1 (f : X.K) φ :=
  ⟨fun ⟨f, a, b, c, d⟩ => ⟨f, ⟨a, b, c⟩, d⟩, fun ⟨f, ⟨a, b, c⟩, d⟩ => ⟨f, a, b, c, d⟩⟩

instance topMu.neZero (l n m N : ℕ) [Fact l.Prime] [NeZero N] : NeZero (topMu l n m N) :=
  ⟨Nat.mul_ne_zero (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) (Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne N))⟩

open Classical in

def Gs (N l M : ℕ) [NeZero M] : Finset SL(2, ZMod M) :=
  Finset.univ.filter fun γ => γ ∈ (Gam N l).map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)))

def Tm (M b : ℕ) : SL(2, ZMod M) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (ModularGroup.T ^ b)

def IsReps (N l M : ℕ) [NeZero M] (R : Finset SL(2, ZMod M)) : Prop :=
  R ⊆ Gs N l M ∧ ∀ γ ∈ Gs N l M, ∃! p : SL(2, ZMod M) × ℕ, p.1 ∈ R ∧ p.2 < M ∧ γ = p.1 * Tm M p.2

def ex (l n w : ℕ) (g : SL(2, ℤ)) : ℕ := ((en g 0 0 : ℤ) : ZMod (l ^ n)).val ^ w

def FF (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n m N : ℕ) [NeZero N] (x : ZMod N) (c d w : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ))
    (σ : Ω ≃ₐ[ℚ] Ω) : X.K :=
  ∏ r₀ : (ZMod l)ˣ, ∏ γ ∈ Gs N l (topMu l n m N),
    X.sl (ofSL (gm r₀ * liftSL _ γ)) (wkMu X l n m N x c d σ) ^ ex l n w (gm r₀ * liftSL _ γ)

def EE [CharZero Ω] (ε : Ω →+* ℂ) (l L N : ℕ) (x : ZMod N) (c d : ℕ) (g : SL(2, ℤ)) (r : ℚ) : Ω :=
  coefQ (l ^ L) (cmul
    (smF c 1 (N * l ^ L) (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) (en g 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L))
      ((N : ℤ) ^ 2 * en g 0 1))
    (smF d 1 (N * l ^ L) (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) (en g 0 0 * (topT l L N : ℤ) * (l : ℤ) ^ L + en g 1 0)
      ((N : ℤ) * en g 1 1))) r

def redTop (l n m N : ℕ) (y : (ZMod (topM l n m (N * N)))ˣ) : (ZMod (l ^ (m + n)))ˣ :=
  Units.map (ZMod.castHom (Dvd.intro _ rfl : l ^ (m + n) ∣ topM l n m (N * N)) (ZMod (l ^ (m + n)))).toMonoidHom y

def bTop (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n m N : ℕ) (bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l) (s : Ω ≃ₐ[ℚ] Ω)
    (y : (ZMod (topM l n m (N * N)))ˣ) : X.Fn l :=
  X.galB l (repM (topM l n m (N * N)) y)
    (bB ((repM (topM l n m (N * N)) y)⁻¹ * s * repM (topM l n m (N * N)) (y * (cycM (topM l n m (N * N)) s)⁻¹)))

instance topM.neZero (l n m N : ℕ) [Fact l.Prime] [NeZero N] : NeZero (topM l n m (N * N)) :=
  ⟨Nat.mul_ne_zero (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) (Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne N))⟩

open Classical in

def bMid (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n m N : ℕ) [NeZero N] (bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l) (s : Ω ≃ₐ[ℚ] Ω)
    (z : (ZMod (l ^ (m + n)))ˣ) : X.Fn l :=
  ∑ y ∈ Finset.univ.filter (fun y => redTop l n m N y = z), bTop X l n m N bB s y

open Classical in

def Fsum [CharZero Ω] (ε : Ω →+* ℂ) (l : ℕ) [Fact l.Prime] (n m N : ℕ) [NeZero N] (x : ZMod N) (c d w : ℕ)
    (gm : (ZMod l)ˣ → SL(2, ℤ)) (R : Finset SL(2, ZMod (topMu l n m N))) (z : (ZMod (l ^ (m + n)))ˣ) (r : ℚ) : Ω :=
  if r.den = 1 then
    (N : Ω) ^ 3 * ∑ y ∈ Finset.univ.filter (fun y => redTop l n m N y = z), ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ R,
      (ex l n w (gm r₀ * liftSL _ γ) : Ω) * repM (topM l n m (N * N)) y (EE ε l (m + n) N x c d (gm r₀ * liftSL _ γ) r)
  else 0

structure Par (l : ℕ) [Fact l.Prime] (N c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) : Prop where
  odd : l ≠ 2
  five : 5 ≤ N
  cop : ¬ l ∣ N
  c1 : 1 < c
  d1 : 1 < d
  cc : Nat.Coprime c (6 * l * N)
  dc : Nat.Coprime d (6 * l * N)
  g0 : ∀ r₀, gm r₀ ∈ CongruenceSubgroup.Gamma0 N
  ga : ∀ r₀, ((en (gm r₀) 0 0 : ℤ) : ZMod N) = ((en (gm 1) 0 0 : ℤ) : ZMod N)
  col : ∀ r₀ : (ZMod l)ˣ, (((gm r₀ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod l) =
    -(r₀ : ZMod l) * (((gm r₀ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod l)

end UpperTheory.Kd.L
