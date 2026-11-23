import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta
import Development.AbelianVarietyTheory.Definitions.Foundations.Letter

noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4

namespace UpperTheory.V.Z.Kato.Sym

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

abbrev Row (M : ℕ) : Type := Fin 2 → ZMod M

def toQ (M : ℕ) (x : Row M) : Fin 2 → ℚ := fun i => ((x i).val : ℚ) / M

def Ok {M : ℕ} (x y : Row M) : Prop := (2 : ZMod M) • x ≠ 0 ∧ (2 : ZMod M) • y ≠ 0

def cyc (M : ℕ) (s : Ω ≃ₐ[ℚ] Ω) : ZMod M := Classical.epsilon fun y : ZMod M => ∀ z : Ω, z ^ M = 1 → s z = z ^ y.val

def gr (M : ℕ) (s : Ω ≃ₐ[ℚ] Ω) (x : Row M) : Row M := ![x 0, cyc M s * x 1]

def rt {M : ℕ} (x : Row M) (γ : SL(2, ℤ)) : Row M := x ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M))

def dn (k M : ℕ) (x : Row (k * M)) : Row M := fun i => ZMod.castHom (dvd_mul_left M k) (ZMod M) (x i)

def up (k M : ℕ) (x : Row M) : Row (k * M) := fun i => ((k * (x i).val : ℕ) : ZMod (k * M))

def Cgr {K : Type} [Field K] (m : ℕ) (f g : Kˣ) : Prop := ∃ h : Kˣ, f = g * h ^ m

def slU (X : Tower Ω ε) (g : GQ) : X.Kˣ →* X.Kˣ := Units.map (X.sl g : X.K →* X.K)

def galU (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) : X.Kˣ →* X.Kˣ := Units.map (X.gal s : X.K →* X.K)

abbrev Fam (X : Tower Ω ε) (M : ℕ) : Type := Row M → Row M → X.Kˣ

def Eqv (X : Tower Ω ε) (m M : ℕ) (a : Fam X M) : Prop :=
  ∀ x y, Ok x y → a x y ∈ X.Un m ∧ ∀ γ : SL(2, ℤ), Cgr m (slU X (ofSL γ) (a x y)) (a (rt x γ) (rt y γ))

def tw (X : Tower Ω ε) (m M : ℕ) (s : Ω ≃ₐ[ℚ] Ω) (a : Fam X M) : Fam X M :=
  fun x y => galU X s (a (gr M s⁻¹ x) (gr M s⁻¹ y)) ^ (cyc m s).val

def CobBy (X : Tower Ω ε) (m M : ℕ) (a : Fam X M) (w w' : (Ω ≃ₐ[ℚ] Ω) → Fam X M) : Prop :=
  ∀ s x y, Ok x y → Cgr m (w s x y) (w' s x y * tw X m M s a x y / a x y)

def Coh (X : Tower Ω ε) (m M : ℕ) (w w' : (Ω ≃ₐ[ℚ] Ω) → Fam X M) : Prop := ∃ a, Eqv X m M a ∧ CobBy X m M a w w'

structure IsCoc (X : Tower Ω ε) (m M : ℕ) (w : (Ω ≃ₐ[ℚ] Ω) → Fam X M) : Prop where
  eqv : ∀ s, Eqv X m M (w s)
  coc : ∀ s t x y, Ok x y → Cgr m (w (s * t) x y) (w s x y * tw X m M s (w t) x y)
  loc : ∃ T : Finset Ω, ∀ s t, (∀ z ∈ T, s z = t z) → ∀ x y, Ok x y → Cgr m (w s x y) (w t x y)

open Classical in

def pushD (X : Tower Ω ε) (k M : ℕ) [NeZero k] [NeZero M] (a : Fam X (k * M)) : Fam X M :=
  haveI : NeZero (k * M) := ⟨mul_ne_zero (NeZero.ne k) (NeZero.ne M)⟩
  fun x y => ∏ x' ∈ Finset.univ.filter (fun x' => dn k M x' = x), ∏ y' ∈ Finset.univ.filter (fun y' => dn k M y' = y), a x' y'

open Classical in

def pushH (X : Tower Ω ε) (k M : ℕ) [NeZero k] [NeZero M] (a : Fam X (k * M)) : Fam X M :=
  haveI : NeZero (k * M) := ⟨mul_ne_zero (NeZero.ne k) (NeZero.ne M)⟩
  fun x y => ∏ x' ∈ Finset.univ.filter (fun x' => x' 0 = up k M x 0 ∧ dn k M x' 1 = x 1),
    ∏ y' ∈ Finset.univ.filter (fun y' => y' 0 = up k M y 0 ∧ dn k M y' 1 = y 1), a x' y'

def EqvH (X : Tower Ω ε) (m k M : ℕ) (a : Fam X M) : Prop :=
  ∀ x y, Ok x y → a x y ∈ X.Un m ∧ ∀ γ γ' : SL(2, ℤ),
    !![(k : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(k : ℤ), 0; 0, 1] →
      Cgr m (slU X (ofSL γ) (a x y)) (a (rt x γ') (rt y γ'))

attribute [local instance] algMdl

def wGen (X : Tower Ω ε) (M l n : ℕ) (u v : X.K) (σ : Ω ≃ₐ[ℚ] Ω) : X.K :=
  ((topW (K := topL X M) (topZeta X M l n) (topChar X M l n u) (topChar X M l n v)
    (topEta X M (topChar X M l n u) (topChar X M l n v)) (topLift X M σ)⁻¹ : topL X M) : X.K)

def Lv (c d M : ℕ) : Prop := 0 < M ∧ Nat.Coprime c M ∧ Nat.Coprime d M

structure Laws (X : Tower Ω ε) (l c d : ℕ) (w : ∀ (_ M : ℕ), (Ω ≃ₐ[ℚ] Ω) → Fam X M) : Prop where
  coc : ∀ n M, Lv c d M → IsCoc X (l ^ n) M (w n M)
  red : ∀ n M, Lv c d M → Coh X (l ^ n) M (w (n + 1) M) (w n M)
  lev : ∀ n k M, Lv c d (k * M) → Coh X (l ^ n) M (fun s x y => w n (k * M) s (up k M x) (up k M y)) (w n M)
  dist : ∀ n k M [NeZero k] [NeZero M], Lv c d (k * M) → Coh X (l ^ n) M (fun s => pushD X k M (w n (k * M) s)) (w n M)
  isog : ∀ n k M [NeZero k] [NeZero M], Lv c d (k * M) → ∃ a, EqvH X (l ^ n) k M a ∧
    CobBy X (l ^ n) M a (fun s => pushH X k M (w n (k * M) s)) fun s x y => slU X (toGQ !![(k : ℤ), 0; 0, 1]) (w n M s x y)
  top : ∀ n k M M', Lv c d M → 0 < k → 0 < M' → k * M ∣ M' → l ^ n ∣ M' → ∀ x y : Row M, Ok x y → ∀ x' y' : Fin 2 → ℚ,
    (∀ i, ∃ j : ℤ, x' i = toQ M x i + j) → (∀ i, ∃ j : ℤ, y' i = toQ M y i + j) →
      ∃ a : X.Kˣ, a ∈ X.Un (l ^ n) ∧ (∀ γ ∈ CongruenceSubgroup.Gamma M', Cgr (l ^ n) (slU X (ofSL γ) a) a) ∧ ∀ s ∈ fixMu Ω M', ∃ h : X.Kˣ,
        X.sl (toGQ !![(k : ℤ), 0; 0, 1]) (w n M s x y : X.K) =
          wGen X M' l n (X.sl (toGQ !![(k : ℤ), 0; 0, 1]) (siegel X c x')) (X.sl (toGQ !![(k : ℤ), 0; 0, 1]) (siegel X d y')) s *
            (X.gal s a / a) * (h : X.K) ^ l ^ n

def SymEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l c d : ℕ), l.Prime →
    1 < c → 1 < d → Nat.Coprime c 6 → Nat.Coprime d 6 → ∃ w, Laws X l c d w

end UpperTheory.V.Z.Kato.Sym

end
