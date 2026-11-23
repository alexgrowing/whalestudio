import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.WkTopEq

noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4

namespace UpperTheory.V.Z.Kato.Sym

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

abbrev Kb (X : Tower Ω ε) : Type := AlgebraicClosure X.K

abbrev io (X : Tower Ω ε) : X.K →+* Kb X := algebraMap X.K (Kb X)

def InD (X : Tower Ω ε) (h : RingAut (Kb X)) : Prop := ∀ f : X.K, h (io X f) = io X f

def zt (X : Tower Ω ε) (m : ℕ) : Kb X := io X (algebraMap Ω X.K (eOm ε (1 / (m : ℚ))))

def lg (X : Tower Ω ε) (m : ℕ) (a b : Kb X) : ZMod m := Classical.epsilon fun i : ZMod m => a = zt X m ^ i.val * b

def ka (X : Tower Ω ε) (m : ℕ) (θ : Kb X) (h : RingAut (Kb X)) : ZMod m := lg X m (h θ) θ

def IsU (X : Tower Ω ε) (u : X.K) : Prop := u ≠ 0 ∧ ∀ W, X.OverY W → W.valuation u = 1

def LC (X : Tower Ω ε) {m : ℕ} (φ : RingAut (Kb X) → ZMod m) : Prop :=
  ∃ B : Finset (Kb X), ∀ h h', InD X h → InD X h' → (∀ b ∈ B, h b = h' b) → φ h = φ h'

def Unr (X : Tower Ω ε) {m : ℕ} (φ : RingAut (Kb X) → ZMod m) : Prop :=
  ∀ (B : ValuationSubring (Kb X)) (h : RingAut (Kb X)), X.OverY (B.comap (io X)) → InD X h →
    (∀ z, B.valuation z ≤ 1 → B.valuation (h z - z) < 1) → φ h = 0

structure Pt (X : Tower Ω ε) (m : ℕ) where

  a : Kb X

  b : Kb X

  η : RingAut (Kb X) → ZMod m

structure IsPt (X : Tower Ω ε) (m : ℕ) (u v : X.K) (P : Pt X m) : Prop where
  hu : IsU X u
  hv : IsU X v
  ha : P.a ^ m = io X u
  hb : P.b ^ m = io X v
  cob : ∀ g h, InD X g → InD X h → ka X m P.a g * ka X m P.b h = P.η h - P.η (g * h) + P.η g
  lc : LC X P.η
  unr : Unr X P.η

def dif (X : Tower Ω ε) {m : ℕ} (P Q : Pt X m) (h : RingAut (Kb X)) : ZMod m :=
  P.η h - Q.η h + ka X m Q.a h * lg X m P.b Q.b - lg X m P.a Q.a * ka X m Q.b h

def Pt.mv {X : Tower Ω ε} {m : ℕ} (σ : RingAut (Kb X)) (χ : ZMod m) (P : Pt X m) : Pt X m :=
  ⟨σ P.a, σ P.b, fun h => χ ^ 2 * P.η (σ⁻¹ * h * σ)⟩

def IsKum (X : Tower Ω ε) (m : ℕ) (φ : RingAut (Kb X) → ZMod m) (f : X.Kˣ) : Prop :=
  ∃ θ : Kb X, θ ^ m = io X f ∧ ∀ h, InD X h → ka X m θ h = φ h

def admitted (X : Tower Ω ε) (τ : X.K ≃+* X.K) (s : Ω ≃ₐ[ℚ] Ω) : Prop :=
  (∀ c : Ω, τ (algebraMap Ω X.K c) = algebraMap Ω X.K (s c)) ∧ ∀ W, X.OverY W ↔ X.OverY (W.comap (τ : X.K →+* X.K))

def Lifts (X : Tower Ω ε) (σ : RingAut (Kb X)) (τ : X.K ≃+* X.K) : Prop := ∀ f, σ (io X f) = io X (τ f)

def Mv (X : Tower Ω ε) (m : ℕ) (τ : X.K ≃+* X.K) (s : Ω ≃ₐ[ℚ] Ω) (P Q : Pt X m) (f : X.Kˣ) : Prop :=
  ∃ σ, Lifts X σ τ ∧ IsKum X m (dif X (P.mv σ (cyc m s)) Q) f

def unU (X : Tower Ω ε) (τ : X.K ≃+* X.K) : X.Kˣ →* X.Kˣ := Units.map (τ : X.K →* X.K)

def slR (X : Tower Ω ε) (g : GQ) : X.K ≃+* X.K := (X.sl g).toRingEquiv

def IsSum (X : Tower Ω ε) (m : ℕ) {I J : Type} (A : Finset I) (B : Finset J) (P : I → J → Pt X m) (R : Pt X m) : Prop :=
  ∃ (α : I → Kb X) (β : J → Kb X) (η : I → J → RingAut (Kb X) → ZMod m),
    (∀ i ∈ A, ∀ j ∈ B, α i ^ m = (P i j).a ^ m ∧ β j ^ m = (P i j).b ^ m ∧
      ∀ h, InD X h → dif X (P i j) ⟨α i, β j, η i j⟩ h = 0) ∧
    R = ⟨∏ i ∈ A, α i, ∏ j ∈ B, β j, fun h => ∑ i ∈ A, ∑ j ∈ B, η i j h⟩

def Pt.red {X : Tower Ω ε} (k m : ℕ) (P : Pt X (k * m)) : Pt X m :=
  ⟨P.a ^ k, P.b ^ k, fun h => ZMod.castHom (dvd_mul_left m k) (ZMod m) (P.η h)⟩

def IsSec (X : Tower Ω ε) (m : ℕ) (t : X.K → X.K → Pt X m) : Prop :=
  ∀ u v, IsU X u → IsU X v → IsPt X m u v (t u v) ∧
    ∀ γ : SL(2, ℤ), Mv X m (slR X (ofSL γ)) 1 (t u v) (t (X.sl (ofSL γ) u) (X.sl (ofSL γ) v)) 1

def sg (X : Tower Ω ε) (c M : ℕ) (x : Row M) : X.K := siegel X c (toQ M x)

def IsSymb (X : Tower Ω ε) (m c d M : ℕ) (t : X.K → X.K → Pt X m) (w : (Ω ≃ₐ[ℚ] Ω) → Fam X M) : Prop :=
  ∀ s x y, Ok x y → w s x y ∈ X.Un m ∧
    Mv X m (X.gal s) s (t (sg X c M (gr M s⁻¹ x)) (sg X d M (gr M s⁻¹ y))) (t (sg X c M x) (sg X d M y)) (w s x y)

def dg (k : ℕ) : GQ := toGQ !![(k : ℤ), 0; 0, 1]

end UpperTheory.V.Z.Kato.Sym

end
