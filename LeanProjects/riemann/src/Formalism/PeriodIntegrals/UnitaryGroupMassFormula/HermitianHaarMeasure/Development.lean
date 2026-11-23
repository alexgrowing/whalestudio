import Formalism.HermitianCurvature.StatementQ

open Matrix Finset MeasureTheory

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def tA {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (Y Yb : Fin m → A)
    (x xb : Fin m → ℂ) (u : ℂ) : Fin 2 → Fin 2 → A := fun p q =>
  match p, q with
  | 0, 0 => qminor E id id u
  | 0, 1 => -∑ i : Fin m, ∑ j : Fin m,
      ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * x j) • (Yb i * qminor E (skip1 i) (skip1 j) (u - 1))
  | 1, 0 => -∑ i : Fin m, ∑ j : Fin m,
      ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * xb i) • (Y j * qminor E (skip1 i) (skip1 j) u)
  | 1, 1 => -∑ i : Fin m, ∑ i' : Fin m, ∑ j : Fin m, ∑ j' : Fin m,
      if i < i' ∧ j < j' then
        ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ))) •
          ((Yb i * algebraMap ℂ A (xb i') - Yb i' * algebraMap ℂ A (xb i)) *
            (Y j * algebraMap ℂ A (x j') - Y j' * algebraMap ℂ A (x j)) *
            qminor E (skip2 i i') (skip2 j j') (u - 1))
      else 0

def HermAlg : Prop :=
  ∀ (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (m : ℕ) (E : Fin m → Fin m → A)
    (Y Yb : Fin m → A) (Hm : Matrix (Fin m) (Fin m) ℂ) (x xb : Fin m → ℂ),
    GlRel E → Hmᴴ = Hm → Hm * Hm = 1 →
    (∀ a b, star (E a b) = ∑ c, ∑ d, (Hm c b * Hm a d) • E c d) →
    (∀ a b, Y a * Y b = Y b * Y a) → (∀ a b, Yb a * Yb b = Yb b * Yb a) → (∀ a b, Y a * Yb b = Yb b * Y a) →
    (∀ a b c, E a b * Y c - Y c * E a b = if a = c then -Y b else 0) →
    (∀ a b c, E a b * Yb c - Yb c * E a b = if b = c then Yb a else 0) →
    (∀ c, Yb c = ∑ l, Hm l c • star (Y l)) → (∀ c, xb c = ∑ l, Hm l c * star (x l)) →
    ∀ (u : ℂ) (p q : Fin 2), star (tA E Y Yb x xb u p q) = tA E Y Yb x xb (star u) q p

def HermAlgFrom : Prop := StarMinor → ContractionsCovariant → MoveVec → MoveCov → HermAlg

def Hm (k r : ℕ) (i : Fin (r + 1)) : Matrix (Fin (mdim k r i)) (Fin (mdim k r i)) ℂ :=
  fun a b => Hpk k r (posL k r i a) (posL k r i b)

def TestF (k r : ℕ) (i : Fin (r + 1)) (f : Mx k r → ℂ) : Prop :=
  SmoothLev k r i Set.univ f ∧ CptOn k r i f

def pairL {k r : ℕ} (μ : Measure (Mt k r)) (f₁ f₂ : Mx k r → ℂ) : ℂ :=
  ∫ x : Mt k r, f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ

def EabTest : Prop :=
  ∀ (k r : ℕ) (i : Fin (r + 1)) (a b : Fin (mdim k r i)) (f : Mx k r → ℂ),
    TestF k r i f → TestF k r i (EH k r (posL k r i a) (posL k r i b) f)

def MulTest : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (c : Fin (mdim k r i)) (f : Mx k r → ℂ),
    TestF k r i f →
      TestF k r i (fun g => yv k r z i g c * f g) ∧ TestF k r i (fun g => star (yv k r z i g c) * f g) ∧
      TestF k r i (fun g => ybv k r z i g c * f g) ∧ TestF k r i (fun g => star (ybv k r z i g c) * f g)

def TestInt : Prop :=
  ∀ (k r : ℕ) (i : Fin (r + 1)) (μ : Measure (Mt k r)), Formalism.FourierDecayAlt.B.IsHaarOn (Glev k r i) μ →
    ∀ (f h : Mx k r → ℂ), TestF k r i f → TestF k r i h →
      Integrable (fun x : Mt k r => f (Matrix.of x) * star (h (Matrix.of x))) μ

def EabAdj : Prop :=
  ∀ (k r : ℕ) (i : Fin (r + 1)) (μ : Measure (Mt k r)), Formalism.FourierDecayAlt.B.IsHaarOn (Glev k r i) μ →
    ∀ (a b : Fin (mdim k r i)) (f₁ f₂ : Mx k r → ℂ), TestF k r i f₁ → TestF k r i f₂ →
      pairL μ (EH k r (posL k r i a) (posL k r i b) f₁) f₂ =
        pairL μ f₁ (fun g => ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • EH k r (posL k r i c) (posL k r i d) f₂ g)

def EabAdjFrom : Prop := RdSkew → EabPres → EabTest → TestInt → EabAdj

def YbRel : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)), inWb k r z →
    ∀ g ∈ Glev k r i, ∀ c, ybv k r z i g c = ∑ l, Hm k r i l c * star (yv k r z i g l)

def XbRel : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)), inWb k r z' →
    ∀ c, xbv k r z' i c = ∑ l, Hm k r i l c * star (xv k r z' i l)

def HmFacts : Prop := ∀ (k r : ℕ) (i : Fin (r + 1)), (Hm k r i)ᴴ = Hm k r i ∧ Hm k r i * Hm k r i = 1

def Glue : Prop :=
  HermAlg → EabTest → EabAdj → MulTest → TestInt → YbRel → XbRel → HmFacts → EabPres → EabGlLev → YLeibniz →
    HermHaar

theorem hermFromSteps_of (hA : HermAlgFrom) (hE : EabAdjFrom) (hT : EabTest) (hM : MulTest) (hI : TestInt)
    (hY : YbRel) (hX : XbRel) (hH : HmFacts) (hG : Glue) : HermFromSteps := by
  intro hRd hSM hCC hMV hMC hYL hGl hEP
  exact hG (hA hSM hCC hMV hMC) hT (hE hRd hEP hT hI) hM hI hY hX hH hEP hGl hYL

theorem qnHermHaar_of (hA : HermAlgFrom) (hE : EabAdjFrom) (hT : EabTest) (hM : MulTest) (hI : TestInt)
    (hY : YbRel) (hX : XbRel) (hH : HmFacts) (hG : Glue) :
    RdSkew → StarMinor → ContractionsCovariant → MoveVec → MoveCov → YLeibniz → EabGlLev → EabPres → HermHaar :=
  hermFromSteps_of hA hE hT hM hI hY hX hH hG

end PI.QnHermHaar
