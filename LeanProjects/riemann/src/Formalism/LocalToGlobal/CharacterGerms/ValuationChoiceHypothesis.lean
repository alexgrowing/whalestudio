import Formalism.LocalToGlobal.CharacterGerms.BiadditiveInSingleVariables
import Formalism.DropLevelBounds.ThBounds
import Formalism.DropLevelBounds.SumAdd
import Formalism.LocalToGlobal.Divisibility.Numbers

noncomputable section
open scoped BigOperators

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.BasicNotions

def i0 (k l : ℕ) : ℕ := sInf {i : ℕ | Odd i ∧ 3 ≤ i ∧ (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ i}

def ThlEq : Prop := ∀ k l : ℕ, 1 ≤ k → 2 ≤ l →
  Odd (i0 k l) ∧ 3 ≤ i0 k l ∧ (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ i0 k l ∧
    thl k l = ((l : ℝ) ^ i0 k l)⁻¹

def LevelBound : Prop := ∀ k l : ℕ, 1 ≤ k → 5 ≤ l → ((i0 k l : ℝ) - 1) ≤ 2 + 2 * Real.log k

structure Plan (l d : ℕ) [NeZero d] (W : ZMod d → ℕ) where
  y : ZMod d → ℕ → ℕ
  u : ZMod d → ℕ
  supp : ∀ a i, i ∉ oddLevels d → y a i = 0
  bal : ∀ a, W a = (∑ i ∈ oddLevels d, l ^ i * y a i) +
    (∑ i ∈ oddLevels d, y (a - (i : ZMod d)) i) + u a

def Plan.triv (l d : ℕ) [NeZero d] (W : ZMod d → ℕ) : Plan l d W where
  y := fun _ _ => 0
  u := W
  supp := fun _ _ _ => rfl
  bal := fun a => by simp

def blockBd (l n m i y : ℕ) : ℝ :=
  if y = 0 then 0 else bdP l i n n y + ((i : ℝ) + 1) * m * ((l : ℝ) ^ i + 1) * y / ((l : ℝ) - 1)

def chBd (l n m u : ℕ) : ℝ := (u : ℝ) * (n * gam l + m / ((l : ℝ) - 1))

def Plan.bound {l d : ℕ} [NeZero d] {W : ZMod d → ℕ} (p : Plan l d W) (n m : ℕ) : ℝ :=
  (∑ a, ∑ i ∈ oddLevels d, blockBd l n m i (p.y a i)) + ∑ a, chBd l n m (p.u a)

def Windows (S : ℕ) (G : Set ℕ) : Prop := 0 ∈ G ∧ ∀ Y0 : ℕ, ∃ y ∈ G, Y0 ≤ y ∧ y < Y0 + S

def Plan.Ok {l d : ℕ} [NeZero d] {W : ZMod d → ℕ} (p : Plan l d W) (k : ℕ)
    (Good : ZMod d → ℕ → Set ℕ) : Prop :=
  (∀ a i, i0 k l ≤ i → p.y a i = 0) ∧ (∀ a i, p.y a i ≠ 0 → p.y a i ∈ Good a i) ∧
    (((Finset.univ : Finset (ZMod d)) ×ˢ oddLevels d).filter fun x => p.y x.1 x.2 ≠ 0).card ≤ d

def WindowedChoiceExistsWithBound : Prop :=
  ∀ (l d : ℕ) [NeZero d], l.Prime → 5 ≤ l → 2 ≤ d → Even d → ∀ n m k S : ℕ, 1 ≤ n → 1 ≤ k → 1 ≤ S →
    ∀ (W : ZMod d → ℕ) (Good : ZMod d → ℕ → Set ℕ),
    (∀ a, ∀ i ∈ oddLevels d, i < i0 k l → Windows S (Good a i)) →
    ∃ p : Plan l d W, p.Ok k Good ∧
      p.bound n m ≤ Fnum l d (fun a => (n : ℝ) * W a) + thl k l * n * (∑ a, (W a : ℝ)) +
        (2 * (i0 k l : ℝ) - 1) * m * (∑ a, (W a : ℝ)) / ((l : ℝ) - 1) +
        d * (n * ((S : ℝ) + 1) + n * (Real.logb l n + 1))

def ContentOrbit : Prop :=
  ∀ (l d : ℕ) [NeZero d], l.Prime → 5 ≤ l → 2 ≤ d → Even d → ∀ n m k S : ℕ, 1 ≤ n → 1 ≤ k → 1 ≤ S →
    ∀ (W : ZMod d → ℕ) (Good : ZMod d → ℕ → Set ℕ) (T θ : ℝ) (w th : ZMod d → ℝ),
    (∀ a, ∀ i ∈ oddLevels d, i < i0 k l → Windows S (Good a i)) →
    0 < T → (∀ a, 0 < w a) → (∀ a, T * W a = w a * (1 - th a)) → (∀ a, 0 ≤ th a ∧ th a ≤ θ) →
    θ ≤ 1 / 2 →
    ∃ p : Plan l d W, p.Ok k Good ∧
      T * p.bound n m ≤ Fnum l d (fun a => (n : ℝ) * w a) + 6 * θ * n * (∑ a, w a) / l +
        thl k l * n * (∑ a, w a) + (2 * (i0 k l : ℝ) - 1) * m * (∑ a, w a) / ((l : ℝ) - 1) +
        T * (d * (n * ((S : ℝ) + 1) + n * (Real.logb l n + 1)))

def IsReps (N : NumDatum) (l : ℕ) (Z : Finset (RPl N.R)) : Prop :=
  ∀ z' : RPl N.R, ∃! p : RPl N.R × ZMod (N.ordP l), p.1 ∈ Z ∧ N.pos l p.1 p.2.val = z'

def alongOrb {X : Type} (N : NumDatum) (l : ℕ) (z : RPl N.R) (W : RPl N.R → X) : ZMod (N.ordP l) → X :=
  fun s => W (N.pos l z s.val)

def FInertReps : Prop :=
  ∀ (N : NumDatum) (j l : ℕ) (Z : Finset (RPl N.R)), IsReps N l Z →
    (N.cls l = PrimeClass.inertClass ∨ N.cls l = PrimeClass.signal) →
    ¬ (N.cls l = PrimeClass.inertClass ∧ N.hP l = 0) →
    N.FInert j l = ∑ z ∈ Z, Fnum l (N.ordP l)
        (fun s => ((N.R.k : ℝ) - 1) * alongOrb N l z (N.w j) s) ∧
      (l ≠ N.g 0 → l ≠ N.g 1 → (l : ℝ) ≤ N.sc.X'' N.R.n → N.FjP j l = N.FInert j l)

def ValHyp (N : NumDatum) (l : ℕ) (Z : Finset (RPl N.R)) (W : RPl N.R → ℕ)
    (Good : RPl N.R → ZMod (N.ordP l) → ℕ → Set ℕ) (rest ν : ℝ) : Prop :=
  ∀ p : ∀ z : RPl N.R, Plan l (N.ordP l) (alongOrb N l z W),
    (∀ z ∈ Z, (p z).Ok N.R.k (Good z)) →
    ν ≤ (∑ z ∈ Z, (p z).bound (N.R.k - 1) N.R.m) + rest / ((l : ℝ) - 1)

structure DegHyp (N : NumDatum) (j : ℕ) (W : RPl N.R → ℕ) (T θ rest C1 : ℝ) (th : RPl N.R → ℝ) :
    Prop where
  T_pos : 0 < T
  w_pos : ∀ z, 0 < N.w j z
  TW : ∀ z, T * W z = N.w j z * (1 - th z)
  th_rng : ∀ z, 0 ≤ th z ∧ th z ≤ θ
  th_half : θ ≤ 1 / 2
  th_m : 6 * θ * ((N.R.k : ℝ) - 1) ≤ 30 * N.R.m
  rest_nonneg : 0 ≤ rest
  rest_le : T * rest ≤ C1 * (N.R.f * N.R.k * (N.Sc + N.eta))

def errC (N : NumDatum) (j l : ℕ) (C T l1 : ℝ) : ℝ :=
  C * Real.log N.R.k * N.R.m * (∑ z, N.w j z) / l + C * (N.R.f * N.R.k * (N.Sc + N.eta)) / l +
    C * N.R.k * thl N.R.k l * (∑ z, N.w j z) + T * (C * addl N.R.k (N.R.k - 1) N.R.f l1 l)

def GoodHyp (N : NumDatum) (l : ℕ) (Z : Finset (RPl N.R))
    (Good : RPl N.R → ZMod (N.ordP l) → ℕ → Set ℕ) : Prop :=
  ∀ z ∈ Z, ∀ a, ∀ i ∈ oddLevels (N.ordP l), i < i0 N.R.k l →
    Windows (S0 l (i0 N.R.k l) (N.R.k - 1)) (Good z a i)

def ContentInertAt (C1 C : ℝ) : Prop :=
  ∀ (N : NumDatum) (j l : ℕ) (Z : Finset (RPl N.R)), l.Prime → 5 ≤ l → IsReps N l Z →
    (N.cls l = PrimeClass.inertClass ∨ N.cls l = PrimeClass.signal) →
    ¬ (N.cls l = PrimeClass.inertClass ∧ N.hP l = 0) →
    ∀ (W : RPl N.R → ℕ) (T θ rest l1 ν : ℝ) (th : RPl N.R → ℝ)
      (Good : RPl N.R → ZMod (N.ordP l) → ℕ → Set ℕ),
    DegHyp N j W T θ rest C1 th → GoodHyp N l Z Good → ValHyp N l Z W Good rest ν → (l : ℝ) < l1 →
      T * ν ≤ N.FInert j l + errC N j l C T l1 ∧
      (l ≠ N.g 0 → l ≠ N.g 1 → (l : ℝ) ≤ N.sc.X'' N.R.n → T * ν ≤ N.FjP j l + errC N j l C T l1) ∧
      ((∀ z z', N.w j z' ≤ l * N.w j z) →
        T * ν ≤ ((N.R.k : ℝ) - 1) * (∑ z, N.w j z) / ((l : ℝ) ^ 2 - 1) + errC N j l C T l1)

def ContentInert : Prop := ∀ C1 : ℝ, 0 ≤ C1 → ∃ C : ℝ, 0 < C ∧ ContentInertAt C1 C

structure Choice1 (l d : ℕ) [NeZero d] (W : ZMod d → ℕ) where
  Y : ZMod d → ℕ
  R1 : ZMod d → ℕ
  R2 : ZMod d → ℕ
  bal : ∀ a, W a = l * Y a + Y (a - 1) + R1 a + R2 a
  level_one_bound_le_succ : ∀ a, R1 a ≤ l + 1

def Choice1.bound {l d : ℕ} [NeZero d] {W : ZMod d → ℕ} (p : Choice1 l d W) (n m : ℕ) : ℝ :=
  (∑ a, 2 * (m : ℝ) * p.Y a) + ∑ a, chBd l n m (p.R2 a)

def LevelOneChoiceExists : Prop :=
  ∀ (l d : ℕ) [NeZero d], l.Prime → 2 ≤ d → Even d → ∀ n m k : ℕ, 1 ≤ n → 1 ≤ k → 2 * n + 2 < l →
    (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ 3 → ∀ W : ZMod d → ℕ,
    ∃ p : Choice1 l d W,
      p.bound n m ≤ Fnum l d (fun a => (n : ℝ) * W a) + thl k l * n * (∑ a, (W a : ℝ)) +
        3 * m * (∑ a, (W a : ℝ)) / ((l : ℝ) - 1)

def ValuationChoiceHypothesis (N : NumDatum) (l : ℕ) (Z : Finset (RPl N.R)) (W : RPl N.R → ℕ) (rest ν : ℝ) : Prop :=
  ∀ p : ∀ z : RPl N.R, Choice1 l (N.ordP l) (alongOrb N l z W),
    ν ≤ (∑ z ∈ Z, (p z).bound (N.R.k - 1) N.R.m) + rest / ((l : ℝ) - 1)

def ContentLargeAt (C1 C : ℝ) : Prop :=
  ∀ (N : NumDatum) (j l : ℕ) (Z : Finset (RPl N.R)), l.Prime → 5 ≤ l → IsReps N l Z →
    (N.cls l = PrimeClass.inertClass ∨ N.cls l = PrimeClass.signal) →
    ¬ (N.cls l = PrimeClass.inertClass ∧ N.hP l = 0) →
    2 * (N.R.k - 1) + 2 < l → (N.R.k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ 3 →
    ∀ (W : RPl N.R → ℕ) (T θ rest l1 ν : ℝ) (th : RPl N.R → ℝ),
    DegHyp N j W T θ rest C1 th → ValuationChoiceHypothesis N l Z W rest ν → l1 ≤ (l : ℝ) →
      addl N.R.k (N.R.k - 1) N.R.f l1 l = 0 ∧
      T * ν ≤ N.FInert j l + errC N j l C T l1 ∧
      (l ≠ N.g 0 → l ≠ N.g 1 → (l : ℝ) ≤ N.sc.X'' N.R.n → T * ν ≤ N.FjP j l + errC N j l C T l1) ∧
      ((∀ z z', N.w j z' ≤ l * N.w j z) →
        T * ν ≤ ((N.R.k : ℝ) - 1) * (∑ z, N.w j z) / ((l : ℝ) ^ 2 - 1) + errC N j l C T l1)

def ContentLarge : Prop := ∀ C1 : ℝ, 0 ≤ C1 → ∃ C : ℝ, 0 < C ∧ ContentLargeAt C1 C

def LemmaFe : Prop :=
  ∀ (l d : ℕ) [NeZero d], 2 ≤ l → 2 ≤ d → Even d → ∀ D : ZMod d → ℝ, (∀ a, 0 ≤ D a) →
    (∀ a a', D a' ≤ l * D a) → Fnum l d D = rho l * ∑ a, D a

def ContentSplit : Prop :=
  ∀ (N : NumDatum) (j l : ℕ), 2 ≤ l → ∀ (W : RPl N.R → ℕ) (T θ rest C1 ν : ℝ) (th : RPl N.R → ℝ),
    DegHyp N j W T θ rest C1 th →
    ν ≤ (∑ z, (W z : ℝ)) * N.R.m / ((l : ℝ) - 1) + rest / ((l : ℝ) - 1) →
    T * ν ≤ (N.R.m * (∑ z, N.w j z) + C1 * (N.R.f * N.R.k * (N.Sc + N.eta))) / ((l : ℝ) - 1)

def Sums : Prop := SumTh ∧ SumAdd

end Formalism.L2.FormalSeriesBounds
