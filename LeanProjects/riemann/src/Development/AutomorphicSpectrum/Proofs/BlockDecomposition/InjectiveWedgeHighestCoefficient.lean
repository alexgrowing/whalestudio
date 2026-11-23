import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.NoSecondTypeWeight
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy

noncomputable section

open Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.PairMult

open Formalism.REAL (GlRel qdet)
open CompanionTheory.D.LK (Pos)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

variable {n : ℕ}

abbrev Lt (n : ℕ) : Type := Bool × Pos n

abbrev Cq (n : ℕ) (V : Type) : Type := Finset (Lt n) → V

def keyL (l : Lt n) : ℕ := (if l.1 then 0 else (n + 1) * (n + 1)) + CompanionTheory.D.LK.key l.2

def sgL (l : Lt n) (A : Finset (Lt n)) : ℂ := (-1) ^ (A.filter fun j => keyL j < keyL l).card

section Chains

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def annq (l : Lt n) : Module.End ℂ (Cq n V) where
  toFun x := fun A => if l ∈ A then 0 else sgL l A • x (insert l A)
  map_add' x y := by funext A; by_cases h : l ∈ A <;> simp [h]
  map_smul' c x := by funext A; by_cases h : l ∈ A <;> simp [h, smul_comm c]

def creq (l : Lt n) : Module.End ℂ (Cq n V) where
  toFun x := fun A => if l ∈ A then sgL l A • x (A.erase l) else 0
  map_add' x y := by funext A; by_cases h : l ∈ A <;> simp [h]
  map_smul' c x := by funext A; by_cases h : l ∈ A <;> simp [h, smul_comm c]

def liftq (n : ℕ) {V' : Type} [AddCommGroup V'] [Module ℂ V'] (T : V →ₗ[ℂ] V') : Cq n V →ₗ[ℂ] Cq n V' :=
  T.compLeft (Finset (Lt n))

def Ts (E1 E2 : Fin n → Fin n → Module.End ℂ V) (s : Bool) (p q : Fin n) : Module.End ℂ V :=
  if s then E1 p q + E2 p q else E1 p q - E2 p q

def Tl (E1 E2 : Fin n → Fin n → Module.End ℂ V) (l : Lt n) : Module.End ℂ V := Ts E1 E2 l.1 l.2.1.1 l.2.1.2

def bdq (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ (Cq n V) :=
  (∑ l : Lt n, (liftq n (Tl E1 E2 l) : Module.End ℂ (Cq n V)) * annq l) +
    ∑ s : Bool, ∑ t : Bool, ∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
      if i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then creq ((s == t), k) * annq (t, j) * annq (s, i) else 0

def SuppQ (P : Lt n → Prop) (y : Cq n V) : Prop := ∀ A, y A ≠ 0 → ∀ l ∈ A, P l

def DegQ (j : ℕ) (y : Cq n V) : Prop := ∀ A, y A ≠ 0 → A.card = j

def adLq (s : Bool) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  ∑ t : Bool, ∑ i : Pos n, ∑ k : Pos n, CompanionTheory.RgExh.U.adC p q i k • (creq ((s == t), k) * annq (t, i))

def lFq (E1 E2 : Fin n → Fin n → Module.End ℂ V) (s : Bool) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  liftq n (Ts E1 E2 s p q) + adLq s p q

def c1 (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  (1 / 2 : ℂ) • (lFq E1 E2 true p q + lFq E1 E2 false p q)

def c2 (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  (1 / 2 : ℂ) • (lFq E1 E2 true p q - lFq E1 E2 false p q)

end Chains

abbrev inUL (lev : Fin n → ℕ) (l : Lt n) : Prop := lev l.2.1.1 < lev l.2.1.2

abbrev inKU (lev : Fin n → ℕ) (l : Lt n) : Prop := l.1 = true ∧ lev l.2.1.1 < lev l.2.1.2

def omQ (lev : Fin n → ℕ) : Finset (Lt n) := univ.filter fun l => l.1 = true ∧ lev l.2.1.1 < lev l.2.1.2

def topq {V : Type} [AddCommGroup V] [Module ℂ V] (lev : Fin n → ℕ) (v : V) : Cq n V := Pi.single (omQ lev) v

def IsSubL (lev : Fin n → ℕ) (S : Lt n → Prop) : Prop :=
  (∀ l, S l → inUL lev l) ∧ ∀ (s t : Bool) (i j k : Pos n), i.1.2 = j.1.1 → k.1.1 = i.1.1 → k.1.2 = j.1.2 →
    S (s, i) → S (t, j) → S ((s == t), k)

section Algebra

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def PairRel (E1 E2 : Fin n → Fin n → Module.End ℂ W) : Prop :=
  GlRel E1 ∧ GlRel E2 ∧ ∀ a b c d, Commute (E1 a b) (E2 c d)

def ev2 (E1 E2 : Fin n → Fin n → Module.End ℂ W) : FreeAlgebra ℂ (Bool × Fin n × Fin n) →ₐ[ℂ] Module.End ℂ W :=
  FreeAlgebra.lift ℂ fun x => if x.1 then E1 x.2.1 x.2.2 else E2 x.2.1 x.2.2

def evB (lev : Fin n → ℕ) (X1 X2 : Fin n → Fin n → Module.End ℂ W) :
    FreeAlgebra ℂ (Bool × Fin n × Fin n) →ₐ[ℂ] Module.End ℂ W :=
  FreeAlgebra.lift ℂ fun x => if lev x.2.1 = lev x.2.2 then (if x.1 then X1 x.2.1 x.2.2 else X2 x.2.1 x.2.2) else 0

def LRel (lev : Fin n → ℕ) (X1 X2 : Fin n → Fin n → Module.End ℂ W) : Prop :=
  (∀ p q r v, lev p = lev q → lev r = lev v →
    X1 p q * X1 r v - X1 r v * X1 p q = (if q = r then X1 p v else 0) - (if v = p then X1 r q else 0)) ∧
  (∀ p q r v, lev p = lev q → lev r = lev v →
    X2 p q * X2 r v - X2 r v * X2 p q = (if q = r then X2 p v else 0) - (if v = p then X2 r q else 0)) ∧
  ∀ p q r v, lev p = lev q → lev r = lev v → Commute (X1 p q) (X2 r v)

def blk (lev : Fin n → ℕ) {M : ℕ} (h : ∑ i, GlobalTheory.CompanionTheory.RgCOBlock.sz lev M i = n) (X : Fin n → Fin n → Module.End ℂ W)
    (i : Fin M) (p q : Fin (GlobalTheory.CompanionTheory.RgCOBlock.sz lev M i)) : Module.End ℂ W :=
  X (GlobalTheory.SmGL.stdBlocks (GlobalTheory.CompanionTheory.RgCOBlock.sz lev M) h ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks (GlobalTheory.CompanionTheory.RgCOBlock.sz lev M) h ⟨i, q⟩)

end Algebra

def Inv2 (a : FreeAlgebra ℂ (Bool × Fin n × Fin n)) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
    ∀ c d, Commute (E1 c d + E2 c d) (ev2 E1 E2 a)

def InvLev (lev : Fin n → ℕ) (b : FreeAlgebra ℂ (Bool × Fin n × Fin n)) : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (X1 X2 : Fin n → Fin n → Module.End ℂ W), LRel lev X1 X2 →
    ∀ p q, lev p = lev q → Commute (X1 p q + X2 p q) (evB lev X1 X2 b)

def injL (s : Bool) : FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] FreeAlgebra ℂ (Bool × Fin n × Fin n) :=
  FreeAlgebra.lift ℂ fun p => FreeAlgebra.ι ℂ (s, p)

def LiftInv : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℝ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
    (∀ a b (x y : V), ⟪kF E1 E2 a b x, y⟫_ℂ = ⟪x, kF E1 E2 b a y⟫_ℂ) →
    (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF E1 E2 a b w ∈ S) →
    ∀ v w : V, v ≠ 0 → v ∈ hwSp E1 E2 μ → w ∈ hwSp E1 E2 μ → (∃ x ∈ alg E1 E2, x v = w) →
      ∃ a, Inv2 a ∧ ev2 E1 E2 a v = w

def HCDec2 : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ) (a : FreeAlgebra ℂ (Bool × Fin n × Fin n)), Monotone lev → Inv2 a →
    ∃ b : FreeAlgebra ℂ (Bool × Fin n × Fin n), ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 → ∀ x : V, ∃ w : Lt n → V,
        ev2 E1 E2 a x - evB lev E1 E2 b x = ∑ l : Lt n, if inUL lev l then Tl E1 E2 l (w l) else 0

def GenCOU2 : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ) (S : Lt n → Prop) (a b : FreeAlgebra ℂ (Bool × Fin n × Fin n)), Monotone lev → IsSubL lev S →
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
      (∀ l, S l → Commute (Tl E1 E2 l) (ev2 E1 E2 a)) ∧
      ∀ x : V, ∃ w : Lt n → V, ev2 E1 E2 a x - evB lev E1 E2 b x = ∑ l : Lt n, if inUL lev l then Tl E1 E2 l (w l) else 0) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
      ∀ (j : ℕ) (x : Cq n V), SuppQ S x → DegQ j x → bdq E1 E2 x = 0 →
        ∃ w : Cq n V, SuppQ (inUL lev) w ∧ DegQ (j + 1) w ∧
          liftq n (ev2 E1 E2 a) x - evB lev (c1 E1 E2) (c2 E1 E2) b x = bdq E1 E2 w

def TopCyc : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
    PairRel E1 E2 → ∀ v : V, (∀ l, inKU lev l → Tl E1 E2 l v = 0) → bdq E1 E2 (topq lev v) = 0

def InjectiveWedgeHighestCoefficient : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      AdmFor lam lev E1 E2 → ∀ (u : V) (y : Cq n V), u ∈ hwSp E1 E2 (muQ lam lev) → SuppQ (inUL lev) y →
        DegQ ((omQ lev).card + 1) y → bdq E1 E2 y = topq lev u → u = 0

def KlChar : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ), IsLev lam lev →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      AdmFor lam lev E1 E2 → ∀ x ∈ hwSp E1 E2 (muQ lam lev), ∀ p q, lev p = lev q →
        lFq E1 E2 true p q (topq lev x) =
          if p = q then ((muQ lam lev p + 2 * rhoU lev p : ℝ) : ℂ) • topq lev x else 0

def LeviRel : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
    Monotone lev → PairRel E1 E2 → ∀ x : Cq n V, SuppQ (inUL lev) x →
      (∀ s p q, lev p = lev q → SuppQ (inUL lev) (lFq E1 E2 s p q x) ∧ (∀ j, DegQ j x → DegQ j (lFq E1 E2 s p q x)) ∧
        lFq E1 E2 s p q (bdq E1 E2 x) = bdq E1 E2 (lFq E1 E2 s p q x)) ∧
      ∀ p q r v, lev p = lev q → lev r = lev v →
        (c1 E1 E2 p q (c1 E1 E2 r v x) - c1 E1 E2 r v (c1 E1 E2 p q x) =
          (if q = r then c1 E1 E2 p v x else 0) - (if v = p then c1 E1 E2 r q x else 0)) ∧
        (c2 E1 E2 p q (c2 E1 E2 r v x) - c2 E1 E2 r v (c2 E1 E2 p q x) =
          (if q = r then c2 E1 E2 p v x else 0) - (if v = p then c2 E1 E2 r q x else 0)) ∧
        c1 E1 E2 p q (c2 E1 E2 r v x) = c2 E1 E2 r v (c1 E1 E2 p q x)

def InvL : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (X1 X2 : Fin n → Fin n → Module.End ℂ W)
    (L : Submodule ℂ W) (b : FreeAlgebra ℂ (Bool × Fin n × Fin n)), LRel lev X1 X2 →
    (∀ p q, lev p = lev q → ∀ s ∈ L, (X1 p q + X2 p q) s ∈ L) →
    (∀ p q, lev p = lev q → ∀ s ∈ L, (X1 p q + X2 p q) (evB lev X1 X2 b s) = evB lev X1 X2 b ((X1 p q + X2 p q) s)) →
    ∃ b', InvLev lev b' ∧ ∀ s ∈ L, evB lev X1 X2 b' s = evB lev X1 X2 b s

def CenterScalar : Prop :=
  ∀ (n M : ℕ) (lev : Fin n → ℕ) (h : ∑ i, GlobalTheory.CompanionTheory.RgCOBlock.sz lev M i = n), Monotone lev → (∀ a, lev a < M) →
    ∀ b : FreeAlgebra ℂ (Bool × Fin n × Fin n), InvLev lev b → ∀ τ : Fin n → ℂ, (∀ a c, lev a = lev c → τ a = τ c) →
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (X1 X2 : Fin n → Fin n → Module.End ℂ W), LRel lev X1 X2 →
        ∀ t : W, (∀ p q, lev p = lev q → (X1 p q + X2 p q) t = if p = q then τ p • t else 0) →
          (∀ (i : Fin M) (u : ℂ), ∃ g : ℂ, qdet (blk lev h X1 i) u t = g • t) → ∃ s : ℂ, evB lev X1 X2 b t = s • t

def BlockSplit : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (t : W) (n M : ℕ) (lev : Fin n → ℕ) (L : Fin n → ℝ)
    (A B : ∀ i : Fin M, Fin (GlobalTheory.CompanionTheory.RgCOBlock.sz lev M i) → Fin (GlobalTheory.CompanionTheory.RgCOBlock.sz lev M i) → Module.End ℂ W)
    (s τ : Fin M → ℂ), t ≠ 0 → Monotone lev → (∀ a, lev a < M) → StrictAnti L → (∀ i, GlRel (A i)) → (∀ i, GlRel (B i)) →
    (∀ i j, i ≠ j → ∀ p q r v, Commute (A i p q) (A j r v)) → (∀ i j, i ≠ j → ∀ p q r v, Commute (B i p q) (B j r v)) →
    (∀ i j p q r v, Commute (A i p q) (B j r v)) →
    (∀ Y : ℂ, (List.ofFn fun i => qdet (A i) (Y + s i)).prod = Formalism.QuantumDeterminants.capP (fun a => (L a : ℂ)) Y • (1 : Module.End ℂ W)) →
    (∀ Y : ℂ, (List.ofFn fun i => qdet (B i) (Y + s i)).prod = Formalism.QuantumDeterminants.capP (fun a => (L a : ℂ)) Y • (1 : Module.End ℂ W)) →
    (∀ i, (∑ p, (A i p p + B i p p)) t = τ i • t) →
    (∀ i : Fin M, τ i = 2 * ∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), (L a : ℂ) +
      (GlobalTheory.CompanionTheory.RgCOBlock.sz lev M i : ℂ) * ((GlobalTheory.CompanionTheory.RgCOBlock.sz lev M i : ℂ) - 1) - 2 * (GlobalTheory.CompanionTheory.RgCOBlock.sz lev M i : ℂ) * s i) →
    ∀ (i : Fin M) (Y : ℂ), qdet (A i) (Y + s i) t = (∏ a ∈ univ.filter (fun a => lev a = (i : ℕ)), (Y + (L a : ℂ))) • t

def CapOne : Prop :=
  ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (χ : Fin n → ℂ),
    GlRel E → (∀ m (x : V), gelA E m x = GlobalTheory.Dec.gelfVal χ m • x) →
      ∀ Y : ℂ, qdet E (Y + ((n : ℂ) - 1) / 2) = Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ V)

def DualCap : Prop :=
  ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (χ : Fin n → ℂ),
    GlRel E → (∀ m (x : V), gelA (barF E) m x = GlobalTheory.Dec.gelfVal (fun a => -χ a) m • x) →
      ∀ Y : ℂ, qdet E (Y + ((n : ℂ) - 1) / 2) = Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ V)

def CapProd : Prop :=
  ∀ (n M : ℕ) (lev : Fin n → ℕ) (h : ∑ i, GlobalTheory.CompanionTheory.RgCOBlock.sz lev M i = n), Monotone lev → (∀ a, lev a < M) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
      ∀ (s : Bool) (Y r : ℂ), qdet (if s then E1 else E2) (Y + ((n : ℂ) - 1) / 2) = r • (1 : Module.End ℂ V) →
        ∀ (j : ℕ) (x : Cq n V), SuppQ (inUL lev) x → DegQ j x → bdq E1 E2 x = 0 →
          ∃ w : Cq n V, SuppQ (inUL lev) w ∧ DegQ (j + 1) w ∧
            r • x - evB lev (c1 E1 E2) (c2 E1 E2) (injL s (GlobalTheory.CompanionTheory.RgCOBlock.fb (GlobalTheory.CompanionTheory.RgCOBlock.sz lev M) h Y)) x = bdq E1 E2 w

def LeviScalar : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      AdmFor lam lev E1 E2 → ∀ v w : V, v ∈ hwSp E1 E2 (muQ lam lev) → w ∈ hwSp E1 E2 (muQ lam lev) → v ≠ 0 →
        ∀ b : FreeAlgebra ℂ (Bool × Fin n × Fin n),
          (∃ y : Cq n V, SuppQ (inUL lev) y ∧ DegQ ((omQ lev).card + 1) y ∧
            topq lev w - evB lev (c1 E1 E2) (c2 E1 E2) b (topq lev v) = bdq E1 E2 y) →
          ∃ (s : ℂ) (y : Cq n V), SuppQ (inUL lev) y ∧ DegQ ((omQ lev).card + 1) y ∧
            topq lev w - s • topq lev v = bdq E1 E2 y

end GlobalTheory.CompanionTheory.PairMult
