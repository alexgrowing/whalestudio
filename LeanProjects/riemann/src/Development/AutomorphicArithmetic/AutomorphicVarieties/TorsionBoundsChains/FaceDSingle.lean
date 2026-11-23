import Mathlib

open CategoryTheory

namespace UpperTheory.V.KH

def TorsLe (M : Type) [AddCommGroup M] (B : ℕ) : Prop :=
  Finite (AddCommGroup.torsion M) ∧ Nat.card (AddCommGroup.torsion M) ≤ B

def CardLe (M : Type) (B : ℕ) : Prop := Finite M ∧ Nat.card M ≤ B

noncomputable abbrev HZ (G : Type) [Group G] (m : ℕ) : ModuleCat ℤ :=
  groupHomology (Rep.trivial ℤ G ℤ) m

noncomputable def perm (G X : Type) [Group G] [MulAction G X] : Representation ℤ G (X →₀ ℤ) where
  toFun g := Finsupp.lmapDomain ℤ ℤ (fun x : X => g • x)
  map_one' := by ext x y; simp
  map_mul' g h := by ext x y; simp [mul_smul]

@[simp] theorem perm_single {G X : Type} [Group G] [MulAction G X] (g : G) (x : X) (c : ℤ) :
    perm G X g (Finsupp.single x c) = Finsupp.single (g • x) c := by
  simp [perm]

theorem perm_apply {G X : Type} [Group G] [MulAction G X] (g : G) (f : X →₀ ℤ) :
    perm G X g f = Finsupp.mapDomain (fun x : X => g • x) f := rfl

noncomputable abbrev permRep (G X : Type) [Group G] [MulAction G X] : Rep ℤ G := Rep.of (perm G X)

def l1 {X : Type} (f : X →₀ ℤ) : ℕ := f.sum fun _ c => c.natAbs

def OrbLe (G X : Type) [Group G] [MulAction G X] (A : ℕ) : Prop :=
  CardLe (MulAction.orbitRel.Quotient G X) A

def StabLe (G X : Type) [Group G] [MulAction G X] (s : ℕ) : Prop :=
  ∀ x : X, CardLe (MulAction.stabilizer G x) s

structure PermCx (G : Type) [Group G] (X : ℕ → Type) [∀ p, MulAction G (X p)] where
  d : ∀ p, (X (p + 1) →₀ ℤ) →ₗ[ℤ] (X p →₀ ℤ)
  ε : (X 0 →₀ ℤ) →ₗ[ℤ] ℤ
  d_equiv : ∀ p (g : G) (f : X (p + 1) →₀ ℤ), d p (perm G _ g f) = perm G _ g (d p f)
  ε_equiv : ∀ (g : G) (f : X 0 →₀ ℤ), ε (perm G _ g f) = ε f

def PermCx.ExactTo {G : Type} [Group G] {X : ℕ → Type} [∀ p, MulAction G (X p)]
    (C : PermCx G X) (m : ℕ) : Prop :=
  Function.Surjective C.ε ∧ Function.Exact (C.d 0) C.ε ∧
    ∀ p, p < m → Function.Exact (C.d (p + 1)) (C.d p)

noncomputable def faceD {Y X : Type} {k : ℕ} (face : Fin k → Y → X) :
    (Y →₀ ℤ) →ₗ[ℤ] (X →₀ ℤ) :=
  ∑ i : Fin k, ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.lmapDomain ℤ ℤ (face i)

noncomputable def aug (X : Type) : (X →₀ ℤ) →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ : X => (1 : ℤ))

theorem faceD_single {Y X : Type} {k : ℕ} (face : Fin k → Y → X) (y : Y) (c : ℤ) :
    faceD face (Finsupp.single y c) =
      ∑ i : Fin k, ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (face i y) c := by
  simp only [faceD, LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]

@[simp] theorem aug_single {X : Type} (x : X) (c : ℤ) : aug X (Finsupp.single x c) = c := by
  simp [aug]

def FaceExactTo (X : ℕ → Type) (face : ∀ p, Fin (p + 2) → X (p + 1) → X p) (m : ℕ) : Prop :=
  Function.Surjective (aug (X 0)) ∧ Function.Exact (faceD (face 0)) (aug (X 0)) ∧
    ∀ p, p < m → Function.Exact (faceD (face (p + 1))) (faceD (face p))

noncomputable def faceCx (G : Type) [Group G] (X : ℕ → Type) [∀ p, MulAction G (X p)]
    (face : ∀ p, Fin (p + 2) → X (p + 1) → X p)
    (h : ∀ p i (g : G) (x : X (p + 1)), face p i (g • x) = g • face p i x) : PermCx G X where
  d p := faceD (face p)
  ε := aug (X 0)
  d_equiv p g f := by
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single x c => simp only [perm_single, faceD_single, map_sum, map_smul, h]
  ε_equiv g f := by
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single x c => simp

def Chain (P : Type) [Preorder P] (p : ℕ) : Type := {f : Fin (p + 1) → P // StrictMono f}

def Chain.face (P : Type) [Preorder P] (p : ℕ) (i : Fin (p + 2)) (c : Chain P (p + 1)) :
    Chain P p :=
  ⟨fun j => c.1 (i.succAbove j), c.2.comp (Fin.strictMono_succAbove i)⟩

instance Chain.mulAction (G P : Type) [Group G] [Preorder P] [MulAction G P]
    [CovariantClass G P (· • ·) (· < ·)] (p : ℕ) : MulAction G (Chain P p) where
  smul g c := ⟨fun j => g • c.1 j, fun _ _ hab =>
    CovariantClass.elim (μ := fun (g : G) (x : P) => g • x) (r := (· < ·)) g (c.2 hab)⟩
  one_smul c := Subtype.ext (funext fun j => one_smul G (c.1 j))
  mul_smul g h c := Subtype.ext (funext fun j => mul_smul g h (c.1 j))

theorem Chain.smul_val {G P : Type} [Group G] [Preorder P] [MulAction G P]
    [CovariantClass G P (· • ·) (· < ·)] {p : ℕ} (g : G) (c : Chain P p) (j : Fin (p + 1)) :
    (g • c).1 j = g • c.1 j := rfl

theorem Chain.face_smul {G P : Type} [Group G] [Preorder P] [MulAction G P]
    [CovariantClass G P (· • ·) (· < ·)] (p : ℕ) (i : Fin (p + 2)) (g : G)
    (c : Chain P (p + 1)) : Chain.face P p i (g • c) = g • Chain.face P p i c := rfl

def OrdExactTo (P : Type) [Preorder P] (m : ℕ) : Prop := FaceExactTo (Chain P) (Chain.face P) m

def bound (m A s b : ℕ) : ℕ := b ^ A * s ^ (m * A * s ^ m)

instance : Inhabited (Chain Unit 0) := ⟨⟨fun _ => (), fun a b h => absurd h (by omega)⟩⟩

end UpperTheory.V.KH
