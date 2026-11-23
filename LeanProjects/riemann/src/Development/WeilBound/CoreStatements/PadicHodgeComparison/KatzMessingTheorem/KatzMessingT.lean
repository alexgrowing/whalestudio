import Mathlib

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace CompanionTheory.KM

variable (k : Type) [Field k] [Fintype k] (kb : Type) [Field kb] [IsAlgClosed kb] [Algebra k kb]

abbrev Sk : Scheme := Spec (CommRingCat.of k)

structure Var where
  Y : Scheme
  s : Y ⟶ Sk k
  smooth : Smooth s
  proper : IsProper s

variable {k}

def Pts {X : Scheme} (s : X ⟶ Sk k) : Type :=
  {y : Spec (CommRingCat.of kb) ⟶ X // y ≫ s = Spec.map (CommRingCat.ofHom (algebraMap k kb))}

structure Corr (Y : Var k) where
  C : Scheme
  c₁ : C ⟶ Y.Y
  c₂ : C ⟶ Y.Y
  base : c₁ ≫ Y.s = c₂ ≫ Y.s
  fin₁ : IsFinite c₁
  fin₂ : IsFinite c₂
  et₁ : Etale c₁
  et₂ : Etale c₂

def IsFrobK (σ : kb →+* kb) : Prop := ∀ x, σ x = x ^ Fintype.card k

def Fix {Y : Var k} (c : Corr Y) (σ : kb →+* kb) (n : ℕ) : Set (Spec (CommRingCat.of kb) ⟶ c.C) :=
  {z | z ≫ c.c₁ ≫ Y.s = Spec.map (CommRingCat.ofHom (algebraMap k kb)) ∧
    z ≫ c.c₂ = Spec.map (CommRingCat.ofHom (σ ^ n)) ≫ z ≫ c.c₁}

structure CohModel (F : Type) [Field F] where

  H : Var k → ℕ → Type
  [acg : ∀ Y i, AddCommGroup (H Y i)]
  [mod : ∀ Y i, Module F (H Y i)]
  [fd : ∀ Y i, FiniteDimensional F (H Y i)]
  top : Var k → ℕ
  vanish : ∀ Y i, top Y < i → Subsingleton (H Y i)
  frob : ∀ Y i, H Y i →ₗ[F] H Y i
  act : ∀ {Y : Var k}, Corr Y → ∀ i, H Y i →ₗ[F] H Y i
  comm : ∀ {Y : Var k} (c : Corr Y) i, act c i ∘ₗ frob Y i = frob Y i ∘ₗ act c i

attribute [instance] CohModel.acg CohModel.mod CohModel.fd

variable {F : Type} [Field F] {E : Type} [Field E] [CharZero E]

def CohModel.actQ [Algebra E F] (M : CohModel (k := k) F) {Y : Var k} (e : Corr Y →₀ E) (i : ℕ) :
    M.H Y i →ₗ[F] M.H Y i :=
  e.sum fun c a => algebraMap E F a • M.act c i

theorem CohModel.actQ_frob [Algebra E F] (M : CohModel (k := k) F) {Y : Var k} (e : Corr Y →₀ E) (i : ℕ)
    (y : M.H Y i) : M.actQ e i (M.frob Y i y) = M.frob Y i (M.actQ e i y) := by
  unfold CohModel.actQ Finsupp.sum
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [LinearMap.smul_apply, map_smul]
  rw [← LinearMap.comp_apply (M.act c i), M.comm c i, LinearMap.comp_apply]

def Lefschetz (M : CohModel (k := k) F) : Prop :=
  ∀ (Y : Var k) (c : Corr Y) (σ : kb →+* kb), IsFrobK (k := k) kb σ → ∀ n : ℕ, 1 ≤ n →
    (Fix kb c σ n).Finite ∧
    ∑ i ∈ Finset.range (M.top Y + 1), (-1 : F) ^ i * LinearMap.trace F (M.H Y i) (M.act c i ∘ₗ M.frob Y i ^ n) =
      (Nat.card ↥(Fix kb c σ n) : F)

def IsIdem [Algebra E F] (M : CohModel (k := k) F) {Y : Var k} (e : Corr Y →₀ E) : Prop :=
  ∀ i, M.actQ e i ∘ₗ M.actQ e i = M.actQ e i

def Conc [Algebra E F] (M : CohModel (k := k) F) {Y : Var k} (e : Corr Y →₀ E) (i₀ : ℕ) : Prop :=
  ∀ i, i ≠ i₀ → M.actQ e i = 0

def charPolE [Algebra E F] (M : CohModel (k := k) F) {Y : Var k} (e : Corr Y →₀ E) (i : ℕ) : Polynomial F :=
  LinearMap.charpoly (LinearMap.restrict (M.frob Y i) (p := LinearMap.range (M.actQ e i)) (q := LinearMap.range (M.actQ e i))
    (fun x hx => by
      obtain ⟨y, rfl⟩ := hx
      refine ⟨M.frob Y i y, ?_⟩
      exact M.actQ_frob e i y))

def KMCore : Prop :=
  ∀ (E F₁ F₂ : Type) [Field E] [CharZero E] [Field F₁] [Field F₂] [Algebra E F₁] [Algebra E F₂]
    (M₁ : CohModel (k := k) F₁) (M₂ : CohModel (k := k) F₂), Lefschetz kb M₁ → Lefschetz kb M₂ →
    (∃ σ : kb →+* kb, IsFrobK (k := k) kb σ) →
    ∀ (Y : Var k) (e : Corr Y →₀ E) (i₀ : ℕ), IsIdem M₁ e → IsIdem M₂ e → Conc M₁ e i₀ → Conc M₂ e i₀ →
      Module.finrank F₁ (LinearMap.range (M₁.actQ e i₀)) = Module.finrank F₂ (LinearMap.range (M₂.actQ e i₀)) →
      ∃ P : Polynomial E, charPolE M₁ e i₀ = P.map (algebraMap E F₁) ∧ charPolE M₂ e i₀ = P.map (algebraMap E F₂)

def KMConc : Prop :=
  ∀ (E F₁ F₂ : Type) [Field E] [CharZero E] [Field F₁] [Field F₂] [Algebra E F₁] [Algebra E F₂]
    (M₁ : CohModel (k := k) F₁) (M₂ : CohModel (k := k) F₂) (Y : Var k) (e : Corr Y →₀ E) (i₀ : ℕ),
    (∀ i, Module.finrank F₁ (LinearMap.range (M₁.actQ e i)) = Module.finrank F₂ (LinearMap.range (M₂.actQ e i))) →
    Conc M₂ e i₀ → Conc M₁ e i₀

def KatzMessingT (E : Type) [Field E] [CharZero E] {F₁ F₂ : Type} [Field F₁] [Field F₂] [Algebra E F₁] [Algebra E F₂]
    (M₁ : CohModel (k := k) F₁) (M₂ : CohModel (k := k) F₂) : Prop :=
  Lefschetz kb M₁ → Lefschetz kb M₂ → (∃ σ : kb →+* kb, IsFrobK (k := k) kb σ) →
    ∀ (Y : Var k) (e : Corr Y →₀ E) (i₀ : ℕ), IsIdem M₁ e → IsIdem M₂ e → Conc M₂ e i₀ →
      (∀ i, Module.finrank F₁ (LinearMap.range (M₁.actQ e i)) = Module.finrank F₂ (LinearMap.range (M₂.actQ e i))) →
      ∃ P : Polynomial E, charPolE M₁ e i₀ = P.map (algebraMap E F₁) ∧ charPolE M₂ e i₀ = P.map (algebraMap E F₂)

end CompanionTheory.KM
