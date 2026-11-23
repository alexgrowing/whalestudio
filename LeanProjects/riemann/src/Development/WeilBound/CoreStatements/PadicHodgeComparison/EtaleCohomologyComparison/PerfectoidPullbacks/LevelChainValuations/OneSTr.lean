import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

universe u

namespace CrystallineSemistableComparison.Pb.Kap

structure Chain (Λ A B K : Type) [CommRing Λ] [CommRing A] [CommRing B] [Field K] where
  ℓ : ℕ
  S : ℕ → ℕ → Type u
  [sab : ∀ n j, AddCommGroup (S n j)]
  [smd : ∀ n j, Module Λ (S n j)]
  Zn : ℕ → ℕ → Type u
  [znab : ∀ n j, AddCommGroup (Zn n j)]
  [znmd : ∀ n j, Module A (Zn n j)]
  Z : ℕ → Type u
  [zab : ∀ j, AddCommGroup (Z j)]
  [zmd : ∀ j, Module A (Z j)]
  W : ℕ → Type u
  [wab : ∀ j, AddCommGroup (W j)]
  [wmd : ∀ j, Module B (W j)]
  V : ℕ → Type u
  [vab : ∀ j, AddCommGroup (V j)]
  [vmd : ∀ j, Module K (V j)]
  lam : Λ →+* A
  ι : A →+* B
  o : K →+* B
  tS : ∀ n j, S (n + 1) j →ₗ[Λ] S n j
  tZ : ∀ n j, Zn (n + 1) j →ₗ[A] Zn n j
  r : ∀ n j, S n j →ₛₗ[lam] Zn n j
  red : ∀ n j, Z j →ₗ[A] Zn n j
  b : ∀ j, Z j →ₛₗ[ι] W j
  μ : ∀ j, V j →ₛₗ[o] W j

attribute [instance] Chain.sab Chain.smd Chain.znab Chain.znmd Chain.zab Chain.zmd Chain.wab Chain.wmd Chain.vab Chain.vmd

variable {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K]

namespace Chain

variable (C : Chain.{u} Λ A B K)

def Comp {j : ℕ} (x : ∀ n, C.S n j) : Prop := ∀ n, C.tS n j (x (n + 1)) = x n

structure Good : Prop where
  unit : IsUnit (C.ℓ : B)
  fin : ∀ j, FiniteDimensional K (C.V j)
  basis : ∀ (j : ℕ) {m : ℕ} (bs : Module.Basis (Fin m) K (C.V j)) (w : C.W j),
    ∃! g : Fin m → B, w = ∑ s, g s • C.μ j (bs s)
  r_tr : ∀ n j (x : C.S (n + 1) j), C.tZ n j (C.r (n + 1) j x) = C.r n j (C.tS n j x)
  red_tr : ∀ n j (z : C.Z j), C.tZ n j (C.red (n + 1) j z) = C.red n j z
  lift : ∀ j (x : ∀ n, C.S n j), C.Comp x → ∃ (e : ℕ) (z : C.Z j), ∀ n, C.red n j z = ((C.ℓ : A) ^ e) • C.r n j (x n)
  sep : ∀ j (z : C.Z j), (∀ n, C.red n j z = 0) → C.b j z = 0

def Rho {j : ℕ} (x : ∀ n, C.S n j) (f : Module.Dual K (C.V j) →+ B) : Prop :=
  (∀ (k : K) (φ : Module.Dual K (C.V j)), f (k • φ) = C.o k * f φ) ∧
  ∃ (e : ℕ) (z : C.Z j), (∀ n, C.red n j z = ((C.ℓ : A) ^ e) • C.r n j (x n)) ∧
    ∀ {m : ℕ} (bs : Module.Basis (Fin m) K (C.V j)), ((C.ℓ : B) ^ e) • ∑ s, f (bs.coord s) • C.μ j (bs s) = C.b j z

end Chain

structure Hom {Λ' A' B' : Type} [CommRing Λ'] [CommRing A'] [CommRing B'] (C : Chain.{u} Λ A B K)
    (C' : Chain.{u} Λ' A' B' K) where
  sΛ : Λ →+* Λ'
  sA : A →+* A'
  sB : B →+* B'
  fS : ∀ n j, C.S n j →ₛₗ[sΛ] C'.S n j
  fZn : ∀ n j, C.Zn n j →ₛₗ[sA] C'.Zn n j
  fZ : ∀ j, C.Z j →ₛₗ[sA] C'.Z j
  fW : ∀ j, C.W j →ₛₗ[sB] C'.W j
  fV : ∀ j, C.V j →ₗ[K] C'.V j

structure Hom.Good {Λ' A' B' : Type} [CommRing Λ'] [CommRing A'] [CommRing B'] {C : Chain.{u} Λ A B K}
    {C' : Chain.{u} Λ' A' B' K} (h : Hom C C') : Prop where
  ℓ : C'.ℓ = C.ℓ
  lam : ∀ c, h.sA (C.lam c) = C'.lam (h.sΛ c)
  ι : ∀ a, h.sB (C.ι a) = C'.ι (h.sA a)
  o : ∀ k, h.sB (C.o k) = C'.o k
  tS : ∀ n j x, h.fS n j (C.tS n j x) = C'.tS n j (h.fS (n + 1) j x)
  r : ∀ n j x, h.fZn n j (C.r n j x) = C'.r n j (h.fS n j x)
  red : ∀ n j z, h.fZn n j (C.red n j z) = C'.red n j (h.fZ j z)
  b : ∀ j z, h.fW j (C.b j z) = C'.b j (h.fZ j z)
  μ : ∀ j v, h.fW j (C.μ j v) = C'.μ j (h.fV j v)

def Hom.tr {Λ' A' B' : Type} [CommRing Λ'] [CommRing A'] [CommRing B'] {C : Chain.{u} Λ A B K}
    {C' : Chain.{u} Λ' A' B' K} (h : Hom C C') (j : ℕ) (f : Module.Dual K (C.V j) →+ B) :
    Module.Dual K (C'.V j) →+ B' :=
  h.sB.toAddMonoidHom.comp (f.comp (Module.Dual.transpose (R := K) (h.fV j)).toAddMonoidHom)

structure Cup (C : Chain.{u} Λ A B K) where
  cS : ∀ n i j, C.S n i →ₗ[Λ] C.S n j →ₗ[Λ] C.S n (i + j)
  cZn : ∀ n i j, C.Zn n i →ₗ[A] C.Zn n j →ₗ[A] C.Zn n (i + j)
  cZ : ∀ i j, C.Z i →ₗ[A] C.Z j →ₗ[A] C.Z (i + j)
  cW : ∀ i j, C.W i →ₗ[B] C.W j →ₗ[B] C.W (i + j)
  cV : ∀ i j, C.V i →ₗ[K] C.V j →ₗ[K] C.V (i + j)
  oneS : ∀ n, C.S n 0
  oneZ : C.Z 0
  oneV : C.V 0

structure Cup.Good {C : Chain.{u} Λ A B K} (P : Cup C) : Prop where
  r : ∀ n i j x y, C.r n (i + j) (P.cS n i j x y) = P.cZn n i j (C.r n i x) (C.r n j y)
  red : ∀ n i j z w, C.red n (i + j) (P.cZ i j z w) = P.cZn n i j (C.red n i z) (C.red n j w)
  b : ∀ i j z w, C.b (i + j) (P.cZ i j z w) = P.cW i j (C.b i z) (C.b j w)
  μ : ∀ i j v w, C.μ (i + j) (P.cV i j v w) = P.cW i j (C.μ i v) (C.μ j w)
  tS : ∀ n i j x y, C.tS n (i + j) (P.cS (n + 1) i j x y) = P.cS n i j (C.tS n i x) (C.tS n j y)
  oneS_tr : ∀ n, C.tS n 0 (P.oneS (n + 1)) = P.oneS n
  one_r : ∀ n, C.red n 0 P.oneZ = C.r n 0 (P.oneS n)
  one_b : C.b 0 P.oneZ = C.μ 0 P.oneV

end CrystallineSemistableComparison.Pb.Kap
