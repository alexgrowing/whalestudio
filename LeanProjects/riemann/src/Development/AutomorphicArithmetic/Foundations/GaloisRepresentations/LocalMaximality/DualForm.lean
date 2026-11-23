import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 GlobalTheory.W1.Lef
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section
variable {F : Type} [Field F] [Algebra ℂ F] {V V' : Type} [AddCommGroup V] [Module F V] [Module ℂ V] [IsScalarTower ℂ F V]
  [AddCommGroup V'] [Module F V'] [Module ℂ V'] [IsScalarTower ℂ F V']

def Lat (A : Subalgebra ℂ F) (M : Submodule ℂ V) : Prop :=
  (∀ a ∈ A, ∀ m ∈ M, a • m ∈ M) ∧ ∃ (n : ℕ) (v : Fin n → V) (φ : Fin n → V →ₗ[F] F), (∀ k, v k ∈ M) ∧ (∀ k, ∀ m ∈ M, φ k m ∈ A) ∧
    ∀ m ∈ M, m = ∑ k, φ k m • v k

variable (F V V') in

def actF : F ⊗[ℂ] F →ₐ[ℂ] Module.End ℂ (V ⊗[ℂ] V') :=
  (Module.endTensorEndAlgHom).comp (Algebra.TensorProduct.map (Algebra.lsmul ℂ ℂ V) (Algebra.lsmul ℂ ℂ V'))

variable (V') in

def ctrF (ψ : V →ₗ[F] F) : V ⊗[ℂ] V' →ₗ[ℂ] V' := TensorProduct.lift ((Algebra.lsmul ℂ ℂ V').toLinearMap ∘ₗ ψ.restrictScalars ℂ)

def f0 {d : ℕ} (x : Fin (d + 1) → Fˣ) (j : Fin (d + 1)) (l : Fin d) : F ⊗[ℂ] F :=
  ((x (j.succAbove l) : F) / x j) ⊗ₜ 1 - 1 ⊗ₜ ((x (j.succAbove l) : F) / x j)

def R0 {d : ℕ} (x : Fin (d + 1) → Fˣ) (I J : Finset (Fin (d + 1))) : Subalgebra ℂ (F ⊗[ℂ] F) :=
  (Algebra.TensorProduct.map (rA ℂ (xv x) I).val (rA ℂ (xv x) J).val).range

def omG {d : ℕ} (x : Fin (d + 1) → Fˣ) (i : Fin (d + 1)) : F := ∏ l, ((x l : F) / x i)

variable (V') in

def resP (ρ : F →ₗ[ℂ] ℂ) : F ⊗[ℂ] V' →ₗ[ℂ] V' := TensorProduct.lift ((LinearMap.lsmul ℂ V') ∘ₗ ρ)

end

section
variable {F : Type} (K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}
  (x : Fin (d + 1) → Fˣ)

structure ZF {κ : Type} [LinearOrder κ] (n : κ → ℕ × ℕ) (z : κ → K ⊗[ℂ] K) : Prop where
  adm : (sysZ K x 0).admitted n z
  diag : ∀ l, Algebra.TensorProduct.lmul' ℂ (z l) = 0
  gen : ∀ i, Algebra.adjoin ℂ {b : K | b ∈ rB ℂ K (xv x) {i} ∧ ∃ l N, n l = (N, N) ∧
    z l = (((sysZ K x 0).X i ^ N * (sysZ K x 0).Y i ^ N : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) * (b ⊗ₜ 1 - 1 ⊗ₜ b)} = rB ℂ K (xv x) {i}

def IsDiag (τ : DR ℂ K →ₗ[K] K) (a : ℕ) (c : Finset (Two d ⊕ₗ Mi d) → DR ℂ K ⊗[ℂ] DR ℂ K) : Prop :=
  ∀ i j L, L.card = d → Acts (F := F) K τ a (c (uni (uni {i} {j}) L)) ((-1) ^ d * kap K x L)

abbrev pr (τ : DR ℂ K →ₗ[K] K) (ρ : F →ₗ[ℂ] ℂ) : (Finset (Fin (d + 1)) → DR ℂ K) →ₗ[ℂ] (Finset (Fin (d + 1)) → DR ℂ K) →ₗ[ℂ] ℂ :=
  cupPair ((LinearMap.mul ℂ (DR ℂ K)).compr₂ (trF ℂ τ ρ))

end

def GoodZ : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ a : ℕ, (sysZ K x a).Good ∧ (sysP K x a).Good ∧
  ∀ s t : Finset (Fin (d + 1)), s.Nonempty → s ⊆ t → omB ℂ K (rB ℂ K (xv x) s) a ≤ omB ℂ K (rB ℂ K (xv x) t) a

def LatOm : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (a : ℕ) (I : Finset (Fin (d + 1))), I.Nonempty →
  Lat (rA ℂ (xv x) I) (omB ℂ K (rB ℂ K (xv x) I) a) ∧
  ∀ w ∈ ⋀[K]^a Ω[K⁄ℂ], w ∈ Submodule.span F (omB ℂ K (rB ℂ K (xv x) I) a : Set (DR ℂ K))

def LatA : Prop := ∀ (F : Type) [Field F] [Algebra ℂ F] (d : ℕ) (x : Fin (d + 1) → Fˣ), IsPd ℂ (xv x) → ∀ (I : Finset (Fin (d + 1))), ∀ i ∈ I, Lat (rA ℂ (xv x) I) (omA ℂ (xv x) I) ∧
  (∀ y : F, y ∈ omA ℂ (xv x) I ↔ y / omG x i ∈ rA ℂ (xv x) I) ∧
  ∀ j, ∀ y ∈ omA ℂ (xv x) (insert j I), ∃ N : ℕ, ((x j : F) / x i) ^ N * y ∈ omA ℂ (xv x) I

def Reg0 : Prop := ∀ (F : Type) [Field F] [Algebra ℂ F] (d : ℕ) (x : Fin (d + 1) → Fˣ), IsPd ℂ (xv x) → ∀ (I J : Finset (Fin (d + 1))), ∀ j ∈ I, j ∈ J →
  Reg (Algebra.lmul ℂ (F ⊗[ℂ] F)) (Subalgebra.toSubmodule (R0 x I J)) (f0 x j)

def Ker0 : Prop := ∀ (F : Type) [Field F] [Algebra ℂ F] (d : ℕ) (x : Fin (d + 1) → Fˣ), IsPd ℂ (xv x) → ∀ (I J : Finset (Fin (d + 1))), ∀ j ∈ I, j ∈ J → ∀ m ∈ R0 x I J,
  Algebra.TensorProduct.lmul' ℂ m = 0 →
  m ∈ sm (Algebra.lmul ℂ (F ⊗[ℂ] F)) (Subalgebra.toSubmodule (R0 x I J)) (Set.range (f0 x j))

def RegLat : Prop := ∀ (F : Type) [Field F] [Algebra ℂ F] (d : ℕ) (x : Fin (d + 1) → Fˣ), IsPd ℂ (xv x) → ∀ (V V' : Type) [AddCommGroup V] [Module F V] [Module ℂ V] [IsScalarTower ℂ F V]
  [AddCommGroup V'] [Module F V'] [Module ℂ V'] [IsScalarTower ℂ F V'] (I J : Finset (Fin (d + 1))) (M : Submodule ℂ V)
  (M' : Submodule ℂ V'), Lat (rA ℂ (xv x) I) M → Lat (rA ℂ (xv x) J) M' → ∀ j ∈ I, j ∈ J →
  Reg (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') (f0 x j) ∧
  ∀ m ∈ Submodule.map₂ (TensorProduct.mk ℂ _ _) M M', (∀ ψ : V →ₗ[F] F, ctrF V' ψ m = 0) →
    m ∈ sm (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') (Set.range (f0 x j))

def DualForm : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a, a ≤ d → ∀ ψ : DR ℂ K →ₗ[F] F,
  (∃ w ∈ ⋀[K]^a Ω[K⁄ℂ], ∀ y ∈ ⋀[K]^(d - a) Ω[K⁄ℂ], ψ y = Algebra.trace F K (τ (y * w))) ∧
  ∃ w ∈ ⋀[K]^(d - a) Ω[K⁄ℂ], ∀ y ∈ ⋀[K]^a Ω[K⁄ℂ], ψ y = Algebra.trace F K (τ (w * y))

def ColZ : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a, a ≤ d → ∀ I J, ∀ i ∈ I, ∀ j ∈ J,
  KE (kos (sysZ K x a).act ((sysZ K x a).M I J) fun l => (sysZ K x a).r n11 (sysZ K x a).mu i j (dj j l)) d ∧
  ∀ m ∈ (sysZ K x a).M I J, Acts (F := F) K τ a m 0 →
    m ∈ sm (sysZ K x a).act ((sysZ K x a).M I J) (Set.range fun l => (sysZ K x a).r n11 (sysZ K x a).mu i j (dj j l))

def ColP : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ a I J, ∀ i ∈ I, ∀ j ∈ J,
  KE (kos (sysP K x a).act ((sysP K x a).M I J) fun l => (sysP K x a).r n11 (sysP K x a).mu i j (dj j l)) d ∧
  ∀ m ∈ (sysP K x a).M I J, mulP F K m = 0 →
    m ∈ sm (sysP K x a).act ((sysP K x a).M I J) (Set.range fun l => (sysP K x a).r n11 (sysP K x a).mu i j (dj j l))

def ActsLin : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a : ℕ,
  (∀ m m' c c', Acts (F := F) K τ a m c → Acts (F := F) K τ a m' c' →
    Acts (F := F) K τ a (m + m') (c + c') ∧ Acts (F := F) K τ a (m - m') (c - c')) ∧
  (∀ m c s, Acts (F := F) K τ a m c → Acts (F := F) K τ a (actZ K s m) (Algebra.TensorProduct.lmul' ℂ s * c)) ∧
  (∀ i j M m, m ∈ sm (actZ K) M (Set.range ((sysZ K x a).r n11 (sysZ K x a).mu i j)) → Acts (F := F) K τ a m 0) ∧
  (∀ (u : (K ⊗[ℂ] K)ˣ) M m i j, m ∈ sm (actZ K) M (Set.range ((sysZ K x a).r n11 (sysZ K x a).mu i j)) →
    Acts (F := F) K τ a (actZ K u m) 0) ∧
  (∀ (s : F ⊗[ℂ] K) m, mulP F K ((sysP K x a).act s m) =
    Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom ℂ F K) (AlgHom.id ℂ K) s • mulP F K m) ∧
  ∀ (s : F ⊗[ℂ] K) m w, muP F K τ (actZ K (Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℂ F K) (AlgHom.id ℂ K) s) m) w =
    (sysP K x a).act s (muP F K τ m w)

def IdJ : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a, a ≤ d → ∀ j, ∃ m ∈ (sysZ K x a).M {j} {j}, Acts (F := F) K τ a m (algebraMap F K (omG x j))

def IdIJ : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a, a ≤ d → ∀ i j, ∃ m ∈ (sysZ K x a).M {i} {j}, Acts (F := F) K τ a m (algebraMap F K (omG x i))

def ZFam : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∃ (m : ℕ) (n : Fin m → ℕ × ℕ) (z : Fin m → K ⊗[ℂ] K), ZF K x n z

def KapInd : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (S E : Type) [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)
  (π : S →ₐ[ℂ] K), (∀ i, π (T.X i) = algebraMap F K (x i)) → (∀ i, π (T.Y i) = algebraMap F K (x i)) →
  ∀ i L, L.card = d → π (detC T.rowMu (uni {i} L)) = kap K x L

def ZCol : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a, a ≤ d → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → K ⊗[ℂ] K), ZF K x n z →
  ∀ i j, ∃ c ∈ ((sysZ K x a).colCx (app n11 n) (app (sysZ K x a).mu z) {i} {j}).Z d,
    ∀ L : Finset (Mi d), L.card = d → Acts (F := F) K τ a (c (uni L ∅)) ((-1) ^ d * kap K x L)

def ZEx : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a, a ≤ d → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → K ⊗[ℂ] K), ZF K x n z →
  ∃ c ∈ ((sysZ K x a).cx (app n11 n) (app (sysZ K x a).mu z)).Z (d + 2), IsDiag K x τ a (resK inlE c)

def PLift : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ a I J, I.Nonempty → J.Nonempty → ∀ w ∈ omB ℂ K (rB ℂ K (xv x) (I ∪ J)) a,
  ∃ y ∈ ((sysP K x a).colCx n11 (sysP K x a).mu I J).Z d, ∀ L, L.card = d → mulP F K (y L) = kap K x L • w

def PCmp : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (a p : ℕ), ∀ c ∈ ((sysP K x a).cx n11 (sysP K x a).mu).Z (d + p + 2),
  (∀ b L, d < L.card → c (uni b L) = 0) →
  ∀ γ ∈ (acx (mixF fun I J : Finset (Fin (d + 1)) => omB ℂ K (rB ℂ K (xv x) (I ∪ J)) a) fun _ => 1).B (p + 2),
  (∀ b L, L.card = d → mulP F K (c (uni b L)) = kap K x L • γ b) → c ∈ ((sysP K x a).cx n11 (sysP K x a).mu).B (d + p + 2)

def PTheta : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (a p : ℕ), ∀ β ∈ (omCx (rB ℂ K (xv x)) a).Z p,
  ∃ c ∈ ((sysP K x a).cx n11 (sysP K x a).mu).Z (d + p + 2), (∀ b L, d < L.card → c (uni b L) = 0) ∧
    (∀ b L, L.card = d → mulP F K (c (uni b L)) = kap K x L • ((-1 : ℤ) ^ ((p + 1) * d)) • edge2 β b) ∧
    ∀ J, c (uni (uni Finset.univ J) ∅) = 1 ⊗ₜ β J

def PCup : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ (a p : ℕ), a ≤ d → ∀ c ∈ ((sysZ K x a).cx n11 (sysZ K x a).mu).Z (d + 2), IsDiag K x τ a c →
  ∀ α ∈ (omCx (rB ℂ K (xv x)) a).Z p,
  rcup (muP F K τ) p c α ∈ ((sysP K x a).cx n11 (sysP K x a).mu).Z (d + p + 2) ∧
    (∀ b L, d < L.card → rcup (muP F K τ) p c α (uni b L) = 0) ∧
    ∀ b L, L.card = d → mulP F K (rcup (muP F K τ) p c α (uni b L)) = kap K x L • ((-1 : ℤ) ^ (p * (d + 1) + d)) • edge1 α b

def PInt : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ (ρ : F →ₗ[ℂ] ℂ), IsRes ℂ (xv x) ρ → ∀ (a p : ℕ), ∀ t ∈ (sysP K x a).mix.B (d + p + 2),
  (fun J => resP (DR ℂ K) ρ (t (uni Finset.univ J))) ∈ (omCx (rB ℂ K (xv x)) a).B p

def RCupTop : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ (ρ : F →ₗ[ℂ] ℂ), IsRes ℂ (xv x) ρ → ∀ (a p : ℕ), a ≤ d → ∀ t ∈ (sysZ K x a).mix.B (d + 2), ∀ α ∈ (omCx (rB ℂ K (xv x)) a).Z p,
  (fun J => resP (DR ℂ K) ρ (∑ i, muP F K τ (t (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·))))) ∈
    (omCx (rB ℂ K (xv x)) a).B p

def ZAct : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ (ρ : F →ₗ[ℂ] ℂ), IsRes ℂ (xv x) ρ → ∀ (a p : ℕ), a ≤ d → ∀ c ∈ ((sysZ K x a).cx n11 (sysZ K x a).mu).Z (d + 2), IsDiag K x τ a c →
  ∀ α ∈ (omCx (rB ℂ K (xv x)) a).Z p,
  α - (fun J => resP (DR ℂ K) ρ (∑ i, muP F K τ (top c (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·))))) ∈
    (omCx (rB ℂ K (xv x)) a).B p

def ZId : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ (ρ : F →ₗ[ℂ] ℂ), IsRes ℂ (xv x) ρ → ∀ a : ℕ, a ≤ d → ∀ c ∈ ((sysZ K x a).cx n11 (sysZ K x a).mu).Z (d + 2), IsDiag K x τ a c →
  ∃ (m : ℕ) (p : Fin m → ℕ) (e f : Fin m → Finset (Fin (d + 1)) → DR ℂ K),
    (∀ k, p k ≤ d ∧ e k ∈ (omCx (rB ℂ K (xv x)) (d - a)).Z (d - p k) ∧ f k ∈ (omCx (rB ℂ K (xv x)) a).Z (p k)) ∧
    top c - ∑ k, join (TensorProduct.mk ℂ _ _) (e k) (f k) ∈ (sysZ K x a).mix.B (d + 2) ∧
    ∀ q : ℕ, ∀ α ∈ (omCx (rB ℂ K (xv x)) a).Z q,
      α - ∑ k ∈ Finset.univ.filter (fun k => p k = q), pr K τ ρ (e k) α • f k ∈ (omCx (rB ℂ K (xv x)) a).B q

def PrB : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ (ρ : F →ₗ[ℂ] ℂ), IsRes ℂ (xv x) ρ → ∀ (a q : ℕ), a ≤ d → q ≤ d → ∀ e ∈ (omCx (rB ℂ K (xv x)) (d - a)).Z (d - q),
  ∀ y ∈ (omCx (rB ℂ K (xv x)) a).B q, pr K τ ρ e y = 0

end UpperTheory.Gal.productCup_of_system

end
