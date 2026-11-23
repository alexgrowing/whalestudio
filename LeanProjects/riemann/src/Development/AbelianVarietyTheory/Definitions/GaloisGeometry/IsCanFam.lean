import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MZmix
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TcoMem

set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.W1
open scoped TensorProduct

namespace GlobalTheory.WH

section Z

variable (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}
  (x : Fin (d + 1) → F)

def RZ (I J : Finset (Fin (d + 1))) : Subalgebra ℂ (K ⊗[ℂ] K) :=
  (Algebra.TensorProduct.map (rB ℂ K x I).val (rB ℂ K x J).val).range

def IsGen {κ : Type} [Fintype κ] (p1 p2 : κ → Fin (d + 1)) (z : κ → K ⊗[ℂ] K) : Prop :=
  (∀ l, z l ∈ RZ F K x {p1 l} {p2 l} ∧ Algebra.TensorProduct.lmul' ℂ (z l) = 0) ∧
    ∀ i j : Fin (d + 1), ∀ y ∈ RZ F K x {i} {j}, Algebra.TensorProduct.lmul' ℂ y = 0 →
      ∃ cf : κ → K ⊗[ℂ] K, (∀ l, cf l ∈ RZ F K x {i} {j}) ∧
        y = ∑ l ∈ Finset.univ.filter (fun l => p1 l = i ∧ p2 l = j), cf l * z l

def totZ {κ : Type} [LinearOrder κ] (p1 p2 : κ → Fin (d + 1)) (a : ℕ) (z : κ → K ⊗[ℂ] K) :
    GlobalTheory.PD.Cx ℂ (Finset ((Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ) → Finset (Fin (d + 1)) → DR ℂ K ⊗[ℂ] DR ℂ K) :=
  tcx (TZ F K x p1 p2 a) (wZ K z) (wd (XZ F K x))

def botZ {κ : Type} [LinearOrder κ] (m : Fin (d + 1) → Fin (d + 1) → DR ℂ K ⊗[ℂ] DR ℂ K) :
    Finset ((Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ) → Finset (Fin (d + 1)) → DR ℂ K ⊗[ℂ] DR ℂ K := fun s =>
  ∑ i, ∑ j, if s = uni (uni {i} {j}) ∅ then Pi.single Finset.univ ((XZ F K x i ^ d * YZ F K x j) (m i j)) else 0

def IsCanFam (τ : DR ℂ K →ₗ[K] K) (a : ℕ) (m : Fin (d + 1) → Fin (d + 1) → DR ℂ K ⊗[ℂ] DR ℂ K) : Prop :=
  ∀ i j, m i j ∈ MZ F K x a {i} {j} ∧
    ∀ w ∈ ⋀[K]^a Ω[K⁄ℂ], ctr F K τ w (m i j) = algebraMap F K ((∏ l, x l) / (x i ^ d * x j)) • w

end Z

section Y

variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K']
  {d : ℕ} (x : Fin (d + 1) → F)

def totY {κ : Type} [LinearOrder κ] (p1 p2 : κ → Fin (d + 1)) (j2 : K →ₐ[ℂ] K') (z : κ → K ⊗[ℂ] K) :
    GlobalTheory.PD.Cx ℂ (Finset ((Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ) → Finset (Fin (d + 1)) → DR ℂ K') :=
  tcx (TY x p1 p2 j2) (wY j2 z) (wd (XY x))

def pullY {κ : Type} (j2 : K →ₐ[ℂ] K')
    (c : Finset ((Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ) → Finset (Fin (d + 1)) → DR ℂ K ⊗[ℂ] DR ℂ K) :
    Finset ((Fin (d + 1) ⊕ₗ Fin (d + 1)) ⊕ₗ κ) → Finset (Fin (d + 1)) → DR ℂ K' := fun s U => gY j2 (c s U)

def LefData (j2 : K →ₐ[ℂ] K') (Fx : Finset (fib ℂ K' x)) (A : fib ℂ K' x → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ (i : Fin (d + 1)) (e : rB ℂ K' x {i} →ₐ[ℂ] ℂ), ∃ j : Fin (d + 1), ∀ v ∈ R2 x j2 {j},
      ∃ (b : K') (hb : b ∈ rB ℂ K' x {i}), e ⟨b, hb⟩ ≠ 0 ∧ b * v ∈ rB ℂ K' x {i}) ∧
  IsReduced ((rB ℂ K' x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ K' x j⟩ : rB ℂ K' x {0})))) ∧
  (∀ (i : Fin (d + 1)), i ≠ 0 → ∀ e : rB ℂ K' x {i} →ₐ[ℂ] ℂ, ¬ IsFix (rB ℂ K' x {i}) e j2 (rB ℂ K x {i})) ∧
  (∀ e : rB ℂ K' x {0} →ₐ[ℂ] ℂ, IsFix (rB ℂ K' x {0}) e j2 (rB ℂ K x {0}) → ∀ j : Fin d, e ⟨_, tco_mem ℂ K' x j⟩ = 0) ∧
  (∀ e : fib ℂ K' x, e ∈ Fx ↔ IsFix (rB ℂ K' x {0}) e.1 j2 (rB ℂ K x {0})) ∧
  (∀ e ∈ Fx, ∀ (b : K) (hb1 : algebraMap K K' b ∈ rB ℂ K' x {0}), b ∈ rB ℂ K x {0} → e.1 ⟨_, hb1⟩ = 0 →
    ∃ (c : K) (hc1 : algebraMap K K' c ∈ rB ℂ K' x {0}), c ∈ rB ℂ K x {0} ∧ e.1 ⟨_, hc1⟩ ≠ 0 ∧
      ∃ g : Fin d → K, (∀ l, g l ∈ rB ℂ K x {0}) ∧ c * b = ∑ l, g l * algebraMap F K (x l.succ / x 0)) ∧
  (∀ e ∈ Fx, ∀ m : Fin d, ∃ (c : K') (hc : c ∈ rB ℂ K' x {0}) (g : Fin d → K') (hg : ∀ l, g l ∈ rB ℂ K' x {0}),
    e.1 ⟨c, hc⟩ ≠ 0 ∧ c * j2 (algebraMap F K (x m.succ / x 0)) = ∑ l, g l * algebraMap F K' (x l.succ / x 0) ∧
      ∀ l, e.1 ⟨g l, hg l⟩ = e.1 ⟨c, hc⟩ * A e m l) ∧
  (∀ e ∈ Fx, (1 - A e).det ≠ 0)

end Y

end GlobalTheory.WH
