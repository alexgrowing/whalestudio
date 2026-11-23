import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H
open scoped BigOperators
open Classical

namespace GlobalTheory.BaseVacuum

def four : Fin 4 ≃ Fin 2 × Fin 2 := (finCongr (by norm_num)).trans finProdFinEquiv.symm

def posE (n n' : ℕ) : (Fin n' × Fin n) × Fin 4 ≃ Fin (n' * 2) × Fin (n * 2) :=
  ((Equiv.refl _).prodCongr four).trans
    ((Equiv.prodProdProdComm _ _ _ _).trans (finProdFinEquiv.prodCongr finProdFinEquiv))

abbrev Ix (D : D7) (n n' : ℕ) : Type := (Fin n' × Fin n) × (Fin 4 × D.what₂.Tau)

def blk (D : D7) {n n' : ℕ} (k : Fin n' × Fin n) (z : TaylorLogMetric.VC D (n * 2) (n' * 2)) : Fin 4 × D.what₂.Tau → ℂ :=
  fun w => z w.2 (posE n n' (k, w.1)).1 (posE n n' (k, w.1)).2

def reix (D : D7) (n n' : ℕ) : TaylorLogMetric.VC D (n * 2) (n' * 2) ≃ₗ[ℂ] (Ix D n n' → ℂ) where
  toFun z p := blk D p.1 z p.2
  invFun y τ i j := y (((posE n n').symm (i, j)).1, (((posE n n').symm (i, j)).2, τ))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv z := by
    funext τ i j
    simp [blk]
  right_inv y := by
    funext p
    simp [blk]

def gBig {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (n n' : ℕ) :
    (Ix D n n' → ℂ) ≃ₗ[ℂ] (Ix D n n' → ℂ) where
  toFun y p := B.gC (fun w => y (p.1, w)) p.2
  invFun y p := B.gC.symm (fun w => y (p.1, w)) p.2
  map_add' x y := by
    funext p
    show B.gC ((fun w => x (p.1, w)) + (fun w => y (p.1, w))) p.2 = _
    rw [map_add]; rfl
  map_smul' c x := by
    funext p
    show B.gC (c • (fun w => x (p.1, w))) p.2 = _
    rw [map_smul]; rfl
  left_inv y := by
    funext p
    simp
  right_inv y := by
    funext p
    simp

def phi {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (n n' : ℕ) :
    TaylorLogMetric.VC D (n * 2) (n' * 2) ≃ₗ[ℂ] (Ix D n n' → ℂ) :=
  (reix D n n').trans (gBig B n n')

theorem phi_apply {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (n n' : ℕ)
    (z : TaylorLogMetric.VC D (n * 2) (n' * 2)) (p : Ix D n n') : phi B n n' z p = B.gC (blk D p.1 z) p.2 := rfl

def ixE (D : D7) (n n' : ℕ) : Fin (TaylorLogMetric.fF D * (n * 2) * (n' * 2)) ≃ Ix D n n' :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin]
    simp only [Fintype.card_prod, Fintype.card_fin, D.what₂.card_Tau, TaylorLogMetric.fF]
    ring)

def xv {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (w : Fin 4 × D.what₂.Tau) : Fin 4 → D.host.E :=
  B.γ₀.g.symm (Pi.single w 1)

def putB (D : D7) {n n' : ℕ} (k : Fin n' × Fin n) (x : Fin 4 → D.host.E) :
    Matrix (Fin (n' * 2)) (Fin (n * 2)) D.host.E :=
  fun i j => if ((posE n n').symm (i, j)).1 = k then x ((posE n n').symm (i, j)).2 else 0

def bas {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (n n' : ℕ) :
    Fin (TaylorLogMetric.fF D * (n * 2) * (n' * 2)) → Matrix (Fin (n' * 2)) (Fin (n * 2)) D.host.E :=
  fun j => putB D (ixE D n n' j).1 (xv B (ixE D n n' j).2)

def blkLat {ι m : Type} (Λ : AddSubgroup (m → ℂ)) : AddSubgroup (ι × m → ℂ) where
  carrier := {y | ∀ k, (fun w => y (k, w)) ∈ Λ}
  zero_mem' := fun _ => Λ.zero_mem
  add_mem' := fun hx hy k => Λ.add_mem (hx k) (hy k)
  neg_mem' := fun hx k => Λ.neg_mem (hx k)

end GlobalTheory.BaseVacuum
