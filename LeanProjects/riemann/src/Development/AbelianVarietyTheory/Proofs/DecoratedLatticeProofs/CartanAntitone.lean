import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationDivZpowOrd
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.SortedCartan

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def permUnitO {N : ℕ} (σ : Equiv.Perm (Fin N)) : GL (Fin N) 𝒪[k] where
  val := σ.toPEquiv.toMatrix
  inv := σ.symm.toPEquiv.toMatrix
  val_inv := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
  inv_val := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]

def permUnit {N : ℕ} (σ : Equiv.Perm (Fin N)) : GL (Fin N) k :=
  Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) (permUnitO σ)

theorem permUnit_mem_KO {N : ℕ} (σ : Equiv.Perm (Fin N)) : (permUnit σ : GL (Fin N) k) ∈ KO k (Fin N) :=
  ⟨permUnitO σ, rfl⟩

theorem permUnit_val {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    ((permUnit σ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = σ.toPEquiv.toMatrix := by
  ext i j
  simp only [permUnit, permUnitO, Matrix.GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply, PEquiv.toMatrix_apply]
  split_ifs <;> simp

theorem conj_torusElt {N : ℕ} (ϖ : kˣ) (m : Fin N → ℤ) (σ : Equiv.Perm (Fin N)) :
    permUnit σ * torusElt k (Fin N) ϖ m * (permUnit σ)⁻¹ = torusElt k (Fin N) ϖ (m ∘ σ) := by
  apply Units.ext
  have hinv : (((permUnit σ : GL (Fin N) k)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      σ.symm.toPEquiv.toMatrix := by
    show (σ.symm.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) 𝒪[k]).map (algebraMap 𝒪[k] k) = _
    exact PEquiv.map_toMatrix _ _
  rw [Units.val_mul, Units.val_mul, hinv, permUnit_val, torusElt, torusElt, val_diagT, val_diagT,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm,
    Matrix.submatrix_submatrix]
  exact Matrix.submatrix_diagonal_equiv _ σ

theorem torusElt_conj {N : ℕ} (ϖ : kˣ) (m : Fin N → ℤ) (σ : Equiv.Perm (Fin N)) :
    torusElt k (Fin N) ϖ m = (permUnit σ)⁻¹ * torusElt k (Fin N) ϖ (m ∘ σ) * permUnit σ := by
  rw [← conj_torusElt ϖ m σ]
  group

theorem cartan_antitone : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ x : GL (Fin N) k, ∃ ν : Fin N → ℤ, Antitone ν ∧ ∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N), x = κ * torusElt k (Fin N) ϖ ν * κ' := by
  intro k _ _ _ _ N ϖ hϖ g
  obtain ⟨x, hx, y, hy, m, rfl⟩ := GlobalTheory.LocalCartan.cartan_decomposition k (Fin N) ϖ g hϖ
  obtain ⟨σ, hmono⟩ : ∃ σ : Equiv.Perm (Fin N), Monotone ((fun i => -m i) ∘ σ) :=
    ⟨_, Tuple.monotone_sort _⟩
  refine ⟨m ∘ σ, fun a b hab => ?_, x * (permUnit σ)⁻¹, mul_mem hx (inv_mem (permUnit_mem_KO σ)),
    permUnit σ * y, mul_mem (permUnit_mem_KO σ) hy, ?_⟩
  · have := hmono hab
    simp only [Function.comp_apply] at this ⊢
    omega
  · have h := torusElt_conj ϖ m σ
    rw [torusElt] at h
    rw [h]
    group

end GlobalTheory.SortedCartan

end
