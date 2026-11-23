import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent

open Matrix

namespace GlobalTheory.Core.Rk.Exh

theorem exists_orthonormal_of_isLocalRing (O : Type) [CommRing O] [IsLocalRing O] (s : O →+* O)
    (hs : ∀ x, s (s x) = x) (hτ : ∃ τ : O, τ + s τ = 1)
    (hn : ∀ u : O, IsUnit u → s u = u → ∃ x : O, s x * x = u)
    (n : ℕ) (Q : Matrix (Fin n) (Fin n) O) (hQ : Formalism.UG.cT s Q = Q) (hu : IsUnit Q) :
    ∃ a : GL (Fin n) O, Formalism.UG.cT s a.1 * Q * a.1 = 1 := by
  obtain ⟨P, hP, h⟩ := UnramifiedHermitian.exists_eq_transpose_mul_map_of_isUnit_or s hs
    (fun x _ => IsLocalRing.isUnit_or_isUnit_one_sub_self x) hτ
    (fun u h1 h2 => (hn u h2 h1).imp fun x hx => by rw [mul_comm, hx])
    (G := Q) (fun a b => congrFun (congrFun hQ b) a) ((Matrix.isUnit_iff_isUnit_det Q).1 hu)
  obtain ⟨R, hR, h'⟩ := UnramifiedHermitian.exists_congr_symm s (G := 1) (H := Q) hP
    (by rw [Matrix.mul_one, h])
  have hR' : IsUnit (R.map s) := by
    rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hR.map s
  refine ⟨hR'.unit, ?_⟩
  rw [IsUnit.unit_spec, h']
  congr 2
  ext i j
  exact hs _

end GlobalTheory.Core.Rk.Exh
