import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

noncomputable section

open Matrix GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.PolyTensor

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ)
  (γ : Matrix (Fin n) (Fin n) K)

def polySub : Subalgebra ℚ_[p] (Matrix (Fin n) (Fin n) K) := (Algebra.adjoin K {γ}).restrictScalars ℚ_[p]

theorem mem_polySub {x : Matrix (Fin n) (Fin n) K} : x ∈ polySub p K n γ ↔ x ∈ Algebra.adjoin K {γ} :=
  Iff.rfl

theorem polySub_comm (a b : polySub p K n γ) : a * b = b * a :=
  Subtype.ext (Algebra.commute_of_mem_adjoin_of_forall_mem_commute (mem_polySub p K n γ |>.1 b.2)
    (fun y hy => by
      rw [Set.mem_singleton_iff.1 hy]
      exact (Algebra.commute_of_mem_adjoin_singleton_of_commute (mem_polySub p K n γ |>.1 a.2)
        (Commute.refl γ)).symm)).eq

def PolyAlg : Type := polySub p K n γ

instance : CommRing (PolyAlg p K n γ) :=
  { (polySub p K n γ).toRing with mul_comm := polySub_comm p K n γ }

instance : Algebra ℚ_[p] (PolyAlg p K n γ) := inferInstanceAs (Algebra ℚ_[p] (polySub p K n γ))

instance [FiniteDimensional ℚ_[p] K] : Module.Finite ℚ_[p] (PolyAlg p K n γ) :=
  inferInstanceAs (Module.Finite ℚ_[p] (polySub p K n γ))

def val : PolyAlg p K n γ →ₐ[ℚ_[p]] Matrix (Fin n) (Fin n) K := (polySub p K n γ).val

variable (r : ℕ)

def phi : PolyAlg p K n γ ⊗[ℚ_[p]] Qr p r →ₐ[ℚ_[p]] Matrix (Fin n) (Fin n) (KQ p K r) :=
  Algebra.TensorProduct.lift (((inclK p K r).mapMatrix).comp (val p K n γ))
    (((Algebra.ofId (KQ p K r) (Matrix (Fin n) (Fin n) (KQ p K r))).restrictScalars ℚ_[p]).comp (inclQ p K r))
    (fun x y => (Algebra.commutes (inclQ p K r y) (((inclK p K r).mapMatrix.comp (val p K n γ)) x)).symm)

theorem phi_tmul (b : PolyAlg p K n γ) (q : Qr p r) :
    phi p K n γ r (b ⊗ₜ q) = (val p K n γ b).map (inclK p K r) * algebraMap (KQ p K r) _ (inclQ p K r q) := by
  unfold phi
  exact Algebra.TensorProduct.lift_tmul _ _ _ b q

def tw : PolyAlg p K n γ ⊗[ℚ_[p]] Qr p r →ₐ[ℚ_[p]] PolyAlg p K n γ ⊗[ℚ_[p]] Qr p r :=
  Algebra.TensorProduct.map (AlgHom.id ℚ_[p] _) (frobQ p r)

theorem phi_tw (x : PolyAlg p K n γ ⊗[ℚ_[p]] Qr p r) :
    phi p K n γ r (tw p K n γ r x) = (phi p K n γ r x).map (sigKQ p K r) := by
  change ((phi p K n γ r).comp (tw p K n γ r)) x = ((sigKQ p K r).mapMatrix.comp (phi p K n γ r)) x
  congr 1
  refine Algebra.TensorProduct.ext' fun b q => ?_
  simp only [AlgHom.comp_apply, tw, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, phi_tmul, map_mul,
    AlgHom.mapMatrix_apply]
  congr 1
  · ext i j
    simp only [Matrix.map_apply]
    exact (sigKQ_apply_inclK p K r _).symm
  · ext i j
    simp only [Matrix.map_apply, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp [sigKQ_apply_inclQ]

theorem phi_commute (y : Matrix (Fin n) (Fin n) K) (hy : Commute y γ) (x : PolyAlg p K n γ ⊗[ℚ_[p]] Qr p r) :
    Commute (y.map (inclK p K r)) (phi p K n γ r x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Commute.zero_right _
  | tmul b q =>
    rw [phi_tmul]
    refine Commute.mul_right ?_ (Algebra.commutes _ _).symm
    have h : Commute y (val p K n γ b) :=
      Algebra.commute_of_mem_adjoin_singleton_of_commute ((mem_polySub p K n γ).1 b.2) hy
    exact h.map (inclK p K r).mapMatrix
  | add a b ha hb => rw [map_add]; exact ha.add_right hb

end GlobalTheory.PolyTensor
