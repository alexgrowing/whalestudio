import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

noncomputable section

open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS.Laurent

variable {F : Type} [Field F] {s : ℕ}

def chi (t : Fin s → Fˣ) : Multiplicative (Fin s → ℤ) →* F where
  toFun a := ((∏ j, t j ^ (Multiplicative.toAdd a) j : Fˣ) : F)
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, Pi.add_apply, _root_.zpow_add, Finset.prod_mul_distrib, Units.val_mul]

def ev (t : Fin s → Fˣ) : AddMonoidAlgebra F (Fin s → ℤ) →ₐ[F] F :=
  AddMonoidAlgebra.lift F F (Fin s → ℤ) (chi t)

theorem ev_single (t : Fin s → Fˣ) (a : Fin s → ℤ) (c : F) :
    ev t (AddMonoidAlgebra.single a c) = c * ((∏ j, t j ^ a j : Fˣ) : F) := by
  rw [ev, AddMonoidAlgebra.lift_single]; rfl

def univ (F : Type) [Field F] (s : ℕ) (j : Fin s) : (AddMonoidAlgebra F (Fin s → ℤ))ˣ where
  val := AddMonoidAlgebra.single (Pi.single j 1) 1
  inv := AddMonoidAlgebra.single (-Pi.single j 1) 1
  val_inv := by rw [AddMonoidAlgebra.single_mul_single]; simp [AddMonoidAlgebra.one_def]
  inv_val := by rw [AddMonoidAlgebra.single_mul_single]; simp [AddMonoidAlgebra.one_def]

theorem map_univ (t : Fin s → Fˣ) (j : Fin s) :
    Units.map (ev t : AddMonoidAlgebra F (Fin s → ℤ) →* F) (univ F s j) = t j := by
  refine Units.ext ?_
  change ev t (AddMonoidAlgebra.single (Pi.single j 1) 1) = _
  rw [ev_single, one_mul, Finset.prod_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem exists_coeff {E : Type} [CommRing E] [Algebra F E]
    (x : E ⊗[F] AddMonoidAlgebra F (Fin s → ℤ)) :
    ∃ c : (Fin s → ℤ) →₀ E ⊗[F] F, ∀ t : Fin s → Fˣ,
      Algebra.TensorProduct.map (AlgHom.id F E) (ev t) x =
        c.sum fun a y => ((∏ j, t j ^ a j : Fˣ) : F) • y := by
  have hadd : ∀ x y : E ⊗[F] AddMonoidAlgebra F (Fin s → ℤ),
      (∃ c : (Fin s → ℤ) →₀ E ⊗[F] F, ∀ t : Fin s → Fˣ,
        Algebra.TensorProduct.map (AlgHom.id F E) (ev t) x =
          c.sum fun a y => ((∏ j, t j ^ a j : Fˣ) : F) • y) →
      (∃ c : (Fin s → ℤ) →₀ E ⊗[F] F, ∀ t : Fin s → Fˣ,
        Algebra.TensorProduct.map (AlgHom.id F E) (ev t) y =
          c.sum fun a y => ((∏ j, t j ^ a j : Fˣ) : F) • y) →
      (∃ c : (Fin s → ℤ) →₀ E ⊗[F] F, ∀ t : Fin s → Fˣ,
        Algebra.TensorProduct.map (AlgHom.id F E) (ev t) (x + y) =
          c.sum fun a y => ((∏ j, t j ^ a j : Fˣ) : F) • y) := by
    rintro x y ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c + d, fun t => ?_⟩
    rw [map_add, hc, hd, Finsupp.sum_add_index' (by simp) (by simp [smul_add])]
  induction x with
  | zero => exact ⟨0, fun t => by simp⟩
  | add x y hx hy => exact hadd x y hx hy
  | tmul e p =>
    induction p using AddMonoidAlgebra.induction_linear with
    | zero => exact ⟨0, fun t => by simp⟩
    | add p q hp hq => rw [TensorProduct.tmul_add]; exact hadd _ _ hp hq
    | single a c =>
      refine ⟨Finsupp.single a (e ⊗ₜ c), fun t => ?_⟩
      rw [Finsupp.sum_single_index (by simp), Algebra.TensorProduct.map_tmul, ev_single,
        AlgHom.id_apply, mul_comm, ← smul_eq_mul, TensorProduct.tmul_smul]

end GlobalTheory.RegSS.Laurent

namespace GlobalTheory.RegSS

open Laurent

theorem subtorusLaurent : SubtorusLaurent := by
  intro F E _ _ _ n _ _ σ J γ s A
  classical
  choose c hc using fun i j : n => exists_coeff (F := F) (s := s)
    ((A.hom _ (univ F s) : Matrix n n (E ⊗[F] AddMonoidAlgebra F (Fin s → ℤ))) i j)
  refine ⟨Finset.univ.biUnion fun p : n × n => (c p.1 p.2).support,
    fun a => Matrix.of fun i j => c i j a, fun t => ?_⟩
  have h := A.natural _ F (ev t) (univ F s)
  simp only [map_univ] at h
  ext i j
  have h2 : (A.hom F t : Matrix n n (E ⊗[F] F)) i j =
      Algebra.TensorProduct.map (AlgHom.id F E) (ev t)
        ((A.hom _ (univ F s) : Matrix n n (E ⊗[F] AddMonoidAlgebra F (Fin s → ℤ))) i j) := by
    rw [h]; rfl
  rw [h2, hc, Matrix.sum_apply, Finsupp.sum_of_support_subset _
    (Finset.subset_biUnion_of_mem (fun p : n × n => (c p.1 p.2).support) (Finset.mem_univ (i, j)))
    _ (by simp)]
  rfl

end GlobalTheory.RegSS
