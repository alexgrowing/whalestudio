import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

noncomputable section

open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS.MatBd

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

theorem assoc_sigR (P : Type) [CommRing P] [Algebra F P] (σ : E →ₐ[F] E) (R : Type) [CommRing R]
    [Algebra F R] (x : (P ⊗[F] E) ⊗[F] R) :
    Algebra.TensorProduct.assoc F F F P E R (sigR (tConj P σ) R x) =
      tConj3 P σ R (Algebra.TensorProduct.assoc F F F P E R x) := by
  induction x with
  | zero => simp
  | tmul a r =>
    induction a with
    | zero => simp
    | tmul p e => simp [sigR, tConj, tConj3]
    | add a b ha hb => rw [TensorProduct.add_tmul, map_add, map_add, map_add, map_add, ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]

def entry (σ : E →ₐ[F] E) (J γ : Matrix n n E) (i j : n) : plusAlg σ J γ ⊗[F] E →ₗ[F] E where
  toFun x := (plusTensor σ J γ x : Matrix n n E) i j
  map_add' a b := by rw [map_add]; rfl
  map_smul' c a := by rw [map_smul]; rfl

theorem toMat_assoc_apply (σ : E →ₐ[F] E) (J γ : Matrix n n E) (R : Type) [CommRing R]
    [Algebra F R] (x : (plusAlg σ J γ ⊗[F] E) ⊗[F] R) (i j : n) :
    toMat σ J γ R (Algebra.TensorProduct.assoc F F F (plusAlg σ J γ) E R x) i j =
      LinearMap.rTensor R (entry σ J γ i j) x := by
  induction x with
  | zero => simp
  | tmul a r =>
    induction a with
    | zero => simp
    | tmul p e =>
      have h : (plusTensor σ J γ (p ⊗ₜ e) : Matrix n n E) =
          e • ((p : genAlg γ) : Matrix n n E) := by
        rw [plusTensor, Algebra.TensorProduct.productMap_apply_tmul, mul_comm]
        exact (Algebra.smul_def e ((p : genAlg γ) : Matrix n n E)).symm
      rw [Algebra.TensorProduct.assoc_tmul, LinearMap.rTensor_tmul]
      change (((p : genAlg γ) : Matrix n n E).map (inclE (F := F) R) *
        algebraMap (E ⊗[F] R) (Matrix n n (E ⊗[F] R)) (e ⊗ₜ r)) i j =
        ((plusTensor σ J γ (p ⊗ₜ e) : Matrix n n E) i j) ⊗ₜ r
      rw [h, ← Algebra.commutes, ← Algebra.smul_def]
      simp [inclE]
    | add a b ha hb =>
      rw [TensorProduct.add_tmul, map_add, map_add, map_add, Matrix.add_apply, ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, Matrix.add_apply, ha, hb]

theorem toMat_assoc_inclE (σ : E →ₐ[F] E) (J γ : Matrix n n E) (R : Type) [CommRing R]
    [Algebra F R] (β : plusAlg σ J γ ⊗[F] E) :
    toMat σ J γ R (Algebra.TensorProduct.assoc F F F (plusAlg σ J γ) E R (inclE (F := F) R β)) =
      (plusTensor σ J γ β : Matrix n n E).map (inclE (F := F) R) := by
  ext i j
  rw [toMat_assoc_apply]
  rfl

theorem exists_centRat {σ : E →ₐ[F] E} {J : Matrix n n E} {γ : GL n E} (h : IsRegular σ J γ)
    (β : plusAlg σ J (γ : Matrix n n E) ⊗[F] E) (hβ : β * tConj _ σ β = 1) :
    ∃ δ ∈ centRat σ J γ, (δ : Matrix n n E) = plusTensor σ J (γ : Matrix n n E) β := by
  have h1 : (plusTensor σ J (γ : Matrix n n E) β : Matrix n n E) *
      adj (σ : E →+* E) J (plusTensor σ J (γ : Matrix n n E) β : Matrix n n E) = 1 := by
    rw [← plusTensor_tConj h, ← Subalgebra.coe_mul, ← map_mul, hβ, map_one]
    rfl
  refine ⟨⟨_, _, h1, mul_eq_one_comm.1 h1⟩, ⟨(mem_UJ_iff_mul_adj _ h.nondeg _).2 h1, ?_⟩, rfl⟩
  refine Subgroup.mem_centralizer_singleton_iff.2 (Units.ext ?_)
  exact (commute_of_mem_genAlg rfl (plusTensor σ J (γ : Matrix n n E) β).2).symm

theorem matOfNormBounded : MatOfNormBounded := by
  intro F E _ _ _ _ n _ _ σ J γ h _ _ hP hN
  obtain ⟨D, hD, hu⟩ := hN
  letI : TopologicalSpace (E ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := E) (AdeleRing (𝓞 F) F)
  letI : TopologicalSpace ((plusAlg σ J (γ : Matrix n n E) ⊗[F] E) ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := plusAlg σ J (γ : Matrix n n E) ⊗[F] E) (AdeleRing (𝓞 F) F)
  let a := Algebra.TensorProduct.assoc F F F (plusAlg σ J (γ : Matrix n n E)) E (AdeleRing (𝓞 F) F)
  have hc : Continuous fun x => toMat σ J (γ : Matrix n n E) (AdeleRing (𝓞 F) F) (a x) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [a, toMat_assoc_apply]
    exact continuous_rTensor _ _
  refine ⟨_, hD.image hc, fun g hg => ?_⟩
  obtain ⟨u, hu1, hug⟩ := ((hP (AdeleRing (𝓞 F) F)).2.2 g).1 hg
  obtain ⟨x, hx⟩ := a.surjective u
  obtain ⟨β, hβ, hxβ⟩ := hu x (a.injective (by
    rw [map_mul, map_one, assoc_sigR]
    change a x * tConj3 _ σ _ (a x) = 1
    rw [hx]
    exact hu1))
  obtain ⟨δ, hδ, hδβ⟩ := exists_centRat h β hβ
  refine ⟨δ, hδ, _, hxβ, ?_⟩
  beta_reduce
  rw [map_mul, map_mul, hx, hug, toMat_assoc_inclE, hδβ]

end GlobalTheory.RegSS.MatBd
