import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeZeroTorus
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes GlobalTheory.EisRestrict
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.AdelicInfGlue

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def adeleProdEquiv : AF F ≃ₐ[F] Ainf F × Af F :=
  AlgEquiv.ofAlgHom ((fstA F).prod (sndA F))
    { toFun := fun p => (p.1, p.2)
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
    (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)

open Classical in

def splitEquiv : AF F ⊗[F] E ≃ₐ[F] (∀ w : InfinitePlace F, w.Completion ⊗[F] E) × (Af F ⊗[F] E) :=
  (Algebra.TensorProduct.comm F (AF F) E).trans <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := F) (A₁ := E)) (adeleProdEquiv F)).trans <|
    (Algebra.TensorProduct.prodRight F F E (Ainf F) (Af F)).trans <|
      AlgEquiv.prodCongr
        ((Algebra.TensorProduct.piRight F F E (fun w : InfinitePlace F => w.Completion)).trans
          (AlgEquiv.piCongrRight fun w => Algebra.TensorProduct.comm F E w.Completion))
        (Algebra.TensorProduct.comm F E (Af F))

theorem splitEquiv_fst (w : InfinitePlace F) (z : AF F ⊗[F] E) :
    (splitEquiv F E z).1 w = compInf F E w z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, Prod.fst_add, Pi.add_apply, hx, hy, map_add]
  | tmul a e =>
    simp only [splitEquiv, AlgEquiv.trans_apply, Algebra.TensorProduct.comm_tmul,
      Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, AlgEquiv.refl_toAlgHom,
      Algebra.TensorProduct.prodRight_tmul, AlgEquiv.prodCongr_apply, Prod.map_fst,
      Algebra.TensorProduct.piRight_tmul, AlgEquiv.piCongrRight_apply]
    rfl

def pairMat {R S : Type} {m : ℕ} (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin m) (Fin m) S) :
    Matrix (Fin m) (Fin m) (R × S) := Matrix.of fun i j => (A i j, B i j)

theorem pairMat_mul {R S : Type} [Semiring R] [Semiring S] {m : ℕ} (A A' : Matrix (Fin m) (Fin m) R)
    (B B' : Matrix (Fin m) (Fin m) S) : pairMat A B * pairMat A' B' = pairMat (A * A') (B * B') := by
  ext i j
  · simp [pairMat, Matrix.mul_apply, Prod.fst_sum]
  · simp [pairMat, Matrix.mul_apply, Prod.snd_sum]

theorem pairMat_one {R S : Type} [Semiring R] [Semiring S] {m : ℕ} :
    pairMat (1 : Matrix (Fin m) (Fin m) R) (1 : Matrix (Fin m) (Fin m) S) = 1 := by
  ext i j <;> by_cases h : i = j <;> simp [pairMat, Matrix.one_apply, h]

def piMat {ι : Type} {R : ι → Type} {m : ℕ} (A : ∀ w, Matrix (Fin m) (Fin m) (R w)) :
    Matrix (Fin m) (Fin m) (∀ w, R w) := Matrix.of fun i j w => A w i j

theorem piMat_mul {ι : Type} {R : ι → Type} [∀ w, Semiring (R w)] {m : ℕ}
    (A A' : ∀ w, Matrix (Fin m) (Fin m) (R w)) : piMat A * piMat A' = piMat fun w => A w * A' w := by
  ext i j w
  simp [piMat, Matrix.mul_apply, Finset.sum_apply]

theorem piMat_one {ι : Type} {R : ι → Type} [∀ w, Semiring (R w)] {m : ℕ} :
    piMat (fun w => (1 : Matrix (Fin m) (Fin m) (R w))) = 1 := by
  ext i j w
  by_cases h : i = j <;> simp [piMat, Matrix.one_apply, h]

def glueGL {ι : Type} {R : ι → Type} [∀ w, CommRing (R w)] {S : Type} [CommRing S] {m : ℕ}
    (g : ∀ w, GL (Fin m) (R w)) : GL (Fin m) ((∀ w, R w) × S) where
  val := pairMat (piMat fun w => (g w : Matrix (Fin m) (Fin m) (R w))) 1
  inv := pairMat (piMat fun w => (((g w)⁻¹ : GL (Fin m) (R w)) : Matrix (Fin m) (Fin m) (R w))) 1
  val_inv := by
    rw [pairMat_mul, piMat_mul, Matrix.one_mul]
    simp only [Units.mul_inv]
    rw [piMat_one, pairMat_one]
  inv_val := by
    rw [pairMat_mul, piMat_mul, Matrix.one_mul]
    simp only [Units.inv_mul]
    rw [piMat_one, pairMat_one]

theorem exists_gl_inf_components (m : ℕ) (g : ∀ w : InfinitePlace F, GL (Fin m) (w.Completion ⊗[F] E)) :
    ∃ a₀ : GL (Fin m) (AF F ⊗[F] E), ∀ w, Formalism.UG.bc (compInf F E w) a₀ = g w := by
  refine ⟨Formalism.UG.bc (splitEquiv F E).symm.toRingEquiv.toRingHom (glueGL (S := Af F ⊗[F] E) g), fun w => ?_⟩
  refine Units.ext (Matrix.ext fun i j => ?_)
  change compInf F E w ((splitEquiv F E).symm _) = _
  rw [← splitEquiv_fst, AlgEquiv.apply_symm_apply]
  rfl

end GlobalTheory.AdelicInfGlue

theorem GlobalTheory.adelic_gl_prescribed_infinite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (m : ℕ)
    (g : ∀ w : InfinitePlace F, GL (Fin m) (w.Completion ⊗[F] E)),
    ∃ a₀ : GL (Fin m) (AF F ⊗[F] E), ∀ w, Formalism.UG.bc (compInf F E w) a₀ = g w :=
  fun F E _ _ _ _ _ m g => GlobalTheory.AdelicInfGlue.exists_gl_inf_components F E m g
