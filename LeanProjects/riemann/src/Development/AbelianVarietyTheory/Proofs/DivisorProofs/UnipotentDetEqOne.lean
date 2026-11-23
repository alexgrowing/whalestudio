import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCocompact.IsReducedInfiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EqZeroOfForallLTensorEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling

namespace GlobalTheory.ThKLiftCusp

theorem det_one_add_of_pow_eq_zero {R : Type} [CommRing R] [IsReduced R] {n : Type} [Fintype n] [DecidableEq n]
    (N : Matrix n n R) (k : ℕ) (hN : N ^ k = 0) : (1 + N).det = 1 := by
  have hM : IsNilpotent (-N) := (IsNilpotent.neg ⟨k, hN⟩)
  have h0 := Polynomial.isNilpotent_iff.1 (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hM)
  have h1 : (-N).charpoly = Polynomial.X ^ Fintype.card n := by
    ext i
    have := (h0 i).eq_zero
    rw [Polynomial.coeff_sub] at this
    exact sub_eq_zero.1 this
  have h2 := Matrix.eval_charpoly (-N) 1
  rw [h1] at h2
  simp only [Polynomial.eval_pow, Polynomial.eval_X, one_pow, map_one, sub_neg_eq_add] at h2
  exact h2.symm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem gen_sub_one_pow_three {σ : E →ₐ[F] E} {d j : ℕ} (W : Spc F E d) (Y : Matrix (Fin d) (Fin j) E)
    (u : UA σ W.J) (h1 : mat u * incM F Y = incM F Y)
    (h2 : ∀ z, (∀ k, formA σ W.J z (incV F fun i => Y i k) = 0) → ∃ a, mat u *ᵥ z = z + incM F Y *ᵥ a)
    (h3 : ∀ z k, formA σ W.J (mat u *ᵥ z - z) (incV F fun i => Y i k) = 0) :
    (mat u - 1) ^ 3 = 0 := by
  have hz : ∀ z : Fin d → AE F E, ((mat u - 1) ^ 3) *ᵥ z = 0 := by
    intro z
    have hN : ∀ w : Fin d → AE F E, (mat u - 1) *ᵥ w = mat u *ᵥ w - w := fun w => by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    obtain ⟨a, ha⟩ := h2 ((mat u - 1) *ᵥ z) (fun k => by rw [hN]; exact h3 z k)
    have e2 : (mat u - 1) *ᵥ ((mat u - 1) *ᵥ z) = incM F Y *ᵥ a := by
      rw [hN ((mat u - 1) *ᵥ z), ha]; abel
    have e3 : (mat u - 1) * incM F Y = 0 := by rw [Matrix.sub_mul, h1, Matrix.one_mul, sub_self]
    rw [pow_succ, pow_two, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e2, Matrix.mulVec_mulVec, e3,
      Matrix.zero_mulVec]
  ext a b
  have := congrFun (hz (Pi.single b 1)) a
  simpa [Matrix.mulVec_single_one] using this

theorem det_eq_one_of_mem_unipSp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d : ℕ) (W : Spc F E d) (j : ℕ) (Y : Matrix (Fin d) (Fin j) E),
    ∀ n ∈ GlobalTheory.ThKLiftCusp.unipSp σ W Y, Matrix.GeneralLinearGroup.det n.1 = 1 := by
  intro F E _ _ _ _ _ σ d W j Y
  have hle : unipSp σ W Y ≤ (Matrix.GeneralLinearGroup.det.comp (Subgroup.subtype _)).ker := by
    unfold unipSp
    rw [Subgroup.closure_le]
    rintro u ⟨h1, h2, h3⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Units.ext
    have hred : IsReduced (AE F E) := GlobalTheory.ReducedAlg.isReduced_tensor (k := F) (AF F) E
    have key := det_one_add_of_pow_eq_zero (mat u - 1) 3 (gen_sub_one_pow_three W Y u h1 h2 h3)
    rw [add_sub_cancel] at key
    exact key
  intro n hn
  exact hle hn

end GlobalTheory.ThKLiftCusp
